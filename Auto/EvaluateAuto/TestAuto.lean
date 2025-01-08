import Lean
import Auto.EvaluateAuto.OS
import Auto.EvaluateAuto.Result
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.NameArr
import Auto.Tactic

open Lean Auto

namespace EvalAuto

inductive SolverConfig where
  -- Use `duper` as the backend prover
  | native
  -- Use `duper` as the backend prover, without any preprocessing
  | rawNative
  -- Use `lean-smt`, currently not supported
  | leanSmt
  | smt (solverName : Solver.SMT.SolverName)
  | tptp (solverName : Solver.TPTP.SolverName) (path : String)
  deriving Repr

instance : ToString SolverConfig where
  toString : SolverConfig → String
  | .native       => "native"
  | .rawNative    => "rawNative"
  | .leanSmt      => "leanSmt"
  | .smt sn       => s!"smt {sn}"
  | .tptp sn path => s!"tptp {sn} {path}"

structure EvalAutoConfig where
  /-- Timeout for Lean code (Lean-auto + native provers) -/
  maxHeartbeats : Nat           := 65536
  /-- Timeout for external provers, i.e. TPTP solvers and SMT solvers -/
  timeout       : Nat           := 10
  /-- Solver configuration -/
  solverConfig  : SolverConfig
  /-- Optional file for saving the log of the evaluation -/
  logFile       : Option String := .none
  /-- Optional file for saving the result of the evaluation -/
  resultFile    : Option String := .none

instance : ToString EvalAutoConfig where
  toString : EvalAutoConfig → String
  | ⟨maxHeartbeats, timeout, solverConfig, logFile, resultFile⟩ =>
    let logFileStr :=
      match logFile with
      | .some logFile => s!", logFile := {logFile}"
      | .none => ""
    let resultFileStr :=
      match resultFile with
      | .some resultFile => s!", logFile := {resultFile}"
      | .none => ""
    s!"\{maxHeartbeats := {maxHeartbeats}, timeout := {timeout}, " ++
    s!"solverConfig := {solverConfig}{logFileStr}{resultFileStr}}"

/--
  Run `prover` on `lem.type`, using premises collected from `lem.proof`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
private def runProverOnAutoLemma
  (lem : Auto.Lemma) (prover : Array Lemma → Array Lemma → MetaM Expr) : CoreM Result := do
  if !(← Meta.MetaM.run' <| Meta.isProp lem.type) then
    return .nonProp
  -- **TODO: Aux theorem like those ending in `.proof_1`**
  let usedThmNames ← (← Expr.getUsedTheorems lem.proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThms ← usedThmNames.mapM (fun n => Lemma.ofConst n (.leaf "collected by hammertest"))
  let proverFn : MetaM Expr := Meta.forallTelescope lem.type fun bs body => do
    let negGoal := Expr.app (.const ``Not []) body
    let negGoalImpFalse ← Meta.withLocalDeclD `negGoal negGoal fun negGoalFVar => do
      let inhLemmas ← Auto.Inhabitation.getInhFactsFromLCtx
      let lctxLemmas ← Auto.collectLctxLemmas true #[]
      let allLemmas ← (lctxLemmas ++ usedThms).mapM (Auto.unfoldConstAndPreprocessLemma #[])
      let proofOfFalse ← prover allLemmas inhLemmas
      Meta.mkLambdaFVars #[negGoalFVar] proofOfFalse
    let goal := mkApp2 (.const ``Classical.byContradiction []) body negGoalImpFalse
    Meta.mkLambdaFVars bs goal
  -- Align with tactic elaboration (see `Lean.Elab.Term.TermElabM.run`)
  let metaContext : Meta.Context := { config := Elab.Term.setElabConfig {} }
  let result : Expr ⊕ Exception ←
    Lean.Core.tryCatchRuntimeEx
      (do let proof ← Meta.MetaM.run' proverFn (ctx := metaContext); return .inl proof)
      (fun e => return .inr e)
  match result with
  | .inl proof =>
    match Kernel.check (← getEnv) {} proof with
    | Except.ok proofType =>
      match Kernel.isDefEq (← getEnv) {} proofType lem.type with
      | Except.ok true => return .success
      | _ => return .typeUnequal
    | Except.error _ => return .typeCheckFail
  | .inr e => return .exception e

/--
  Run `prover` on the type of ``name``, using premises collected
    from the proof of `name`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
def runProverOnConst
  (name : Name) (prover : Array Lemma → Array Lemma → MetaM Expr) : CoreM Result := do
  let ci ← Name.getCi name decl_name%
  let .some v := ci.value?
    | throwError "{decl_name%} :: {name} has no value"
  let lemmaPre ← Auto.Lemma.ofConst name (.leaf "ofConst")
  let lemmaV := {lemmaPre with proof := v}
  runProverOnAutoLemma lemmaV prover

def disableAllSolvers (o : Options) : Options :=
  let o := auto.native.set o false
  let o := auto.smt.set o false
  let o := auto.tptp.set o false
  o

def runAutoOnConsts (config : EvalAutoConfig) (names : Array Name) : CoreM Unit := do
  let logFileHandle? : Option IO.FS.Handle ← config.logFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  let resultFileHandle? : Option IO.FS.Handle ← config.resultFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  trace[auto.eval.printConfig] m!"Config = {config}"
  if let .some fhandle := logFileHandle? then
    fhandle.putStrLn s!"Config = {config}"
  let startTime ← IO.monoMsNow
  let mut results := #[]
  for name in names do
    let ci ← Name.getCi name decl_name%
    trace[auto.eval.printProblem] m!"Testing || {name} : {ci.type}"
    if let .some fhandle := logFileHandle? then
      fhandle.putStrLn ""
      fhandle.putStrLn s!"Testing || {name} : {← (Lean.Meta.ppExpr ci.type).run'}"
      fhandle.flush
    let result : Result ← withCurrHeartbeats <|
      withReader (fun ctx => {ctx with maxHeartbeats := config.maxHeartbeats * 1000}) <|
        match config.solverConfig with
        | .native       =>
          withOptions (fun o =>
            let o := disableAllSolvers o
            let o := auto.native.set o true
            let o := auto.mono.mode.set o MonoMode.hol
            o) <| runProverOnConst name (Auto.runAuto (.some name))
        | .rawNative    =>
          runProverOnConst name Solver.Native.queryNative
        | .leanSmt      =>
          throwError "Lean-SMT is currently not supported"
        | .smt sn       =>
          withOptions (fun o =>
            let o := disableAllSolvers o
            let o := auto.smt.set o true
            let o := auto.smt.solver.name.set o sn
            let o := auto.smt.timeout.set o config.timeout
            let o := auto.smt.trust.set o true
            let o := auto.mono.mode.set o MonoMode.fol
            o) <| runProverOnConst name (Auto.runAuto (.some name))
        | .tptp sn path =>
          withOptions (fun o =>
            let o := disableAllSolvers o
            let o := auto.tptp.set o true
            let o := auto.tptp.solver.name.set o sn
            let o := auto.tptp.timeout.set o config.timeout
            let o := auto.tptp.trust.set o true
            let o := auto.mono.mode.set o MonoMode.fol
            match sn with
            | .zipperposition => auto.tptp.zipperposition.path.set o path
            | .zeport _       => auto.tptp.zeport.path.set o path
            | .eproverHo      => auto.tptp.eproverHo.path.set o path
            | .vampire        => auto.tptp.vampire.path.set o path) <|
              runProverOnConst name (Auto.runAuto (.some name))
    trace[auto.eval.printResult] m!"{result}"
    results := results.push result
    if let .some fhandle := logFileHandle? then
      fhandle.putStrLn (toString (← MessageData.format m!"{result}"))
  if let .some fhandle := resultFileHandle? then
    fhandle.putStrLn s!"Elapsed time: {(← IO.monoMsNow) - startTime} ms"
    fhandle.putStrLn s!"\nSummary:\n"
    for ((name, result), idx) in (names.zip results).zipWithIndex do
      fhandle.putStrLn s!"{idx} {result.concise} {Name.uniqRepr name}"

def runAutoOnNamesFile (cfg : EvalAutoConfig) (fname : String) : CoreM Unit := do
  let names ← NameArray.load fname
  runAutoOnConsts cfg names

structure EvalAutoOnMathlibConfig where
  /-- Timeout for Lean code (Lean-auto + native provers) -/
  maxHeartbeats : Nat           := 65536
  /-- Timeout for external provers, i.e. TPTP solvers and SMT solvers -/
  timeout       : Nat           := 10
  /-- Solver configuration -/
  solverConfig  : SolverConfig
  /-- Folder for saving the result of the evaluation -/
  resultFolder  : String
  /-- Number of threads to use -/
  nthreads      : Nat
  /-- Batch size -/
  batchSize     : Nat

def Array.groupBySize (xs : Array α) (size : Nat) : Option (Array (Array α)) :=
  if size == 0 then
    .none
  else
    let n := (xs.size + size - 1) / size
    let ret := Array.mk <| (List.range n).map (fun i => Array.mk <| (xs.toList.drop (size * i)).take size)
    some ret

/--
  This should be run after `import Mathlib, import Auto.EvaluateAuto.TestTactics`,
  and should be run with a `cwd` where `lake env` creates an environment in which
  `Mathlib, lean-auto` and `duper` are available
-/
def evalAutoAtMathlibHumanTheorems (config : EvalAutoOnMathlibConfig) : CoreM Unit := do
  if !(← System.FilePath.isDir config.resultFolder) then
    IO.FS.createDir config.resultFolder
  let evaluateFilesHandle ← IO.FS.Handle.mk (config.resultFolder ++ "/evaluateFiles.txt") .write
  let all ← allHumanTheoremsFromPackage "Mathlib"
  let .some batches := Array.groupBySize all config.batchSize
    | throwError "Batch size must be nonzero"
  let mut running := #[]
  for (batch, idx) in batches.zipWithIndex do
    evaluateFilesHandle.putStrLn (toString idx)
    evaluateFilesHandle.flush
    let evalProc ← EvalProc.create "lake" #["env", "lean", "--stdin"]
    let logPath := config.resultFolder ++ "/" ++ toString idx
    evalProc.stdin.putStr (evalFile batch logPath)
    let (_, evalProc) ← evalProc.takeStdin
    running := running.push (idx, evalProc)
    while running.size >= config.nthreads do
      running ← tryWaitOn evaluateFilesHandle running
  while running.size != 0 do
    running ← tryWaitOn evaluateFilesHandle running
where
  tryWaitOn (evaluateFilesHandle : IO.FS.Handle) (running : Array (Nat × _)) : CoreM (Array (Nat × _)) := do
    let mut running' := #[]
    for (idx, proc) in running do
      let retCode? ← proc.tryWait
      match retCode? with
      | .some retCode =>
        evaluateFilesHandle.putStrLn s!"{idx} : {retCode}"
        evaluateFilesHandle.flush
      | .none => running' := running'.push (idx, proc)
    return running'
  evalFile
    (thms : Array Name) (logPath : String) : String :=
    let lb := "{"
    let rb := "}"
    let thmsStrs : List String :=
      match thms.toList.getLast? with
      | .some last =>
        thms.toList.dropLast.map (fun n => s!"  {repr n},") ++ [s!"  {repr last}"]
      | .none => []
    let lines := [
        s!"import Mathlib",
        "import Auto.EvaluateAuto.TestAuto",
        "import Auto.Tactic",
        "import Duper.Tactic",
        "open Lean Auto EvalAuto",
        "",
        "def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do",
        "  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM",
        "    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))",
        "  Duper.runDuper lemmas.toList 0",
        "",
        "attribute [rebind Auto.Native.solverFunc] Auto.duperRaw",
        "",
        "def thms : Array Name := #["
      ] ++ thmsStrs ++ [
        "]",
        "",
        "def action : CoreM Unit := do",
        "  let p ← initSrcSearchPath",
        s!"  let _ ← runAutoOnConsts",
        s!"    {lb} maxHeartbeats := {config.maxHeartbeats}, timeout := {config.timeout},",
        s!"      solverConfig := {repr config.solverConfig},",
        s!"      logFile := Option.some ({repr (logPath ++ ".log")}), resultFile := Option.some ({repr (logPath ++ ".result")}){rb}",
        "    thms",
        "",
        "#eval action"
      ]
    String.intercalate "\n" lines

end EvalAuto
