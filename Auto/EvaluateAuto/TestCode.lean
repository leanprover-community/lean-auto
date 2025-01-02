import Lean
import Auto.EvaluateAuto.Result
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.NameArr
import Auto.EvaluateAuto.CommandAnalysis
import Auto.Tactic

open Lean Auto

initialize
  registerTraceClass `auto.eval.printConfig
  registerTraceClass `auto.eval.printProblem
  registerTraceClass `auto.eval.printResult

namespace EvalAuto

inductive SolverConfig where
  | native
  | leanSmt
  | smt (solverName : Solver.SMT.SolverName)
  | tptp (solverName : Solver.TPTP.SolverName) (path : String)

instance : ToString SolverConfig where
  toString : SolverConfig → String
  | .native       => "native"
  | .leanSmt      => "leanSmt"
  | .smt sn       => s!"smt {sn}"
  | .tptp sn path => s!"tptp {sn} {path}"

structure EvalConfig where
  /-- Timeout for Lean code (Lean-auto + native provers) -/
  maxHeartbeats : Nat           := 65536
  /-- Timeout for external provers, i.e. TPTP solvers and SMT solvers -/
  timeout       : Nat           := 10
  /-- Solver configuration -/
  solverConfig  : SolverConfig
  /-- Optional logfile for saving the result of the evaluation -/
  logFile       : Option String := .none

instance : ToString EvalConfig where
  toString : EvalConfig → String
  | ⟨maxHeartbeats, timeout, solverConfig, logFile⟩ =>
    let logFileStr :=
      match logFile with
      | .some logFile => s!", logFile := {logFile}"
      | .none => ""
    s!"\{maxHeartbeats := {maxHeartbeats}, timeout := {timeout}, " ++
    s!"solverConfig = {solverConfig}{logFileStr}}"

/--
  Run `Lean-auto` on `lem.type`, using premises collected from `lem.proof`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
private def runAutoOnAutoLemma (declName? : Option Name) (lem : Auto.Lemma) : CoreM Result := do
  if !(← Meta.MetaM.run' <| Meta.isProp lem.type) then
    return .nonProp
  -- **TODO: Aux theorem like those ending in `.proof_1`**
  let usedThmNames ← (← Expr.getUsedTheorems lem.proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThms ← usedThmNames.mapM (fun n => Lemma.ofConst n (.leaf "collected by hammertest"))
  let autoProofFn : MetaM Expr := Meta.forallTelescope lem.type fun bs body => do
    let negGoal := Expr.app (.const ``Not []) body
    let negGoalImpFalse ← Meta.withLocalDeclD `negGoal negGoal fun negGoalFVar => do
      let inhLemmas ← Auto.Inhabitation.getInhFactsFromLCtx
      let lctxLemmas ← Auto.collectLctxLemmas true #[]
      let allLemmas ← (lctxLemmas ++ usedThms).mapM (Auto.unfoldConstAndPreprocessLemma #[])
      let proofOfFalse ← Auto.runAuto declName? allLemmas inhLemmas
      Meta.mkLambdaFVars #[negGoalFVar] proofOfFalse
    let goal := mkApp2 (.const ``Classical.byContradiction []) body negGoalImpFalse
    Meta.mkLambdaFVars bs goal
  -- Align with tactic elaboration (see `Lean.Elab.Term.TermElabM.run`)
  let metaContext : Meta.Context := { config := Elab.Term.setElabConfig {} }
  let result : Expr ⊕ Exception ←
    Lean.Core.tryCatchRuntimeEx
      (do let autoProof ← Meta.MetaM.run' autoProofFn (ctx := metaContext); return .inl autoProof)
      (fun e => return .inr e)
  match result with
  | .inl autoProof =>
    match Kernel.check (← getEnv) {} autoProof with
    | Except.ok autoProofType =>
      match Kernel.isDefEq (← getEnv) {} autoProofType lem.type with
      | Except.ok true => return .success
      | _ => return .typeUnequal
    | Except.error _ => return .typeCheckFail
  | .inr e => return .exception e

/--
  Run `Lean-auto` on the type of ``name``, using premises collected
    from the proof of `name`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
def runAutoOnConst (name : Name) : CoreM Result := do
  let ci ← Name.getCi name decl_name%
  let .some v := ci.value?
    | throwError "{decl_name%} :: {name} has no value"
  let lemmaPre ← Auto.Lemma.ofConst name (.leaf "ofConst")
  let lemmaV := {lemmaPre with proof := v}
  runAutoOnAutoLemma (.some name) lemmaV

def disableAllSolvers (o : Options) : Options :=
  let o := auto.native.set o false
  let o := auto.smt.set o false
  let o := auto.tptp.set o false
  o

def runAutoOnConsts (config : EvalConfig) (names : Array Name) : CoreM Unit := do
  let logFileHandle : Option IO.FS.Handle ← config.logFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  trace[auto.eval.printConfig] m!"Config = {config}"
  if let .some fhandle := logFileHandle then
    fhandle.putStrLn s!"Config = {config}"
  let startTime ← IO.monoMsNow
  let mut results := #[]
  for name in names do
    let ci ← Name.getCi name decl_name%
    trace[auto.eval.printProblem] m!"Testing || {name} : {ci.type}"
    if let .some fhandle := logFileHandle then
      fhandle.putStrLn ""
      fhandle.putStrLn s!"Testing || {name} : {← (Lean.Meta.ppExpr ci.type).run'}"
    let result : Result ← withCurrHeartbeats <|
      withReader (fun ctx => {ctx with maxHeartbeats := config.maxHeartbeats * 1000}) <|
        match config.solverConfig with
        | .native    =>
          withOptions (fun o =>
            let o := disableAllSolvers o
            let o := auto.native.set o true
            let o := auto.mono.mode.set o MonoMode.hol
            o) <| runAutoOnConst name
        | .leanSmt  =>
          throwError "Lean-SMT is currently not supported"
        | .smt sn   =>
          withOptions (fun o =>
            let o := disableAllSolvers o
            let o := auto.smt.set o true
            let o := auto.smt.solver.name.set o sn
            let o := auto.smt.timeout.set o config.timeout
            let o := auto.smt.trust.set o true
            let o := auto.mono.mode.set o MonoMode.fol
            o) <| runAutoOnConst name
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
              runAutoOnConst name
    trace[auto.eval.printResult] m!"{result}"
    results := results.push result
    if let .some fhandle := logFileHandle then
      fhandle.putStrLn (toString (← MessageData.format m!"{result}"))
  if let .some fhandle := logFileHandle then
    fhandle.putStrLn ""
    fhandle.putStrLn s!"Elapsed time: {(← IO.monoMsNow) - startTime} ms"
    fhandle.putStrLn s!"\nSummary:\n"
    for ((name, result), idx) in (names.zip results).zipWithIndex do
      fhandle.putStrLn s!"{idx} {result.concise} {name}"

def runAutoOnNamesFile (cfg : EvalConfig) (fname : String) : CoreM Unit := do
  let names ← NameArray.load fname
  runAutoOnConsts cfg names

open Elab Tactic
def useRfl : TacticM Unit := do evalTactic (← `(tactic| intros; rfl))

def useSimp : TacticM Unit := do evalTactic (← `(tactic| intros; simp))

def useSimpAll : TacticM Unit := do evalTactic (← `(tactic| intros; simp_all))

def useSimpAllWithPremises (ci : ConstantInfo) : TacticM Unit := do
  let .some proof := ci.value?
    | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
  let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThmTerms : Array Term := usedThmNames.map (fun name => ⟨mkIdent name⟩)
  evalTactic (← `(tactic| intros; simp_all [$[$usedThmTerms:term],*]))

private def mkAesopStx (addClauses : Array Syntax) : TSyntax `tactic :=
  let synth : SourceInfo := SourceInfo.synthetic default default false
  TSyntax.mk (
    Syntax.node synth `Aesop.Frontend.Parser.aesopTactic
      #[Syntax.atom synth "aesop", Syntax.node synth `null addClauses]
  )

-- Only guaranteed to work for `aesop @ Lean v4.14.0`
def useAesop : TacticM Unit := evalTactic (mkAesopStx #[])

-- Only guaranteed to work for `aesop @ Lean v4.14.0`
def useAesopWithPremises (ci : ConstantInfo) : TacticM Unit := do
  let .some proof := ci.value?
    | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
  let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThmIdents := usedThmNames.map Lean.mkIdent
  let addClauses := usedThmIdents.map mkAddIdentStx
  let aesopStx := mkAesopStx addClauses
  evalTactic aesopStx
where
  synth : SourceInfo := SourceInfo.synthetic default default false
  mkAddIdentStx (ident : Ident) : Syntax :=
    Syntax.node synth `Aesop.Frontend.Parser.«tactic_clause(Add_)»
      #[Syntax.atom synth "(", Syntax.atom synth "add",
        Syntax.node synth `null
          #[Syntax.node synth `Aesop.Frontend.Parser.rule_expr___
            #[Syntax.node synth `Aesop.Frontend.Parser.feature_
              #[Syntax.node synth `Aesop.Frontend.Parser.phaseUnsafe
                #[Syntax.atom synth "unsafe"]
              ],
              Syntax.node synth `Aesop.Frontend.Parser.rule_expr_
                #[Lean.Syntax.node synth `Aesop.Frontend.Parser.featIdent #[ident]]
            ]
          ],
          Syntax.atom synth ")"
      ]


end EvalAuto
