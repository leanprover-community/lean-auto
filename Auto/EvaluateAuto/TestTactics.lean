import Lean
import Auto.EvaluateAuto.OS
import Auto.EvaluateAuto.Result
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.NameArr
import Auto.EvaluateAuto.CommandAnalysis
import Auto.Tactic
import Auto.EvaluateAuto.AutoConfig
import Std
open Lean

namespace EvalAuto

open Elab Tactic

section Tactics

  /--
    Solves the goal using `sorry` if `ci` does not contain unknown constants,
    and throws and error if `ci` contains unknown constants

    When we evaluate tactics on a theorem `T`, we replay the file that defines `T`
    and calls the tactic on the environment `env` just before the declaration of `T`.
    Since there are commands that define multiple constants simultaneously, it is
    possible that the proof or type of `T` contains constants not present in `env`.
    We run `testUnknownConstant` to detect such situations.
  -/
  def testUnknownConstant (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let usedConsts := Expr.getUsedConstants proof ++ Expr.getUsedConstants ci.type
    for name in usedConsts do
      if ((← getEnv).find? name).isNone then
        throwError "{decl_name%} :: Proof of {ci.name} contains unknown constant {name}"
    evalTactic (← `(tactic| sorry))

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

  private def mkAesopConfigStx (subHeartbeats : Nat) : CoreM Syntax := do
    let synth : SourceInfo := SourceInfo.synthetic default default false
    let shStx := Syntax.node synth `num #[Syntax.atom synth (toString subHeartbeats)]
    let shStx := TSyntax.mk shStx
    let stx ← `(term | { maxSimpHeartbeats := $shStx, maxRuleHeartbeats := $shStx, maxUnfoldHeartbeats := $shStx })
    return Syntax.node synth `Aesop.Frontend.Parser.«tactic_clause(Config:=_)»
           #[Syntax.atom synth "(", Syntax.atom synth "config", Syntax.atom synth ":=", stx]

  private def mkAesopStx (tacticClauses : Array Syntax) : TSyntax `tactic :=
    let synth : SourceInfo := SourceInfo.synthetic default default false
    TSyntax.mk (
      Syntax.node synth `Aesop.Frontend.Parser.aesopTactic
        #[Syntax.atom synth "aesop", Syntax.node synth `null tacticClauses]
    )

  /--
    Tactic sequence: `intros; aesop`
    Only guaranteed to work for `aesop @ Lean v4.14.0`
  -/
  def useAesop (subHeartbeats : Nat) : TacticM Unit := do
    let configStx ← mkAesopConfigStx subHeartbeats
    let aesopStx := mkAesopStx #[configStx]
    let stx ← `(tactic|intros; $aesopStx)
    evalTactic stx

  /--
    Tactic sequence: `intros; aesop (add unsafe premise₁) ⋯ (add unsafe premiseₙ)`
    Only guaranteed to work for `aesop @ Lean v4.14.0`
  -/
  def useAesopWithPremises (subHeartbeats : Nat) (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let configClause ← mkAesopConfigStx subHeartbeats
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmIdents := usedThmNames.map Lean.mkIdent
    let addClauses := usedThmIdents.map mkAddIdentStx
    let aesopStx := mkAesopStx (#[configClause] ++ addClauses)
    let stx ← `(tactic| intros; $aesopStx)
    evalTactic stx
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
                  #[Syntax.node synth `Aesop.Frontend.Parser.featIdent #[ident]]
              ]
            ],
            Syntax.atom synth ")"
        ]

  def useDuper (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmIdents : Array Ident := usedThmNames.map (fun name => ⟨mkIdent name⟩)
    let stx := mkDuperStx usedThmIdents
    evalTactic stx
  where
    mkDuperStx (idents : Array Ident) : Syntax :=
      let synth : SourceInfo := SourceInfo.synthetic default default false
      let idArr : Array Syntax := ((idents.map (fun id => #[Syntax.atom synth ",", id])).flatMap id)[1:]
      Syntax.node synth `Duper.duper
        #[Syntax.atom synth "duper",
          Syntax.node synth `null
            #[Syntax.atom synth "[", Syntax.node synth `null idArr, Syntax.atom synth "]"],
          Syntax.node synth `null
            #[Syntax.atom synth "{",
              Syntax.node synth `null
                #[Syntax.node synth `Duper.«configOptionPortfolioInstance:=_»
                    #[Syntax.atom synth "portfolioInstance",
                      Syntax.atom synth ":=",
                      Syntax.node synth `num #[Syntax.atom synth "0"]],
                  Syntax.atom synth ",",
                  Syntax.node synth `Duper.«configOptionPreprocessing:=_»
                    #[Syntax.atom synth "preprocessing",
                      Syntax.atom synth ":=",
                      Syntax.node synth `Duper.preprocessing_optionNo_preprocessing
                        #[Lean.Syntax.atom synth "no_preprocessing"]]],
              Lean.Syntax.atom synth "}"]
        ]

  def useAuto
    (ignoreNonQuasiHigherOrder : Bool)
    (config : SolverConfig)
    (timeout : Nat) -- Timeout for external provers
    (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmTerms : Array Term := usedThmNames.map (fun name => ⟨mkIdent name⟩)
    let usedThmHints : Array (TSyntax `Auto.hintelem) ← usedThmTerms.mapM (fun t =>
      `(Auto.hintelem| $t:term))
    let stx ← `(tactic| auto [$[$usedThmHints],*])
    withOptions (fun o => auto.mono.ignoreNonQuasiHigherOrder.set o ignoreNonQuasiHigherOrder) <|
      withAutoSolverConfigOptions config timeout <| evalTactic stx

  inductive RegisteredTactic where
    | testUnknownConstant
    | useRfl
    | useSimp
    | useSimpAll
    | useSimpAllWithPremises
    | useAesop (subHeartbeats : Nat)
    | useAesopWithPremises (subHeartbeats : Nat)
    | useDuper
    | useAuto (ignoreNonQuasiHigherOrder : Bool) (config : SolverConfig) (timeout : Nat)
  deriving BEq, Hashable, Repr

  instance : ToString RegisteredTactic where
    toString : RegisteredTactic → String
    | .testUnknownConstant     => "testUnknownConstant"
    | .useRfl                  => "useRfl"
    | .useSimp                 => "useSimp"
    | .useSimpAll              => "useSimpAll"
    | .useSimpAllWithPremises  => "useSimpAllWithPremises"
    | .useAesop sh             => s!"useAesop {sh}"
    | .useAesopWithPremises sh => s!"useAesopWithPremises {sh}"
    | .useDuper                => s!"useDuper"
    | .useAuto ig config timeout => s!"useAuto {ig} {config} {timeout}"

  def RegisteredTactic.toCiTactic : RegisteredTactic → ConstantInfo → TacticM Unit
    | .testUnknownConstant     => EvalAuto.testUnknownConstant
    | .useRfl                  => fun _ => EvalAuto.useRfl
    | .useSimp                 => fun _ => EvalAuto.useSimp
    | .useSimpAll              => fun _ => EvalAuto.useSimpAll
    | .useSimpAllWithPremises  => EvalAuto.useSimpAllWithPremises
    | .useAesop sh             => fun _ => EvalAuto.useAesop sh
    | .useAesopWithPremises sh => EvalAuto.useAesopWithPremises sh
    | .useDuper                => EvalAuto.useDuper
    | .useAuto ig config timeout => EvalAuto.useAuto ig config timeout

end Tactics

/--
  Use `runWithEffectOfCommands` to run tactics at the place just before
  the command that created the constant `name`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files
-/
/- **TODO: Fix Evaluation Issue** -/
def runTacticsAtConstantDeclaration
  (name : Name) (searchPath : SearchPath)
  (tactics : Array (ConstantInfo → TacticM Unit)) : CoreM (Array Result) := do
  if ← isInitializerExecutionEnabled then
    throwError "{decl_name%} :: Running this function with execution of `initialize` code enabled is unsafe"
  let .some modName ← Lean.findModuleOf? name
    | throwError "{decl_name%} :: Cannot find constant {name}"
  let .some uri ← Server.documentUriFromModule? modName
    | throwError "{decl_name%} :: Cannot find module {modName}"
  let .some path := System.Uri.fileUriToPath? uri
    | throwError "{decl_name%} :: URI {uri} of {modName} is not a file"
  let path := path.normalize
  let inputHandle ← IO.FS.Handle.mk path .read
  let input ← inputHandle.readToEnd
  let results : Array (Array Result) ← runWithEffectOfCommands input path.toString (.some 1) (fun ctx st₁ st₂ ci => do
    if name != ci.name then
      return .none
    let metaAction (tactic : ConstantInfo → TacticM Unit) : MetaM Result :=
      Term.TermElabM.run' <| Result.ofTacticOnExpr ci.type (tactic ci)
    let coreAction tactic : CoreM Result := (metaAction tactic).run'
    let ioAction tactic : IO (Result × _) :=
      (coreAction tactic).toIO {fileName := path.toString, fileMap := FileMap.ofString input } { env := st₁.commandState.env }
    let resultsWithState ← tactics.mapM (fun tactic => ioAction tactic)
    return .some (resultsWithState.map Prod.fst))
  let #[result] := results
    | throwError "{decl_name%} :: Unexpected error"
  return result

structure EvalTacticConfig where
  /-- Timeout for each tactic -/
  maxHeartbeats : Nat           := 65536
  /-- Tactics to run at each constant declaration -/
  tactics       : Array RegisteredTactic
  /-- Optional file for saving the log of the evaluation -/
  logFile       : Option String := .none
  /-- Optional file for saving the result of the evaluation -/
  resultFile    : Option String := .none
  /--
    On some problems, certain tactics may go into infinite loops not
    guarded by `Core.checkMaxHeartbeats`. These instances should be
    recorded here and avoided (throw error immediately) during evaluation.
  -/
  nonterminates : Array (RegisteredTactic × Name)

instance : ToString EvalTacticConfig where
  toString : EvalTacticConfig → String
  | ⟨maxHeartbeats, tactics, logFile, resultFile, nonterminates⟩ =>
    let logFileStr :=
      match logFile with
      | .some logFile => s!", logFile := {logFile}"
      | .none => ""
    let resultFileStr :=
      match resultFile with
      | .some resultFile => s!", resultFile := {resultFile}"
      | .none => ""
    let nontermStr := String.intercalate ",\n" (nonterminates.map (fun (rt, n) => s!"    ({rt}, {n})")).toList
    let nontermStr := if nonterminates.size != 0 then nontermStr ++ "\n" else nontermStr
    s!"\{\n  maxHeartbeats := {maxHeartbeats}, tactics := {tactics}{logFileStr}{resultFileStr}" ++
    s!"\n  nonterminates := #[\n{nontermStr}  ]\n}"

/- **TODO: Fix Evaluation Issue** -/
/--
  Effectively `runTacticsAtConstantDeclaration` at each constant in `modName` which satisfies `filter`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files

  For the `i`-th theorem `name` in `names`, its entry in the result file has the following form:
  `<i> #[<result> <time> <heartbeats>, ⋯, <result> <time> <heartbeats>] <name>`
-/
def evalTacticsAtModule
  (modName : Name) (searchPath : SearchPath) (filter : ConstantInfo → Bool)
  (config : EvalTacticConfig) : CoreM Unit:= do
  let logFileHandle? : Option IO.FS.Handle ← config.logFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  let resultFileHandle? : Option IO.FS.Handle ← config.resultFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  trace[auto.eval.printConfig] m!"Config = {config}"
  if let .some fhandle := logFileHandle? then
    fhandle.putStrLn s!"Config = {config}"
    fhandle.putStrLn s!"Start time : {← Std.Time.Timestamp.now}"
  let .some uri ← Server.documentUriFromModule? modName
    | throwError "{decl_name%} :: Cannot find module {modName}"
  let .some path := System.Uri.fileUriToPath? uri
    | throwError "{decl_name%} :: URI {uri} of {modName} is not a file"
  let path := path.normalize
  let inputHandle ← IO.FS.Handle.mk path .read
  let input ← inputHandle.readToEnd
  let startTime ← IO.monoMsNow
  let nonterms := Std.HashSet.ofArray config.nonterminates
  let results ← runWithEffectOfCommands input path.toString .none (fun ctx st₁ st₂ ci => do
    if filter ci then
      let result ← evalAction
        {fileName := path.toString, fileMap := FileMap.ofString input } { env := st₁.commandState.env }
        ci logFileHandle? config nonterms
      return .some (ci.name, result)
    else
      return .none)
  if let .some fhandle := resultFileHandle? then
    fhandle.putStrLn s!"Total elapsed time : {(← IO.monoMsNow) - startTime} ms"
    fhandle.putStrLn s!"\nSummary:\n"
    for ((name, result), idx) in results.zipIdx do
      let resultStrs := result.map (fun (r, time, hb) => s!"{r.concise} {time} {hb}")
      fhandle.putStrLn s!"{idx} {resultStrs} {Name.uniqRepr name}"
where
  evalAction
    (context : Core.Context) (state : Core.State) (ci : ConstantInfo)
    (logFileHandle? : Option IO.FS.Handle) (config : EvalTacticConfig)
    (nonterms : Std.HashSet (RegisteredTactic × Name)) : IO (Array (Result × Nat × Nat)) := do
  config.tactics.zipIdx.mapM (fun (tactic, idx) => do
    let metaAction : MetaM Result :=
      Term.TermElabM.run' <| Result.ofTacticOnExpr ci.type (tactic.toCiTactic ci)
    let coreAction : CoreM (Result × Nat × Nat) := (do
      trace[auto.eval.printProblem] m!"Testing tactic {idx} || {ci.name} : {ci.type}"
      if let .some fhandle := logFileHandle? then
        fhandle.putStrLn ""
        fhandle.putStrLn s!"Timestamp : {← Std.Time.Timestamp.now}"
        fhandle.putStrLn s!"Testing tactic {idx} || {ci.name} : {← (Lean.Meta.ppExpr ci.type).run'}"
        fhandle.flush
      let problemStartTime ← IO.monoMsNow
      let problemStartHb ← IO.getNumHeartbeats
      let result ← (do
        if nonterms.contains (tactic, ci.name) then
          return Result.nonterminate
        else
          withCurrHeartbeats <|
            withReader (fun ctx => { ctx with maxHeartbeats := config.maxHeartbeats * 1000 }) <|
              Meta.MetaM.run' metaAction)
      let problemTime := (← IO.monoMsNow) - problemStartTime
      let problemHb := (← IO.getNumHeartbeats) - problemStartHb
      trace[auto.eval.printResult] m!"{result}\nElapsed time : {problemTime} ms, {problemHb} hb"
      if let .some fhandle := logFileHandle? then
        fhandle.putStrLn (toString (← MessageData.format m!"{result}\nElapsed time : {problemTime} ms, {problemHb} hb"))
      return (result, problemTime, problemHb))
    let (result, _) ← coreAction.toIO context state
    return result)

def readEvalTacticsAtModuleResult (resultFile : String) : CoreM (Array (Name × Array (Result × Nat × Nat))) := do
  let content ← IO.FS.readFile resultFile
  let lines := content.splitOn "\n"
  if lines[2]? != .some "Summary:" || lines[3]? != .some "" then
    throwError "{decl_name%} :: Format of result file changed, please change analysis code. Result file : {resultFile}"
  let lines := (lines.drop 4).filter (fun s => s != "")
  (Array.mk lines).mapM (analyzeLine resultFile)
where
  analyzeLine (fileName line : String) : CoreM (Name × Array (Result × Nat × Nat)) := do
    let line := (line.dropWhile (fun c => c != ' ')).drop 3
    let tr := (line.takeWhile (fun c => c != ']')).splitOn ", "
    let tr : Array (Result × Nat × Nat) ← (Array.mk tr).mapM (fun s => do
      let [sr, st, sh] := s.splitOn " "
        | throwError "s!{decl_name%} :: In file {fileName}, {s} is not of the form `<result> <time> <heartbeats>`"
      match Result.ofConcise? sr, String.toNat? st, String.toNat? sh with
      | .some r, .some t, .some h => return (r, t, h)
      | _, _, _ => throwError s!"{decl_name%} :: In file {fileName}, {s} is not of the form `<result> <time> <heartbeats>`")
    let line := (line.dropWhile (fun c => c != ']')).drop 2
    let name := Name.parseUniqRepr line
    return (name, tr)

structure EvalTacticOnMathlibConfig where
  /-- Timeout for each tactic -/
  maxHeartbeats : Nat           := 65536
  /-- Tactics to run at each constant declaration -/
  tactics       : Array RegisteredTactic
  /-- Folder for saving the result of the evaluation -/
  resultFolder  : String
  /-- Number of processes to use -/
  nprocs        : Nat
  /-- Memory limit for each evaluation process, in kb -/
  memoryLimitKb : Option Nat    := .none
  /-- Total time limit for each evaluation process, in seconds -/
  timeLimitS    : Option Nat    := .none
  /-- Specify modules to run tactics on -/
  moduleFilter  : Name → Bool   := fun _ => true
  /--
    On some problems, certain tactics may go into infinite loops not
    guarded by `Core.checkMaxHeartbeats`. These instances should be
    recorded here and avoided (throw error immediately) during evaluation.
  -/
  nonterminates : Array (RegisteredTactic × Name)

/--
  This should be run after `import Mathlib` and `import Auto.EvaluateAuto.TestTactics`,
  and should be run with a `cwd` where `lake env` creates an environment in which
  `Mathlib` and `lean-auto` are available
-/
def evalTacticsAtMathlibHumanTheorems (config : EvalTacticOnMathlibConfig) : CoreM Unit := do
  let mms := (← mathlibModules).filter config.moduleFilter
  if !(mms.all Name.canBeFilename) then
    throwError "{decl_name%} :: Some modules have extra-ordinary names. Evaluation code needs to be changed!"
  if !(← System.FilePath.isDir config.resultFolder) then
    IO.FS.createDir config.resultFolder
  let evaluateFilesHandle ← IO.FS.Handle.mk (config.resultFolder ++ "/evaluateFiles.txt") .write
  let allTally ← tallyNamesByModule (← allHumanTheorems)
  let mut running := #[]
  for mm in mms do
    evaluateFilesHandle.putStrLn mm.toString
    evaluateFilesHandle.flush
    let nComps := mm.components.length
    let paths := (List.range nComps).map (fun i =>
      String.join <| (mm.components.take (i + 1)).map (fun n => "/" ++ n.toString))
    for extraDirPath in paths.dropLast do
      let dirPath := config.resultFolder ++ extraDirPath
      if !(← System.FilePath.isDir dirPath) then
        IO.FS.createDir dirPath
    let .some extraLogPath := paths.getLast?
      | throwError "evalAtMathlibHumanTheorems :: Module name {mm} has zero components"
    let logPath := config.resultFolder ++ extraLogPath
    let validThms := (allTally.get? mm).getD #[]
    NameArray.save validThms (logPath ++ ".name")
    let ef ← evalFile mm validThms logPath config
    let evalProc ← EvalProc.create "bash" #[]
    if let .some mlimit := config.memoryLimitKb then
      evalProc.stdin.putStrLn s!"ulimit -v {mlimit}"
    if let .some tlimit := config.timeLimitS then
      evalProc.stdin.putStrLn ("echo " ++ bashRepr ef ++ s!" | timeout {tlimit} lake env lean --stdin")
    else
      evalProc.stdin.putStrLn ("echo " ++ bashRepr ef ++ s!" | lake env lean --stdin")
    let (_, evalProc) ← evalProc.takeStdin
    running := running.push (mm, evalProc)
    while running.size >= config.nprocs do
      running ← tryWaitOn evaluateFilesHandle running
  while running.size != 0 do
    running ← tryWaitOn evaluateFilesHandle running
where
  tryWaitOn (evaluateFilesHandle : IO.FS.Handle) (running : Array (Name × EvalTakenProc)) : CoreM (Array (Name × _)) := do
    let mut running' := #[]
    for (mm, proc) in running do
      let retCode? ← proc.tryWait
      match retCode? with
      | .some retCode =>
        evaluateFilesHandle.putStrLn s!"{mm} : {retCode}"
        evaluateFilesHandle.flush
      | .none => running' := running'.push (mm, proc)
    return running'
  evalFile
    (mm : Name) (validThms : Array Name)
    (logPath : String) (config : EvalTacticOnMathlibConfig) : CoreM String := do
    let lb := "{"
    let rb := "}"
    let thmsStrs : List String :=
      match validThms.toList.getLast? with
      | .some last =>
        validThms.toList.dropLast.map (fun n => s!"  {repr n},") ++ [s!"  {repr last}"]
      | .none => []
    let nonterms := config.nonterminates
    let nontermsStrs : List String :=
      match nonterms.toList.getLast? with
      | .some last =>
        nonterms.toList.dropLast.map (fun n => s!"  {repr n},") ++ [s!"  {repr last}"]
      | .none => []
    let tacsStr := String.intercalate ", " (config.tactics.map (fun tac => s!"({repr tac})")).toList
    -- Passing options
    let allImportedModules := Std.HashSet.ofArray (← getEnv).allImportedModuleNames
    let ensureAesop := auto.testTactics.ensureAesop.get (← getOptions)
    if ensureAesop && !allImportedModules.contains `Aesop then
      throwError "{decl_name%} :: Cannot find module `Aesop`"
    let ensureAesopImports := if ensureAesop then #["import Aesop"] else #[]
    let ensureAuto := auto.testTactics.ensureAuto.get (← getOptions)
    let rnm := auto.testTactics.rebindNativeModuleName.get (← getOptions)
    let rnm : Name := (rnm.splitOn ".").foldl (fun cur field => Name.str cur field) .anonymous
    if ensureAuto && !allImportedModules.contains rnm then
      throwError "{decl_name%} :: Cannot find rebindNativeModuleName module `{toString rnm}`"
    let ensureAutoImports := if ensureAuto then #["import Duper.Tactic", s!"import {rnm}"] else #[]
    let lines := #[
        s!"import {mm}",
        "import Auto.EvaluateAuto.TestTactics"
      ] ++ ensureAesopImports ++ ensureAutoImports ++ #[
        "open Lean EvalAuto",
        "",
        "def humanThms : Std.HashSet Name := Std.HashSet.ofList ["
      ] ++ thmsStrs ++ #[
        "]",
        "",
        "def nonterms : Array (RegisteredTactic × Name) := #["
      ] ++ nontermsStrs ++ #[
        "]",
        "",
        "def action : CoreM Unit := do",
        "  let p ← initSrcSearchPath",
        s!"  let _ ← evalTacticsAtModule ({repr mm}) p (fun ci => humanThms.contains ci.name)",
        s!"    {lb} maxHeartbeats := {config.maxHeartbeats}, tactics := #[{tacsStr}],",
        s!"      logFile := {repr (logPath ++ ".log")}, resultFile := {repr (logPath ++ ".result")},",
        s!"      nonterminates := nonterms {rb}",
        "",
        -- Passing option `auto.testTactics.ensureAesop`
        s!"set_option auto.testTactics.ensureAesop {ensureAesop}",
        -- Passing option `auto.testTactics.ensureAuto`
        s!"set_option auto.testTactics.ensureAuto {ensureAuto}",
        -- Passing option `auto.testTactics.rebindNativeModuleName`
        s!"set_option auto.testTactics.rebindNativeModuleName \"{rnm}\"",
        "",
        "#eval action"
      ]
    return String.intercalate "\n" lines.toList

/--
  Read results generated by `evalTacticsAtMathlibHumanTheorems`
-/
def readETMHTResult (config : EvalTacticOnMathlibConfig) :
  CoreM (Array (Name × Array (Name × Array (Result × Nat × Nat)))) := do
  let resultFolder := config.resultFolder
  if !(← System.FilePath.isDir resultFolder) then
    throwError "{decl_name%} :: {config.resultFolder} is not a directory"
  let allPaths ← System.FilePath.walkDir resultFolder
  let mut ret := #[]
  for path in allPaths do
    if !(← System.FilePath.isDir path) && path.toString.takeRight 7 == ".result" then
      let content ← readEvalTacticsAtModuleResult path.toString
      let suffix := (path.toString.drop (resultFolder.length + 1)).dropRight 7
      let modName := (suffix.splitOn "/").foldl (fun a b => Name.str a b) .anonymous
      ret := ret.push (modName, content)
  return ret

/--
  Similar to `readETMHTResult`, but will not throw error if a `.result` file is empty.
  Instead, its return value contains all the paths to the `.result` files that are empty.
-/
def readETMHTResultAllowNonRet (config : EvalTacticOnMathlibConfig) :
  CoreM (Array String × Array (Name × Array (Name × Array (Result × Nat × Nat)))) := do
  let resultFolder := config.resultFolder
  if !(← System.FilePath.isDir resultFolder) then
    throwError "{decl_name%} :: {config.resultFolder} is not a directory"
  let allPaths ← System.FilePath.walkDir resultFolder
  let mut ret := #[]
  let mut nonRet := #[]
  for path in allPaths do
    if !(← System.FilePath.isDir path) && path.toString.takeRight 7 == ".result" then
      let raw ← IO.FS.readFile path
      if raw.length == 0 then
        nonRet := nonRet.push (path.toString.dropRight 7)
        continue
      let content ← readEvalTacticsAtModuleResult path.toString
      let suffix := (path.toString.drop (resultFolder.length + 1)).dropRight 7
      let modName := (suffix.splitOn "/").foldl (fun a b => Name.str a b) .anonymous
      ret := ret.push (modName, content)
  return (nonRet, ret)

/--
  Read results generated by `evalTacticsAtMathlibHumanTheorems` and
    store them in a single file `gatheredResult` in `config.resultFolder`
-/
def gatherETMHTResult (config : EvalTacticOnMathlibConfig) : CoreM Unit := do
  let resultFolder := config.resultFolder
  let saveFile ← IO.FS.Handle.mk (resultFolder ++ "/gatheredResult") .write
  if !(← System.FilePath.isDir resultFolder) then
    throwError "{decl_name%} :: {config.resultFolder} is not a directory"
  let readResult ← readETMHTResult config
  let readResult := (readResult.map Prod.snd).flatMap id
  saveFile.putStrLn "Total elapsed time: Not applicable. This is a gathered result of evalTacticsAtMathlibHumanTheorems"
  saveFile.putStrLn ""
  saveFile.putStrLn "Summary:"
  saveFile.putStrLn ""
  for ((name, result), idx) in readResult.zipIdx do
    let resultStrs := result.map (fun (r, time, hb) => s!"{r.concise} {time} {hb}")
    saveFile.putStrLn s!"{idx} {resultStrs} {Name.uniqRepr name}"

/--
  Similar to `gatherETMHTResult`, but will not throw error if a `.result` file is empty.
  Instead, its saves ⟨all the paths to the `.result` files that are empty⟩ in `nonRetPaths`.
-/
def gatherETMHTResultAllowNonRet (config : EvalTacticOnMathlibConfig) : CoreM Unit := do
  let resultFolder := config.resultFolder
  let saveFile ← IO.FS.Handle.mk (resultFolder ++ "/gatheredResult") .write
  let nonRetFile ← IO.FS.Handle.mk (resultFolder ++ "/nonRetPaths") .write
  if !(← System.FilePath.isDir resultFolder) then
    throwError "{decl_name%} :: {config.resultFolder} is not a directory"
  let (nonRet, readResult) ← readETMHTResultAllowNonRet config
  let readResult := (readResult.map Prod.snd).flatMap id
  saveFile.putStrLn "Total elapsed time: Not applicable. This is a gathered result of evalTacticsAtMathlibHumanTheorems"
  saveFile.putStrLn ""
  saveFile.putStrLn "Summary:"
  saveFile.putStrLn ""
  for ((name, result), idx) in readResult.zipIdx do
    let resultStrs := result.map (fun (r, time, hb) => s!"{r.concise} {time} {hb}")
    saveFile.putStrLn s!"{idx} {resultStrs} {Name.uniqRepr name}"
  for path in nonRet do
    nonRetFile.putStrLn path

/--
  Read `evaluateFiles.txt` generated by `evalTacticsAtMathlibHumanTheorems`
-/
def readETMHTEvaluateFiles (config : EvalTacticOnMathlibConfig) : CoreM (Array Name × Array (Name × Nat)) := do
  let resultFolder := config.resultFolder
  let content ← IO.FS.readFile (resultFolder ++ "/evaluateFiles.txt")
  let lines := (content.splitOn "\n").filter (fun line => line != "")
  let mut retStart := #[]
  let mut retEnd := #[]
  let str2Name (s : String) := (s.splitOn ".").foldl (fun cur field => Name.str cur field) Name.anonymous
  for line in lines do
    if line.contains ':' then
      let [name, retCode] := line.splitOn ":"
        | throwError "{decl_name%} :: Unexpected line format, line content : `{line}`"
      let name := name.dropRight 1
      let retCode := retCode.drop 1
      let some retCode := retCode.toNat?
        | throwError "{decl_name%} :: Unexpected line format, line content : `{line}`"
      retEnd := retEnd.push (str2Name name, retCode)
    else
      retStart := retStart.push (str2Name line)
  return (retStart, retEnd)
