import Lean
import Auto.EvaluateAuto.Result
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.NameArr
import Auto.EvaluateAuto.CommandAnalysis
open Lean

namespace EvalAuto

open Elab Tactic

section Tactics

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
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmIdents := usedThmNames.map Lean.mkIdent
    let configClause ← mkAesopConfigStx subHeartbeats
    let addClauses := usedThmIdents.map mkAddIdentStx
    let aesopStx := mkAesopStx (#[configClause] ++ addClauses)
    let stx ← `(tactic|intros; $aesopStx)
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
                  #[Lean.Syntax.node synth `Aesop.Frontend.Parser.featIdent #[ident]]
              ]
            ],
            Syntax.atom synth ")"
        ]

  inductive RegisteredTactic where
    | useRfl
    | useSimp
    | useSimpAll
    | useSimpAllWithPremises
    | useAesop (subHeartbeats : Nat)
    | useAesopWithPremises (subHeartbeats : Nat)
  deriving BEq, Hashable

  instance : ToString RegisteredTactic where
    toString : RegisteredTactic → String
    | .useRfl                  => "useRfl"
    | .useSimp                 => "useSimp"
    | .useSimpAll              => "useSimpAll"
    | .useSimpAllWithPremises  => "useSimpAllWithPremises"
    | .useAesop sh             => s!"useAesop {sh}"
    | .useAesopWithPremises sh => s!"useAesopWithPremises {sh}"

  def RegisteredTactic.toCiTactic : RegisteredTactic → ConstantInfo → TacticM Unit
    | .useRfl                  => fun _ => EvalAuto.useRfl
    | .useSimp                 => fun _ => EvalAuto.useSimp
    | .useSimpAll              => fun _ => EvalAuto.useSimpAll
    | .useSimpAllWithPremises  => EvalAuto.useSimpAllWithPremises
    | .useAesop sh             => fun _ => EvalAuto.useAesop sh
    | .useAesopWithPremises sh => EvalAuto.useAesopWithPremises sh

end Tactics

/--
  Use `runWithEffectOfCommands` to run tactics at the place just before
  the command that created the constant `name`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files
-/
def runTacticsAtConstantDeclaration
  (name : Name) (searchPath : SearchPath)
  (tactics : Array (ConstantInfo → TacticM Unit)) : CoreM (Array Result) := do
  if ← isInitializerExecutionEnabled then
    throwError "{decl_name%} :: Running this function with execution of `initialize` code enabled is unsafe"
  let .some modName ← Lean.findModuleOf? name
    | throwError "{decl_name%} :: Cannot find constant {name}"
  let .some uri ← Server.documentUriFromModule searchPath modName
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

/--
  Effectively `runTacticsAtConstantDeclaration` at each constant in `modName` which satisfies `filter`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files
-/
def evalAtModule
  (modName : Name) (searchPath : SearchPath) (filter : ConstantInfo → Bool)
  (config : EvalTacticConfig) : CoreM Unit:= do
  let logFileHandle? : Option IO.FS.Handle ← config.logFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  let resultFileHandle? : Option IO.FS.Handle ← config.resultFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  trace[auto.eval.printConfig] m!"Config = {config}"
  if let .some fhandle := logFileHandle? then
    fhandle.putStrLn s!"Config = {config}"
  let .some uri ← Server.documentUriFromModule searchPath modName
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
    fhandle.putStrLn s!"Elapsed time : {(← IO.monoMsNow) - startTime} ms"
    fhandle.putStrLn s!"\nSummary:\n"
    for ((name, result), idx) in results.zipWithIndex do
      fhandle.putStrLn s!"{idx} {result.map Result.concise} {name}"
where
  evalAction
    (context : Core.Context) (state : Core.State) (ci : ConstantInfo)
    (logFileHandle? : Option IO.FS.Handle) (config : EvalTacticConfig)
    (nonterms : Std.HashSet (RegisteredTactic × Name)) : IO (Array Result) := do
  config.tactics.zipWithIndex.mapM (fun (tactic, idx) => do
    let metaAction : MetaM Result :=
      Term.TermElabM.run' <| Result.ofTacticOnExpr ci.type (tactic.toCiTactic ci)
    let coreAction : CoreM Result := (do
      trace[auto.eval.printProblem] m!"Testing tactic {idx} || {ci.name} : {ci.type}"
      if let .some fhandle := logFileHandle? then
        fhandle.putStrLn ""
        fhandle.putStrLn s!"Testing tactic {idx} || {ci.name} : {← (Lean.Meta.ppExpr ci.type).run'}"
        fhandle.flush
      let result ← (do
        if nonterms.contains (tactic, ci.name) then
          return Result.nonterminate
        else
          withCurrHeartbeats <|
            withReader (fun ctx => { ctx with maxHeartbeats := config.maxHeartbeats * 1000 }) <|
              Meta.MetaM.run' metaAction)
      trace[auto.eval.printResult] m!"{result}"
      if let .some fhandle := logFileHandle? then
        fhandle.putStrLn (toString (← MessageData.format m!"{result}"))
      return result)
    let (result, _) ← coreAction.toIO context state
    return result)

structure EvalTacticOnMathlibConfig where
  /-- Timeout for each tactic -/
  maxHeartbeats : Nat           := 65536
  /-- Tactics to run at each constant declaration -/
  tactics       : Array RegisteredTactic
  /-- Folder for saving the result of the evaluation -/
  resultFolder  : String
  /--
    On some problems, certain tactics may go into infinite loops not
    guarded by `Core.checkMaxHeartbeats`. These instances should be
    recorded here and avoided (throw error immediately) during evaluation.
  -/
  nonterminates : Array (RegisteredTactic × Name)
  /--
    Number of threads to use
  -/
  nthreads      : Nat

abbrev EvalProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

def EvalProc.create (path : String) (args : Array String) : IO EvalProc :=
  IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped, cmd := path, args := args}

/--
  This should be run after `import Mathlib`, and should be run with a `cwd` where
    `lake env` creates an environment in which `Mathlib` and `lean-auto` are available
-/
def evalTacticsAtMathlibHumanTheorems (config : EvalTacticOnMathlibConfig) : CoreM Unit := do
  let mms ← mathlibModules
  if !(← allMathlibModuleNamesCanBeFilename) then
    throwError "{decl_name%} :: Some mathlib modules have extra-ordinary names. Evaluation code needs to be changed!"
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
    let evalProc ← EvalProc.create "lake" #["env", "lean", "--stdin"]
    let logPath := config.resultFolder ++ extraLogPath
    let validThms := (allTally.get? mm).getD #[]
    evalProc.stdin.putStr (evalFile mm validThms logPath config.tactics)
    let (_, evalProc) ← evalProc.takeStdin
    running := running.push (mm, evalProc)
    while running.size >= config.nthreads do
      running ← tryWaitOn evaluateFilesHandle running
  while running.size != 0 do
    running ← tryWaitOn evaluateFilesHandle running
where
  tryWaitOn (evaluateFilesHandle : IO.FS.Handle) (running : Array (Name × _)) : CoreM (Array (Name × _)) := do
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
    (logPath : String) (tacs : Array RegisteredTactic) : String :=
    let lb := "{"
    let rb := "}"
    let thmsStrs : List String :=
      match validThms.toList.getLast? with
      | .some last =>
        validThms.toList.dropLast.map (fun n => s!"  {repr n},") ++ [s!"  {repr last}"]
      | .none => []
    let tacsStr := String.intercalate ", " (tacs.map (fun tac => "." ++ toString tac)).toList
    let lines := [
        s!"import {mm}",
        "import Auto.EvaluateAuto.TestTactics",
        "import Aesop",
        "open Lean EvalAuto",
        "",
        "def humanThms : Std.HashSet Name := Std.HashSet.ofList ["
      ] ++ thmsStrs ++ [
        "]",
        "",
        "def action : CoreM Unit := do",
        "  let p ← initSrcSearchPath",
        s!"  let _ ← evalAtModule ({repr mm}) p (fun ci => humanThms.contains ci.name)",
        s!"    {lb} tactics := #[{tacsStr}],",
        s!"      logFile := {repr (logPath ++ ".log")}, resultFile := {repr (logPath ++ ".result")},",
        s!"      nonterminates := #[] {rb}",
        "",
        "set_option auto.evalAuto.ensureAesop true",
        "#eval action"
      ]
    String.intercalate "\n" lines

end EvalAuto
