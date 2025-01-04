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

  private def mkAesopStx (addClauses : Array Syntax) : TSyntax `tactic :=
    let synth : SourceInfo := SourceInfo.synthetic default default false
    TSyntax.mk (
      Syntax.node synth `Aesop.Frontend.Parser.aesopTactic
        #[Syntax.atom synth "aesop", Syntax.node synth `null addClauses]
    )

  /--
    Tactic sequence: `intros; aesop`
    Only guaranteed to work for `aesop @ Lean v4.14.0`
  -/
  def useAesop : TacticM Unit := do
    let aesopStx := mkAesopStx #[]
    let stx ← `(tactic|intros; $aesopStx)
    evalTactic stx

  /--
    Tactic sequence: `intros; aesop (add unsafe premise₁) ⋯ (add unsafe premiseₙ)`
    Only guaranteed to work for `aesop @ Lean v4.14.0`
  -/
  def useAesopWithPremises (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmIdents := usedThmNames.map Lean.mkIdent
    let addClauses := usedThmIdents.map mkAddIdentStx
    let aesopStx := mkAesopStx addClauses
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
    | useAesop
    | useAesopWithPremises

  instance : ToString RegisteredTactic where
    toString : RegisteredTactic → String
    | .useRfl                 => "useRfl"
    | .useSimp                => "useSimp"
    | .useSimpAll             => "useSimpAll"
    | .useSimpAllWithPremises => "useSimpAllWithPremises"
    | .useAesop               => "useAesop"
    | .useAesopWithPremises   => "useAesopWithPremises"

  def RegisteredTactic.toCiTactic : RegisteredTactic → ConstantInfo → TacticM Unit
    | .useRfl                 => fun _ => EvalAuto.useRfl
    | .useSimp                => fun _ => EvalAuto.useSimp
    | .useSimpAll             => fun _ => EvalAuto.useSimpAll
    | .useSimpAllWithPremises => EvalAuto.useSimpAllWithPremises
    | .useAesop               => fun _ => EvalAuto.useAesop
    | .useAesopWithPremises   => EvalAuto.useAesopWithPremises

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
  /-- Optional logfile for saving the result of the evaluation -/
  logFile       : Option String := .none

instance : ToString EvalTacticConfig where
  toString : EvalTacticConfig → String
  | ⟨maxHeartbeats, tactics, logFile⟩ =>
    let logFileStr :=
      match logFile with
      | .some logFile => s!", logFile := {logFile}"
      | .none => ""
    s!"\{maxHeartbeats := {maxHeartbeats}, tactics := {tactics}{logFileStr}}"

/--
  Effectively `runTacticsAtConstantDeclaration` at each constant in `modName` which satisfies `filter`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files
-/
def evalAtModule
  (modName : Name) (searchPath : SearchPath) (filter : ConstantInfo → Bool)
  (config : EvalTacticConfig) : CoreM Unit:= do
  let logFileHandle? : Option IO.FS.Handle ← config.logFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
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
  let results ← runWithEffectOfCommands input path.toString .none (fun ctx st₁ st₂ ci => do
    if filter ci then
      let result ← evalAction
        {fileName := path.toString, fileMap := FileMap.ofString input } { env := st₁.commandState.env }
        ci logFileHandle? config
      return .some (ci.name, result)
    else
      return .none)
  if let .some fhandle := logFileHandle? then
    fhandle.putStrLn ""
    fhandle.putStrLn s!"Elapsed time : {(← IO.monoMsNow) - startTime} ms"
    fhandle.putStrLn s!"\nSummary:\n"
    for ((name, result), idx) in results.zipWithIndex do
      fhandle.putStrLn s!"{idx} {result.map Result.concise} {name}"
where
  evalAction
    (context : Core.Context) (state : Core.State) (ci : ConstantInfo)
    (logFileHandle? : Option IO.FS.Handle) (config : EvalTacticConfig) : IO (Array Result) := do
  config.tactics.zipWithIndex.mapM (fun (tactic, idx) => do
    let metaAction : MetaM Result :=
      Term.TermElabM.run' <| Result.ofTacticOnExpr ci.type (tactic.toCiTactic ci)
    let coreAction : CoreM Result := (do
      trace[auto.eval.printProblem] m!"Testing tactic {idx} || {ci.name} : {ci.type}"
      if let .some fhandle := logFileHandle? then
        fhandle.putStrLn ""
        fhandle.putStrLn s!"Testing tactic {idx} || {ci.name} : {← (Lean.Meta.ppExpr ci.type).run'}"
      let result ← withCurrHeartbeats <|
        withReader (fun ctx => { ctx with maxHeartbeats := config.maxHeartbeats * 1000 }) <|
          Meta.MetaM.run' metaAction
      trace[auto.eval.printResult] m!"{result}"
      if let .some fhandle := logFileHandle? then
        fhandle.putStrLn (toString (← MessageData.format m!"{result}"))
      return result)
    let (result, _) ← coreAction.toIO context state
    return result)

end EvalAuto
