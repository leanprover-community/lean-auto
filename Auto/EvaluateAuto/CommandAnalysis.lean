import Lean
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.Result
open Lean

namespace EvalAuto

open Elab Frontend
def runWithEffectOfCommandsCore
  (cnt? : Option Nat)
  (action : Context → State → State → ConstantInfo → IO (Option α)) : FrontendM (Array α) := do
  let mut done := false
  let mut ret := #[]
  let mut cnt := 0
  while !done do
    if cnt?.isSome && cnt >= cnt?.getD 0 then
      break
    let prev ← get
    done ← Frontend.processCommand
    let post ← get
    let newConsts := Environment.newLocalConstants prev.commandState.env post.commandState.env
    for newConst in newConsts do
      if let .some result ← action (← read) prev post newConst then
        cnt := cnt + 1
        ret := ret.push result
        if cnt?.isSome && cnt >= cnt?.getD 0 then
          break
  return ret

/--
  Given a Lean4 file `fileName` with content `input` consisting of
  a header and a series of commands, first parse the header. Then,
  for each command `cmd`, record the states `st₁, st₂` before and
  after executing the command, and run `action` on the `ConstantInfo`s produced
  by `cmd`, together with `st₁, st₂` and the `InputContext`.\
  An additional `cnt?` can be supplied to control termination.
  When the number of times `action` returns `.some _` reaches `cnt?`,
  the procedure is terminated.
-/
def runWithEffectOfCommands
  (input : String) (fileName : String) (opts : Options := {}) (cnt? : Option Nat)
  (action : Context → State → State → ConstantInfo → IO (Option α)) : IO (Array α) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let commandState := Command.mkState env messages opts
  (runWithEffectOfCommandsCore cnt? action { inputCtx }).run'
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

open Elab Tactic in
/--
  Run `tactic` on a metavariable with type `e` and obtain the result
-/
def Result.ofTacticOnExpr (e : Expr) (tactic : TacticM Unit) : TermElabM Result := do
  let .mvar mid ← Meta.mkFreshExprMVar e
    | throwError "{decl_name%} : Unexpected error"
  let result : List MVarId ⊕ Exception ← tryCatchRuntimeEx
    (do let goals ← Term.TermElabM.run' (Tactic.run mid tactic) {}; return .inl goals)
    (fun e => return .inr e)
  match result with
  | .inl goals =>
    if goals.length >= 1 then
      return .subGoals
    let proof ← instantiateMVars (.mvar mid)
    match Kernel.check (← getEnv) {} proof with
    | Except.ok autoProofType =>
      match Kernel.isDefEq (← getEnv) {} autoProofType e with
      | Except.ok true => return .success
      | _ => return .typeUnequal
    | Except.error _ => return .typeCheckFail
  | .inr e => return (.exception e)

open Elab Tactic in
/--
  Note: Use `initSrcSearchPath` to get SearchPath of Lean4's builtin source files
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
  let results : Array (Array Result) ← runWithEffectOfCommands input path.toString {} (.some 1) (fun ctx st₁ st₂ ci => do
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

section Tactics

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

end Tactics

end EvalAuto
