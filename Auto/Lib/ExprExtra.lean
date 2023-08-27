import Lean
open Lean Elab Command

namespace Auto

def Expr.binders (e : Expr) : Array (Name × Expr × BinderInfo) :=
  let rec aux (e : Expr) :=
    match e with
    | .forallE n ty b bi => (n, ty, bi) :: aux b
    | _ => []
  Array.mk (aux e)

private def Expr.instArgsIdx (e : Expr) (idx : Nat) : List Nat :=
  match e with
  | .forallE _ _ body bi =>
    let trail := instArgsIdx body (.succ idx)
    match bi with
    | .instImplicit => idx :: trail
    | _ => trail
  | _ => .nil

-- Given an expression `e`, which is the type of some
--   term `t`, find the arguments of `t` that are class
--   instances
def Expr.instArgs (e : Expr) : Array Nat := ⟨Expr.instArgsIdx e 0⟩

private def Expr.depArgsIdx (e : Expr) (idx : Nat) : List Nat :=
  match e with
  | .forallE _ _ body _ =>
    let trail := depArgsIdx body (.succ idx)
    match body.hasLooseBVar idx with
    | true  => idx :: trail
    | false => trail
  | _ => .nil

-- Given `e = ∀ (xs : αs), t`, return the indexes of dependent `∀` binders
--  within `xs`
def Expr.depArgs (e : Expr) : Array Nat := ⟨Expr.depArgsIdx e 0⟩

-- Given the name `c` of a constant, suppose `@c : ty`, return
--   `Expr.depArgs ty`
def Expr.constDepArgs (c : Name) : CoreM (Array Nat) := do
  let .some decl := (← getEnv).find? c
    | throwError "Expr.constDepArgs :: Unknown constant {c}"
  return Expr.depArgs decl.type

-- This should only be used when we're sure that reducing `ty`
--   won't be too expensive
def normalizeType (ty : Expr) : MetaM Expr := do
  let ty ← Meta.reduceAll ty
  return ← instantiateMVars ty

-- `ident` must be of type `Expr → TermElabM Unit`
-- Compiles `term` into `Expr`, then applies `ident` to it
syntax (name := getExprAndApply) "#getExprAndApply" "[" term "|" ident "]" : command

@[command_elab Auto.getExprAndApply]
unsafe def elabGetExprAndApply : CommandElab := fun stx =>
  runTermElabM fun _ => do
    match stx with
    | `(command | #getExprAndApply[ $t:term | $i:ident ]) => withRef stx <| do
      let some iexpr ← Term.resolveId? i
        | throwError "elabGetExprAndApply :: Unknown identifier {i}"
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      let fname := iexpr.constName!
      match (← getEnv).evalConst (Expr → TermElabM Unit) (← getOptions) fname with
      | Except.ok f => f e
      | Except.error err => throwError "elabGetExprAndApply :: Failed to evaluate {fname} to a term of type (Expr → TermElabM Unit), error : {err}"
    | _ => throwUnsupportedSyntax

-- Consider the canonical instance of `Lean.ToExpr Expr`. We require that
--   `(← exprFromExpr (← Lean.toExpr e)) ≝ e`
unsafe def exprFromExpr (eToExpr : Expr) : TermElabM Expr := do
  let ty ← Meta.inferType eToExpr
  if ! (← Meta.isDefEq ty (.const ``Expr [])) then
    throwError "exprFromExpr :: Type `{ty}` of input is not definitionally equal to `Expr`"
  let declName := `_exprFromExpr
  let addAndCompile (value : Expr) : TermElabM Unit := do
    let value ← Term.levelMVarToParam (← instantiateMVars value)
    let type ← Meta.inferType value
    let us := collectLevelParams {} value |>.params
    let value ← instantiateMVars value
    let decl := Declaration.defnDecl {
      name        := declName
      levelParams := us.toList
      type        := type
      value       := value
      hints       := ReducibilityHints.opaque
      safety      := DefinitionSafety.unsafe
    }
    Term.ensureNoUnassignedMVars decl
    addAndCompile decl
  let env ← getEnv
  let e ← try addAndCompile eToExpr; evalConst Expr declName finally setEnv env
  return e

syntax (name := lazyReduce) "#lazyReduce" term : command

register_option lazyReduce.skipProof : Bool := {
  defValue := true
  descr    := "Whether to reduce proof when calling #lazyReduce"
}

register_option lazyReduce.skipType : Bool := {
  defValue := true
  descr    := "Whether to reduce type when calling #lazyReduce"
}

register_option lazyReduce.logInfo : Bool := {
  defValue := true
  descr    := "Whether to print result of #reduce"
}

register_option lazyReduce.printTime : Bool := {
  defValue := false
  descr    := "Whether to print result of #reduce"
}

open Meta in
@[command_elab Auto.lazyReduce] def elabLazyReduce : CommandElab
  | `(#lazyReduce%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let startTime ← IO.monoMsNow
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let opts ← getOptions
    let skipProof? := lazyReduce.skipProof.get opts
    let skipType? := lazyReduce.skipType.get opts
    let logInfo? := lazyReduce.logInfo.get opts
    let printTime? := lazyReduce.printTime.get opts
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <| reduce e (skipProofs := skipProof?) (skipTypes := skipType?)
      if logInfo? then
        logInfoAt tk e
      if printTime? then
        IO.println s!"{(← IO.monoMsNow) - startTime} ms"
  | _ => throwUnsupportedSyntax

section EvalAtTermElabM

  open Meta

  private def mkEvalInstCore (evalClassName : Name) (e : Expr) : MetaM Expr := do
    let α    ← inferType e
    let u    ← getDecLevel α
    let inst := mkApp (Lean.mkConst evalClassName [u]) α
    try
      synthInstance inst
    catch _ =>
      -- Put `α` in WHNF and try again
      try
        let α ← whnf α
        synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
      catch _ =>
        -- Fully reduce `α` and try again
        try
          let α ← reduce (skipTypes := false) α
          synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
        catch _ =>
          throwError "expression{indentExpr e}\nhas type{indentExpr α}\nbut instance{indentExpr inst}\nfailed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `{evalClassName}` class"
  
  private def mkRunMetaEval (e : Expr) : MetaM Expr :=
    withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
    withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
      let α ← inferType e
      let u ← getDecLevel α
      let instVal ← mkEvalInstCore ``Lean.MetaEval e
      let e := mkAppN (mkConst ``Lean.runMetaEval [u]) #[α, instVal, env, opts, e]
      instantiateMVars (← mkLambdaFVars #[env, opts] e)
  
  private def mkRunEval (e : Expr) : MetaM Expr := do
    let α ← inferType e
    let u ← getDecLevel α
    let instVal ← mkEvalInstCore ``Lean.Eval e
    instantiateMVars (mkAppN (mkConst ``Lean.runEval [u]) #[α, instVal, mkSimpleThunk e])
  
  unsafe def termElabEval (elabEvalTerm : Expr) : TermElabM Unit := do
    let declName := `_eval
    let addAndCompile (value : Expr) : TermElabM Unit := do
      let value ← Term.levelMVarToParam (← instantiateMVars value)
      let type ← inferType value
      let us := collectLevelParams {} value |>.params
      let value ← instantiateMVars value
      let decl := Declaration.defnDecl {
        name        := declName
        levelParams := us.toList
        type        := type
        value       := value
        hints       := ReducibilityHints.opaque
        safety      := DefinitionSafety.unsafe
      }
      Term.ensureNoUnassignedMVars decl
      addAndCompile decl
    -- Elaborate `term`
    -- Evaluate using term using `MetaEval` class.
    let elabMetaEval : TermElabM Unit := do
      -- act? is `some act` if elaborated `term` has type `TermElabM α`
      let act? ← Term.withDeclName declName do
        let e := elabEvalTerm
        let eType ← instantiateMVars (← inferType e)
        if eType.isAppOfArity ``TermElabM 1 then
          let mut stx ← Term.exprToSyntax e
          unless (← isDefEq eType.appArg! (mkConst ``Unit)) do
            stx ← `($stx >>= fun v => IO.println (repr v))
          let act ← Lean.Elab.Term.evalTerm (TermElabM Unit) (mkApp (mkConst ``TermElabM) (mkConst ``Unit)) stx
          pure <| some act
        else
          let e ← mkRunMetaEval e
          let env ← getEnv
          let opts ← getOptions
          let act ← try addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) declName finally setEnv env
          let (out, res) ← act env opts -- we execute `act` using the environment
          logInfo out
          match res with
          | Except.error e => throwError e.toString
          | Except.ok env  => do setEnv env; pure none
      let some act := act? | return ()
      act
    -- Evaluate using term using `Eval` class.
    let elabEval : TermElabM Unit := Term.withDeclName declName do
      -- fall back to non-meta eval if MetaEval hasn't been defined yet
      -- modify e to `runEval e`
      let e ← mkRunEval elabEvalTerm
      let env ← getEnv
      let act ← try addAndCompile e; evalConst (IO (String × Except IO.Error Unit)) declName finally setEnv env
      let (out, res) ← liftM (m := IO) act
      logInfo out
      match res with
      | Except.error e => throwError e.toString
      | Except.ok _    => pure ()
    if (← getEnv).contains ``Lean.MetaEval then do
      elabMetaEval
    else
      elabEval

end EvalAtTermElabM
      
end Auto