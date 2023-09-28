import Lean
import Auto.Lib.LevelExtra
open Lean Elab Command

namespace Auto

def Expr.hasCurrentDepthLevelMVar : Expr → MetaM Bool
| .sort l => Level.hasCurrentDepthLevelMVar l
| .const _ ls => ls.anyM Level.hasCurrentDepthLevelMVar
| .forallE _ d b _ => or <$> hasCurrentDepthLevelMVar d <*> hasCurrentDepthLevelMVar b
| .lam _ d b _ => or <$> hasCurrentDepthLevelMVar d <*> hasCurrentDepthLevelMVar b
| .letE _ t v b _ =>
  or <$> hasCurrentDepthLevelMVar t <*> (
    or <$> hasCurrentDepthLevelMVar v <*> hasCurrentDepthLevelMVar b)
| .app f a => or <$> hasCurrentDepthLevelMVar f <*> hasCurrentDepthLevelMVar a
| .mdata _ b => hasCurrentDepthLevelMVar b
| .proj _ _ e => hasCurrentDepthLevelMVar e
| _ => pure false

def Expr.findParam? (p : Name → Bool) : Expr → Option Name
| .sort l => Level.findParam? p l
| .const _ ls => ls.foldl (fun acc x => Option.orElse acc (fun _ => Level.findParam? p x)) .none
| .forallE _ d b _ => Option.orElse (findParam? p d) (fun _ => findParam? p b)
| .lam _ d b _ => Option.orElse (findParam? p d) (fun _ => findParam? p b)
| .letE _ t v b _ => Option.orElse (findParam? p t) (fun _ =>
    Option.orElse (findParam? p v) (fun _ => findParam? p b))
| .app f a => Option.orElse (findParam? p f) (fun _ => findParam? p a)
| .mdata _ b => findParam? p b
| .proj _ _ e => findParam? p e
| _ => .none

def Expr.forallBinders (e : Expr) : Array (Name × Expr × BinderInfo) :=
  let rec aux (e : Expr) :=
    match e with
    | .forallE n ty b bi => (n, ty, bi) :: aux b
    | _ => []
  Array.mk (aux e)

def Expr.lambdaBinders (e : Expr) : Array (Name × Expr × BinderInfo) :=
  let rec aux (e : Expr) :=
    match e with
    | .lam n ty b bi => (n, ty, bi) :: aux b
    | _ => []
  Array.mk (aux e)

def Expr.mkForallFromBinderDescrs (binders : Array (Name × Expr × BinderInfo)) (e : Expr) :=
  binders.foldr (fun (n, ty, bi) e => Expr.forallE n ty e bi) e

def Expr.mkLambdaFromBinderDescrs (binders : Array (Name × Expr × BinderInfo)) (e : Expr) :=
  binders.foldr (fun (n, ty, bi) e => Expr.lam n ty e bi) e

def Expr.stripForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ body _ => Expr.stripForall body
  | _ => e

def Expr.stripForallN (n : Nat) (e : Expr) : Option Expr :=
  match n with
  | 0 => .some e
  | n' + 1 =>
    match e with
    | .forallE _ _ body _ => Expr.stripForallN n' body
    | _ => .none

def Expr.stripLambda (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ => Expr.stripLambda body
  | _ => e

def Expr.stripLambdaN (n : Nat) (e : Expr) : Option Expr :=
  match n with
  | 0 => .some e
  | n' + 1 =>
    match e with
    | .lam _ _ body _ => Expr.stripLambdaN n' body
    | _ => .none

def Expr.getAppFnN (n : Nat) (e : Expr) : Option Expr :=
  match n with
  | 0 => .some e
  | n' + 1 =>
    match e with
    | .app fn _ => Expr.getAppFnN n' fn
    | _ => .none

private def Expr.getAppBoundedArgsAux (n : Nat) (e : Expr) : List Expr :=
  match n with
  | 0 => .nil
  | n' + 1 =>
    match e with
    | .app fn arg => arg :: Expr.getAppBoundedArgsAux n' fn
    | _ => .nil

def Expr.getAppBoundedArgs (n : Nat) (e : Expr) : Array Expr :=
  ⟨(Expr.getAppBoundedArgsAux n e).reverse⟩

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

private partial def Expr.depArgsIdx (e : Expr) (idx : Nat) : List Nat :=
  match e with
  | .forallE _ _ body _ =>
    -- Instantiate loose bound variable with any expression
    --   that does not contain loose bound variables
    let body' := body.instantiate1 (.sort .zero)
    let trail := depArgsIdx body' (.succ idx)
    match body.hasLooseBVars with
    | true  => idx :: trail
    | false => trail
  | _ => .nil

-- Given `e = ∀ (xs : αs), t`, return the indexes of dependent `∀` binders
--   within `xs`. This function only works for expressions that does not
--   contain loose bound variables
def Expr.depArgs (e : Expr) : Array Nat := ⟨Expr.depArgsIdx e 0⟩

-- Given the name `c` of a constant, suppose `@c : ty`, return
--   `Expr.depArgs ty`
def Expr.constDepArgs (c : Name) : CoreM (Array Nat) := do
  let .some decl := (← getEnv).find? c
    | throwError "Expr.constDepArgs :: Unknown constant {c}"
  return Expr.depArgs decl.type

private partial def Expr.instDepArgsIdx (e : Expr) (idx : Nat) : List Nat :=
  match e with
  | .forallE _ _ body bi =>
    let body' := body.instantiate1 (.sort .zero)
    let trail := instDepArgsIdx body' (.succ idx)
    if bi == .instImplicit || body.hasLooseBVars then
      idx :: trail
    else
      trail
  | _ => .nil

def Expr.instDepArgs (e : Expr) : Array Nat := ⟨Expr.instDepArgsIdx e 0⟩

def Expr.constInstDepArgs (c : Name) : CoreM (Array Nat) := do
  let .some decl := (← getEnv).find? c
    | throwError "Expr.constInstDepArgs :: Unknown constant {c}"
  return Expr.instDepArgs decl.type

-- Turn all `Prop` binders into `True`
private partial def Expr.isMonomorphicFactAux : Expr → MetaM Expr
| .forallE name ty body bi => do
  let ty := if (← Meta.isProp ty) ∧ !body.hasLooseBVars then .const ``False [] else ty
  Meta.withLocalDecl name bi ty fun x => do
    let body := body.instantiate1 x
    let body ← isMonomorphicFactAux body
    Meta.mkForallFVars #[x] body
| _ => pure (.const ``False [])

-- Test whether `e` is a monomorphic fact.
-- `e` is a monomorphic fact iff for all subterms `t : α` of `e`
--    where `α` is not of type `Prop`, `α` does not depend on bound
--    variables.
def Expr.isMonomorphicFact (e : Expr) : MetaM Bool := do
  let e ← Expr.isMonomorphicFactAux e
  return (Expr.depArgs e).size == 0

-- This should only be used when we're sure that reducing `ty`
--   won't be too expensive
-- e.g. `ty` must be defeq to `Expr.sort <?lvl>`
def Expr.normalizeType (ty : Expr) : MetaM Expr := do
  let ty ← Meta.reduceAll ty
  return ← instantiateMVars ty

def Expr.whnfIfNotForall (e : Expr) : MetaM Expr := do
  if e.isForall then
    return e
  else
    return (← Meta.whnf e)

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