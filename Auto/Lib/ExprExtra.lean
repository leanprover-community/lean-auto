import Lean
import Auto.Lib.LevelExtra
import Auto.Lib.Containers
import Auto.Lib.AbstractMVars
open Lean Elab Command

namespace Auto

def Expr.eraseMData : Expr → Expr
| .app fn arg => .app (eraseMData fn) (eraseMData arg)
| .lam name ty body bi => .lam name (eraseMData ty) (eraseMData body) bi
| .forallE name ty body bi => .forallE name (eraseMData ty) (eraseMData body) bi
| .letE name type value body nonDep => .letE name (eraseMData type) (eraseMData value) (eraseMData body) nonDep
| .mdata _ expr => expr
| .proj typeName idx struct => .proj typeName idx (eraseMData struct)
| e => e

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

def Expr.collectRawM [Monad m] (p : Expr → m Bool) : Expr → m (Std.HashSet Expr)
| e@(.forallE _ d b _) => do
  let hd ← collectRawM p d
  let hb ← collectRawM p b
  addp? p e (mergeHashSet hd hb)
| e@(.lam _ d b _) => do
  let hd ← collectRawM p d
  let hb ← collectRawM p b
  addp? p e (mergeHashSet hd hb)
| e@(.letE _ t v b _) => do
  let ht ← collectRawM p t
  let hv ← collectRawM p v
  let hb ← collectRawM p b
  addp? p e (mergeHashSet ht (mergeHashSet hv hb))
| e@(.app f a) => do
  let hf ← collectRawM p f
  let ha ← collectRawM p a
  addp? p e (mergeHashSet hf ha)
| e@(.mdata _ b) => do
  let hb ← collectRawM p b
  addp? p e hb
| e@(.proj _ _ b) => do
  let hb ← collectRawM p b
  addp? p e hb
| e => addp? p e Std.HashSet.empty
where addp? p e hs := do
  if ← p e then
    return hs.insert e
  else
    return hs

def Expr.lambdaBinders (e : Expr) : Array (Name × Expr × BinderInfo) :=
  let rec aux (e : Expr) :=
    match e with
    | .lam n ty b bi => (n, ty, bi) :: aux b
    | _ => []
  Array.mk (aux e)

def Expr.isDepForall (e : Expr) : Bool :=
  match e with
  | .forallE _ _ body _ => body.hasLooseBVar 0
  | _ => false

def Expr.isDepLambda (e : Expr) : Bool :=
  match e with
  | .lam _ _ body _ => body.hasLooseBVar 0
  | _ => false

def Expr.mkForallFromBinderDescrs (binders : Array (Name × Expr × BinderInfo)) (e : Expr) :=
  binders.foldr (fun (n, ty, bi) e => Expr.forallE n ty e bi) e

def Expr.mkLambdaFromBinderDescrs (binders : Array (Name × Expr × BinderInfo)) (e : Expr) :=
  binders.foldr (fun (n, ty, bi) e => Expr.lam n ty e bi) e

def Expr.stripForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ body _ => Expr.stripForall body
  | _ => e

def Expr.stripLeadingDepForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ body _ =>
    if body.hasLooseBVar 0 then
      stripLeadingDepForall body
    else
      e
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

def Expr.stripLeadingDepLambda (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ =>
    if body.hasLooseBVar 0 then
      stripLeadingDepLambda body
    else
      e
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

/--
  Given an expression `e`, which is the type of some term
    `t`, find the arguments of `t` that are class instances
-/
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

/--
  Given `e = ∀ (xs : αs), t`, return the indexes of dependent `∀` binders
    within `xs`. This function only works for expressions that does not
    contain loose bound variables
-/
def Expr.depArgs (e : Expr) : Array Nat := ⟨Expr.depArgsIdx e 0⟩

/--
  Given the name `c` of a constant, suppose `@c : ty`, return
    `Expr.depArgs ty`
-/
def Expr.constDepArgs (c : Name) : CoreM (Array Nat) := do
  let .some decl := (← getEnv).find? c
    | throwError "{decl_name%} :: Unknown constant {c}"
  return Expr.depArgs decl.type

def Expr.numLeadingDepArgs : Expr → Nat
| .forallE _ _ body _ =>
  if body.hasLooseBVar 0 then
    numLeadingDepArgs body + 1
  else
    0
| _ => 0

/--
  This should only be used when we're sure that reducing `ty`
    won't be too expensive
  e.g. `ty` must be defeq to `Expr.sort <?lvl>`
-/
def Expr.normalizeType (ty : Expr) : MetaM Expr := do
  let ty ← Meta.reduceAll ty
  return ← instantiateMVars ty

def Expr.whnfIfNotForall (e : Expr) : MetaM Expr := do
  if e.isForall then
    return e
  else
    return (← Meta.whnf e)

/--
  Given expression `e₁, e₂`, attempt to find variables `x₁, ⋯, xₗ`,
  terms `t₁, ⋯, tₖ` and a `m ≤ l` such that `∀ x₁ ⋯ xₗ. e₁ x₁ ⋯ xₘ = e₂ t₁ ⋯ tₖ`
  Note that universe polymorphism is not supported

  If successful, return
    `(fun x₁ ⋯ xₗ => Eq.refl (e₁ x₁ ⋯ xₘ), ∀ x₁ ⋯ xₗ. e₁ x₁ ⋯ xₘ = e₂ t₁ ⋯ tₖ)`\
  Otherwise, return `.none`
-/
def Expr.instanceOf? (e₁ e₂ : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty₁ ← Meta.inferType e₁
  let ty₂ ← Meta.inferType e₂
  Meta.forallTelescope ty₁ fun xs _ => do
    let (ms, _, _) ← Meta.forallMetaTelescope ty₂
    let e₁app := mkAppN e₁ xs
    let e₂app := mkAppN e₂ ms
    if ← Meta.isDefEq e₁app e₂app then
      let e₂app ← instantiateMVars e₂app
      let (e₂app, s) := AbstractMVars.abstractExprMVars e₂app { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen)}
      setNGen s.ngen; setMCtx s.mctx
      Meta.withLCtx s.lctx (← Meta.getLocalInstances) <| do
        let proof ← Meta.mkLambdaFVars (xs ++ s.fvars) (← Meta.mkAppM ``Eq.refl #[e₁app])
        let eq ← Meta.mkForallFVars (xs ++ s.fvars) (← Meta.mkAppM ``Eq #[e₁app, e₂app])
        return (proof, eq)
    else
      return .none

def Expr.formatWithUsername (e : Expr) : MetaM Format := do
  let fvarIds := (collectFVars {} e).fvarIds
  let names ← fvarIds.mapM (fun fid => do
    match ← fid.findDecl? with
    | .some decl => return decl.userName
    | .none => throwError "{decl_name%}e :: Unknown free variable {(Expr.fvar fid).dbgToString}")
  let e := e.replaceFVars (fvarIds.map Expr.fvar) (names.map (Expr.const · []))
  let e ← instantiateMVars e
  let mvarIds := (Expr.collectMVars {} e).result
  let names ← mvarIds.mapM (fun mid => do
    match ← mid.findDecl? with
    | .some decl => return decl.userName
    | .none => throwError "{decl_name%} :: Unknown metavariable {(Expr.mvar mid).dbgToString}")
  let e := (e.abstract (mvarIds.map Expr.mvar)).instantiateRev (names.map (Expr.const · []))
  return f!"{e}"

/--
  `ident` must be of type `Expr → TermElabM Unit`
  Compiles `term` into `Expr`, then applies `ident` to it
-/
syntax (name := getExprAndApply) "#getExprAndApply" "[" term "|" ident "]" : command

@[command_elab Auto.getExprAndApply]
unsafe def elabGetExprAndApply : CommandElab := fun stx =>
  runTermElabM fun _ => do
    match stx with
    | `(command | #getExprAndApply[ $t:term | $i:ident ]) => withRef stx <| do
      let some iexpr ← Term.resolveId? i
        | throwError "{decl_name%} :: Unknown identifier {i}"
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      let fname := iexpr.constName!
      match (← getEnv).evalConst (Expr → TermElabM Unit) (← getOptions) fname with
      | Except.ok f => f e
      | Except.error err => throwError "{decl_name%} :: Failed to evaluate {fname} to a term of type (Expr → TermElabM Unit), error : {err}"
    | _ => throwUnsupportedSyntax

/--
  Consider the canonical instance of `Lean.ToExpr Expr`. We require that
    `(← exprFromExpr (← Lean.toExpr e)) ≝ e`
-/
unsafe def exprFromExpr (eToExpr : Expr) : TermElabM Expr := do
  let ty ← Meta.inferType eToExpr
  if ! (← Meta.isDefEq ty (.const ``Expr [])) then
    throwError "{decl_name%} :: Type `{ty}` of input is not definitionally equal to `Expr`"
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

end Auto
