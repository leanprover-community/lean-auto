-- Processing Universe Levels
import Lean
import Auto.Translation.Lift
import Auto.Util.ExprExtra
import Auto.Util.MonadUtils
open Lean

namespace Auto.ULift

-- For an expression `e`, we denote its lifted version as `e↑`. For the
--   following discussion, we assume that we want to lift everything
--   to universe level `u`.
-- `cstULiftPos u e ty`:
--   Given a type `ty` an expression `e : ty`, return
--   (1) `e↑`
--   (2) The type of `e↑`, i.e. `ty×`
-- `cstULiftNeg u e↑ ty`:
--   Given a type `ty` and an expression `e↑` where `e↑ : ty×`, return
--   (1) `(e↑)↓`
--   (2) The type of `e↑`, i.e. `ty×`.
--   Note that the type of `e↑` is unknown when we call `cstULiftNeg`
--   because there will be a free variable of unknown type acting
--   as a hole inside `e↑`. This also explains why we need to
--   return `ty×`.
-- Note that `ULift` proceeds by structural recursion on
--   `ty`, not on `e`.

-- **Usage:** `cstULift` can be used to calculate ULift-ed version
--   of expressions. However, un-lifted constants and free variables
--   may still occur in the `ty×` returned by `cstULift`. So we'll
--   have to use another function `exprULift`, which will be described
--   below
-- Suppose we have a constant/free variable `A`. To calculate the
--   ULift-ed version of `A` (denoted as `A↑`),
--   (1) Compute the type of `A` (denoted as `ty`), instantiate
--       metavariables in `ty` and β-reduce & ζ-reduce it to obtain `ty*`.
--   (2) Let `u` be the universe level you want to lift to.
--       Call `let A↑ ← cstULiftPos u A ty` to obtain the ULift-ed
--       version of `A`

-- **Note:** If `e : ty`, the expected typing relation is `e↑ : GLift (ty↑).down`

mutual
  -- In the return type, the first `Expr` is `e↑`, and the second `Expr` is
  --   the type of `e↑`
  partial def cstULiftPos (u : Level) (e : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "Auto.cstULift :: Loose bound variable"
  | .lam .. => throwError "Auto.cstULift :: Please β-reduce type before calling cstULift"
  | .letE .. => throwError "Auto.cstULift :: Please ζ-reduce type before calling cstULift"
  | .lit .. => throwError "Auto.cstULift :: Malformed type"
  | .proj .. => throwError "Auto.cstULift :: Please unfold projections in type before calling cstULift"
  | .forallE name biTy body binfo => do
    -- We want to reate a free variable (intended) of type `bity↑`.
    --   However, we still don't what's `bity↑`, so we first
    --   create a metavariable representing `bity↑`
    let biUpTyLvl? ← Meta.mkFreshLevelMVar
    let biUpTy? ← Meta.mkFreshExprMVar (.some (.sort biUpTyLvl?))
    -- `downFunc` is such that `downFunc binder↑` is equivalent to `binder`
    let (downFunc, biUpTy) ← Meta.withLocalDeclD `_ biUpTy? fun biUp => do
      -- To be safe, we call `instantiateMVars`
      let (biUpDown, biUpTy) ← cstULiftNeg u biUp (← instantiateMVars biTy)
      biUpTy?.mvarId!.assign biUpTy
      let downFunc ← Meta.mkLambdaFVars #[biUp] biUpDown
      return (downFunc, biUpTy)
    Meta.withLocalDecl name binfo biUpTy fun biUp => do
      -- `eApp = e (downFunc biUp)`
      let biUpDown := Expr.headBeta (.app downFunc biUp)
      let eApp := Expr.app e biUpDown
      let eAppTy := Expr.instantiate1 body biUpDown
      -- `eAppTy` may contain `biUpTy?`, so we need `instantiateMVars`
      let (eAppUp, eAppUpTy) ← cstULiftPos u eApp (← instantiateMVars eAppTy)
      let eUp ← Meta.mkLambdaFVars #[biUp] eAppUp
      let eUpTy ← Meta.mkForallFVars #[biUp] eAppUpTy
      let eUpTy ← instantiateMVars eUpTy
      return (eUp, eUpTy)
  | ty => do
    -- We assume that `ty` is reduced and has metavariables instantiated,
    --   so the following types must be rigid:
    --   1. `.sort u`
    --   2. `.const ..`
    --   3. `.app fn arg`
    --   4. `.fvar id`
    --   5. `.mvar id`
    --
    -- The same holds for `cstULiftNeg`
    let sort ← instantiateMVars (← Meta.inferType ty)
    if !sort.isSort then
      throwError "Auto.ULift :: Expected sort"
    let lvl := sort.sortLevel!
    let eUpTy := mkApp (.const ``GLift [lvl, u]) ty
    let eUp := mkAppN (.const ``GLift.up [lvl, u]) #[ty, e]
    return (eUp, eUpTy)

  -- In the return type, the first `Expr` is `eUp↓`, and the second `Expr` is
  --   the type of `e↑`
  partial def cstULiftNeg (u : Level) (eUp : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "Auto.cstULift :: Loose bound variable"
  | .lam .. => throwError "Auto.cstULift :: Please β-reduce type before calling cstULift"
  | .letE .. => throwError "Auto.cstULift :: Please ζ-reduce type before calling cstULift"
  | .lit .. => throwError "Auto.cstULift :: Malformed type"
  | .proj .. => throwError "Auto.cstULift :: Please unfold projections in type before calling cstULift"
  | .mdata data ty' => cstULiftNeg u eUp ty'
  | .forallE name biTy body binfo => do
    -- `upFunc` is such that `upFunc binder` is equivalent to `binder↑`
    let (upFunc, biUpTy) ← Meta.withLocalDeclD `_ biTy fun bi => do
      -- To be safe, we call `instantiateMVars`
      let (biUp, biUpTy) ← cstULiftPos u bi (← instantiateMVars biTy)
      let upFunc ← Meta.mkLambdaFVars #[bi] biUp
      return (upFunc, biUpTy)
    -- `downFunc` is such that `downFunc binder↑` is equivalent to `binder`
    let downFunc ← Meta.withLocalDeclD `_ biUpTy fun biUp => do
      let (biUpDown, _) ← cstULiftNeg u biUp (← instantiateMVars biTy)
      Meta.mkLambdaFVars #[biUp] biUpDown
    let (e, eUpTyPre) ← Meta.withLocalDecl name binfo biTy fun bi => do
      -- `eUpApp = eUp (upFunc bi)`
      let biUp := Expr.headBeta (.app upFunc bi)
      let eUpApp := Expr.app eUp biUp
      let eAppTy := Expr.instantiate1 body bi
      -- To be safe, we call `instantiateMVars`
      let (eApp, eAppUpTy) ← cstULiftNeg u eUpApp (← instantiateMVars eAppTy)
      let e ← Meta.mkLambdaFVars #[bi] eApp
      let eUpTyPre ← Meta.mkForallFVars #[bi] eAppUpTy
      return (e, eUpTyPre)
    let eUpTy ← Meta.withLocalDecl name binfo biUpTy fun biUp => do
      let biUpDown := Expr.headBeta (.app downFunc biUp)
      let eAppUpTy ← Meta.instantiateForall eUpTyPre #[biUpDown]
      Meta.mkForallFVars #[biUp] eAppUpTy
    return (e, eUpTy)
  | ty => do
    let sort ← instantiateMVars (← Meta.inferType ty)
    if !sort.isSort then
      throwError "Auto.ULift :: Expected sort"
    let lvl := sort.sortLevel!
    let eUpTy := mkApp (.const ``GLift [lvl, u]) ty
    let eUpDown := mkAppN (.const ``GLift.down [lvl, u]) #[ty, eUp]
    return (eUpDown, eUpTy)

end

-- Postprocess expression `e` obtained from ULifting
def postProcessULift (e : Expr) : MetaM Expr := do
  let e ← Core.betaReduce e
  let red (e : Expr) : CoreM TransformStep := do
    match e with
    | .app (.app (.const ``GLift.up lvl₁) ty₁) (.app (.app (.const ``GLift.down lvl₂) ty₂) e') =>
      return .continue e'
    | _ => return .continue e
  liftM <| (Core.transform (pre := red) e : CoreM _)

section TestcstULift

  universe tmp

  private def ulift (e : Expr) : Elab.TermElabM Unit := do
    let ety ← Meta.inferType e
    let ety ← Core.betaReduce ety
    let (eup, eupTy) ← cstULiftPos (.param `tmp) e ety
    let eup ← postProcessULift eup
    logInfo eup
  
  set_option pp.universes true
  set_option pp.funBinderTypes true
  set_option pp.structureProjections false

  private def f₁ := fun (x : Nat) => x
  #getExprAndApply [f₁ | ulift]
  #check fun x => GLift.up.{1, tmp} (f₁ (GLift.down.{1, tmp} x))

  private def f₂ := fun (α : Prop) (x : α) => x
  set_option pp.proofs true in
  #getExprAndApply [f₂ | ulift]
  #check fun (α : GLift.{1, tmp} Prop) (x : GLift.{0, tmp} (GLift.down.{1, tmp} α)) =>
  GLift.up.{0, tmp} (f₂ (GLift.down.{1, tmp} α) (GLift.down.{0, tmp} x))

  private def f₃ := fun (α : Type) (x : α) => x
  set_option pp.proofs true in
  #getExprAndApply [f₃ | ulift]

  private axiom f₄ : ∀ (α : Type) (β : α → Type) (x : α), β x
  #getExprAndApply [f₄ | ulift]
  #check fun (α : GLift.{2, tmp} Type) (β : GLift.{1, tmp} (GLift.down.{2, tmp} α) → GLift.{2, tmp} Type)
    (x : GLift.{1, tmp} (GLift.down.{2, tmp} α)) =>
  GLift.up.{1, tmp}
    (f₄ (GLift.down.{2, tmp} α) (fun (a : GLift.down.{2, tmp} α) => GLift.down.{2, tmp} (β (GLift.up.{1, tmp} a)))
      (GLift.down.{1, tmp} x))

  private axiom f₅ : ((Nat → Nat) → Nat) → Nat
  #getExprAndApply [f₅ | ulift]
  #check fun (a : (GLift.{1, tmp} Nat → GLift.{1, tmp} Nat) → GLift.{1, tmp} Nat) =>
  GLift.up.{1, tmp}
    (Auto.ULift.f₅ fun (a_1 : Nat → Nat) =>
      GLift.down.{1, tmp} (a fun (a : GLift.{1, tmp} Nat) => GLift.up.{1, tmp} (a_1 (GLift.down.{1, tmp} a))))

  set_option pp.explicit true in
  #getExprAndApply[@Nat.rec | ulift]
  universe u_1
  #check fun {motive : GLift.{1, tmp} Nat → GLift.{u_1 + 1, tmp} (Sort u_1)}
    (zero : GLift.{u_1, tmp} (@GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat Nat.zero))))
    (succ :
      (n : GLift.{1, tmp} Nat) →
        GLift.{u_1, tmp}
            (@GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat (@GLift.down.{1, tmp} Nat n)))) →
          GLift.{u_1, tmp}
            (@GLift.down.{u_1 + 1, tmp} (Sort u_1)
              (motive (@GLift.up.{1, tmp} Nat (Nat.succ (@GLift.down.{1, tmp} Nat n))))))
    (t : GLift.{1, tmp} Nat) =>
  @GLift.up.{u_1, tmp}
    (@GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat (@GLift.down.{1, tmp} Nat t))))
    (@Nat.rec.{u_1} (fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t)))
      (@GLift.down.{u_1, tmp} (@GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat Nat.zero))) zero)
      (fun (n : Nat) (n_ih : @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat n))) =>
        @GLift.down.{u_1, tmp} (@GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat (Nat.succ n))))
          (succ (@GLift.up.{1, tmp} Nat n)
            (@GLift.up.{u_1, tmp} (@GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat n))) n_ih)))
      (@GLift.down.{1, tmp} Nat t))

  private axiom f₆ : ∀ (α : Nat → Type) (β : ∀ (f : Nat → Nat), α (f 0)), Nat
  #getExprAndApply [f₆ | ulift]
  #check fun (α : GLift.{1, tmp} Nat → GLift.{2, tmp} Type)
    (β :
      (f : GLift.{1, tmp} Nat → GLift.{1, tmp} Nat) →
        GLift.{1, tmp} (GLift.down.{2, tmp} (α (f (GLift.up.{1, tmp} 0))))) =>
  GLift.up.{1, tmp}
    (Auto.ULift.f₆ (fun (a : Nat) => GLift.down.{2, tmp} (α (GLift.up.{1, tmp} a))) fun (f : Nat → Nat) =>
      GLift.down.{1, tmp} (β fun (a : GLift.{1, tmp} Nat) => GLift.up.{1, tmp} (f (GLift.down.{1, tmp} a))))

end TestcstULift


-- Auxiliary declaration for an example below
private axiom A_Constant : ∀ (α : Type) (β : α) (x : α) (y : Nat), α

noncomputable def A_Constant.Lift.{u} := fun
  (α : GLift.{2, u + 1} Type) (β : GLift (α.down)) (x : GLift (α.down)) (y : GLift Nat) =>
  A_Constant α.down β.down x.down y.down

-- Now, we want to implement a function `exprULift` which lifts an expressions
--   `e` to `e↑`, such that all the constants occurring in `e↑` are [lifted 
--   counterparts of constants in `e`]. To do this, the function requires that
--   all the constants in `e` has already had their lifted counterparts calculated.
-- Before we implement this function, let's first look at what we'll obtain
--   when we lift the following `example₁` (It's definitionally equal to
--   `A_Constant`, but we were applying const-lift to `A_Constant`. Now that
--   `A_Constant` is const-lifted, we'll apply expr-lift to `example₁`)
private noncomputable def example₁ :=
  fun (α : Type) (β : α) (x : α) (y : Nat) => A_Constant α β x y
-- What we'll get is
noncomputable def example₁.Lift.{u} := fun
  (α : GLift.{2, u + 1} Type) (β : GLift (α.down)) (x : GLift (α.down)) (y : GLift Nat) =>
    A_Constant.Lift α β x y
-- We observe a dicrepency here: While binder `(y : Nat)` is lifted to `(y : GLift Nat)`,
--   the binder `(β : α)` is lifted to `(β : GLift (α.down))`. In fact,
--   this discrepency can be resolved by viewing `GLift Nat` as `GLift (GLift.up Nat).down`
-- Now, it's easy to see that to Ulift an expression `e`, we only need to proceed by
--   these three steps:
--   (1) Replace all the atomic expressions (constants/fvars/mvars/sorts/nat lits/string lits)
--       in `e` with their lifted counterparts to obtain `e₁`
--   (2) For all binder `(x : ty)` occuring in `e₁`, replace it with `(x : GLift ty.down)`
--
-- Finally, we describe the procedure `withLiftedExprs` for lifting all user supplied facts.
--   (1) Keep a map which maps atomic expressions to their lifted couonterpart's `fvarId`.
--       The lifted-counterparts are stored as `let`-declarations in the local context
--   (2) Sequentially process the facts supplied by the user
--       Suppose we're processing a fact `p : typ`, we proceed in three steps
--       (i)  Collect all the atomic expressions that `p` depends on
--         Note: `p` depends on a constant `c` iff either `c` occurs in `p`, or
--         `c` occurs in the type of `p`, or an atomic expression occurring
--         in `c` depends on `p`
--       (ii) For all the unprocessed ones in the collected atomic expressions,
--         process them. **Note that the same constant with different universe levels are**
--         **considered different**
--       (iii).(1) If `p` is not a let-declaration,
--          (*) Call `cstULift` on `p` to obtain `(p↑, typ↑)`. **Discard `typ↑`**
--          (*) **Call `exprULift` on `typ`** to obtain `typ↑*`. Note that
--            `typ↑*` is definitionally equal to `typ↑`
--          (*) Introduce a let binder `let fvarp↑ : typ↑* := p↑` into the local context
--       (iii).(2) If `p` is a let-declaration `let p : ty := body`,
--          (*) Call `exprULift` on `ty` to obtain `ty↑`
--          (*) Call `exprULift` on `body` to obtain `body↑`
--          (*) Introduce a let binder `let fvarp↑ : ty↑ := body↑` into the local context

-- **Keep in mind that** If `e : ty`, then expected typing relation is `e↑ : GLift (ty↑).down`

-- Maps atomic expressions described above to their lifted counterpart
structure State where
  -- Maps constant name `c` to an array of (level, fvarId)
  --   such that `fvarId` is the lifted counterpart of `.const c level`
  constMap : HashMap Name (Array (List Level × FVarId))
  -- Maps fvars and mvars to their lifted counterpart
  varMap : HashMap Expr FVarId

abbrev ExprULiftM := StateRefT State MetaM
#genMonadState ExprULiftM

def insertLifted (e : Expr) (eUp : FVarId) : ExprULiftM Unit :=
  match e with
  | .const name lvls => do
    let constMap ← getConstMap
    let arr :=
      (match constMap.find? name with
       | .some arr => arr
       | none => #[])
    let constMap := constMap.insert name (arr.push (lvls, eUp))
    setConstMap constMap
  | .fvar _ => do
    let varMap ← getVarMap
    setVarMap (varMap.insert e eUp)
  | .mvar _ => do
    let varMap ← getVarMap
    setVarMap (varMap.insert e eUp)
  | _ => throwError "insertLifted :: Unexpected expression {e}"

def getLifted? (e : Expr) : ExprULiftM (Option FVarId) :=
  match e with
  | .const name lvls => do
    let constMap ← getConstMap
    let some arrs := constMap.find? name
      | return none
    for (lvls', fvarId) in arrs do
      if ← (lvls'.zip lvls).allM (fun (lvl', lvl) => Meta.isLevelDefEq lvl' lvl) then
        return fvarId
    return none
  | .fvar _ => do
    let varMap ← getVarMap
    return varMap.find? e
  | .mvar _ => do
    let varMap ← getVarMap
    return varMap.find? e
  | _ => throwError "getLifted? :: Unexpected expression {e}"

partial def exprULift (u : Level) : (e : Expr) → ExprULiftM Expr
| .bvar _ => throwError "exprULift :: Loose bound variable"
| .app fn arg => do
  let fnUp ← exprULift u fn
  let argUp ← exprULift u arg
  return .app fnUp argUp
| .lam name biTy body binfo => do
  let biTyUp ← exprULift u biTy
  let biTyUpTy ← instantiateMVars (← Meta.inferType biTyUp)
  let Expr.app (.const ``GLift _) (.sort v) := biTyUpTy
    | throwError "exprULift :: Unexpected error"
  let biUpTy := Expr.app (.const ``LiftTyConv [v, u]) biTyUp
  Meta.withLocalDecl name binfo biUpTy fun biUp => do
    -- This `body'` would not be type correct, but we
    --   do this anyway.
    let body' := Expr.instantiate1 body biUp
    -- Now `bodyUp` is type correct
    let bodyUp ← exprULift u body'
    Meta.mkLambdaFVars #[biUp] bodyUp
| .forallE name biTy body binfo => do
  let biTyUp ← exprULift u biTy
  let biTyUpTy ← instantiateMVars (← Meta.inferType biTyUp)
  let Expr.app (.const ``GLift _) (.sort v) := biTyUpTy
    | throwError "exprULift :: Unexpected error"
  let biUpTy := Expr.app (.const ``LiftTyConv [v, u]) biTyUp
  let (forallToFunc, w) ← Meta.withLocalDecl name binfo biUpTy fun biUp => do
    -- This `body'` would not be type correct, but we
    --   do this anyway.
    let body' := Expr.instantiate1 body biUp
    -- Now `bodyUp` is type correct
    let bodyUp ← exprULift u body'
    let bodyUpTy ← instantiateMVars (← Meta.inferType bodyUp)
    let Expr.app (.const ``GLift _) (.sort w) := bodyUpTy
      | throwError "exprULift :: Unexpected error"
    let forallToFunc ← Meta.mkLambdaFVars #[biUp] bodyUp
    return (forallToFunc, w)
  let biTy := Expr.app (.const ``GLift.down [.succ v, u]) biTyUp
  return mkAppN (.const ``ForallLift [v, u, w]) #[biTy, forallToFunc]
| .letE .. => throwError "exprULift :: Not implemented"
| e => do
  let some eUp ← getLifted? e
    | throwError "exprULift :: Cannot find lifted counterpart of {e}"
  return .fvar eUp

end Auto.ULift