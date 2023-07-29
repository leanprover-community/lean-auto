-- Processing Universe Levels
import Lean
import Auto.Translation.Lift
import Auto.Util.ExprExtra
open Lean

namespace Auto

-- For an `e`, we denote its lifting as `t↑`. For the following
--   discussion, we assume that we want to lift everything to
--   universe level `u`.
-- `ULiftPos u e ty`:
--   Given a type `ty` an expression `e : ty`, return
--   (1) `e↑`
--   (2) The type of `e↑`, i.e. `ty×`
-- `ULiftNeg u e↑ ty`:
--   Given a type `ty` and an expression `e↑` where `e↑ : ty×`, return
--   (1) `(e↑)↓`
--   (2) The type of `e↑`, i.e. `ty×`.
--   Note that the type of `e↑` is unknown when we call `ULiftNeg`
--   because there will be a free variable of unknown type acting
--   as a hole inside `e↑`. This also explains why we need to
--   return `ty×`.
-- Note that `ULift` proceeds by structural recursion on
--   `ty`, not on `e`.
-- **Make sure that** expressions should be β-reduced before being
--   sent to `ULiftPos` or `ULiftNeg`

mutual

  -- In the return type, the first `Expr` is `e↑`, and the second `Expr` is
  --   the type of `e↑`
  partial def ULiftPos (u : Level) (e : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "Auto.ULift :: Loose bound variable"
  | .mvar mid => throwError "Auto.ULift :: Not implemented"
  | .lam .. => throwError "Auto.ULift :: Malformed type"
  | .letE .. => throwError "Auto.ULift :: Malformed type"
  | .lit .. => throwError "Auto.ULift :: Malformed type"
  | .mdata data ty' => ULiftPos u e ty'
  | .forallE name biTy body binfo => do
    -- We want to reate a free variable (intended) of type `bity↑`.
    --   However, we still don't what's `bity↑`, so we first
    --   create a metavariable representing `bity↑`
    let biUpTyLvl? ← Meta.mkFreshLevelMVar
    let biUpTy? ← Meta.mkFreshExprMVar (.some (.sort biUpTyLvl?))
    -- `downFunc` is such that `downFunc binder↑` is equivalent to `binder`
    let (downFunc, biUpTy) ← Meta.withLocalDeclD `_ biUpTy? fun biUp => do
      -- To be safe, we call `instantiateMVars`
      let (biUpDown, biUpTy) ← ULiftNeg u biUp (← instantiateMVars biTy)
      biUpTy?.mvarId!.assign biUpTy
      let downFunc ← Meta.mkLambdaFVars #[biUp] biUpDown
      return (downFunc, biUpTy)
    Meta.withLocalDecl name binfo biUpTy fun biUp => do
      -- `eApp = e (downFunc biUp)`
      let biUpDown := Expr.headBeta (.app downFunc biUp)
      let eApp := Expr.app e biUpDown
      let eAppTy := Expr.instantiate1 body biUpDown
      -- `eAppTy` may contain `biUpTy?`, so we need `instantiateMVars`
      let (eAppUp, eAppUpTy) ← ULiftPos u eApp (← instantiateMVars eAppTy)
      let eUp ← Meta.mkLambdaFVars #[biUp] eAppUp
      let eUpTy ← Meta.mkForallFVars #[biUp] eAppUpTy
      let eUpTy ← instantiateMVars eUpTy
      return (eUp, eUpTy)
  | ty => do
    -- We assume that `e` is reduced, so the following types must be rigid:
    --   1. `.sort u`
    --   2. `.const ..`
    --   3. `.app fn arg`
    --   4. `.fvar id`
    --
    -- The same holds for `ULiftNeg`
    let sort ← instantiateMVars (← Meta.inferType ty)
    if !sort.isSort then
      throwError "Auto.ULift :: Expected sort"
    let lvl := sort.sortLevel!
    let eUpTy := mkApp (.const ``GLift [lvl, u]) ty
    let eUp := mkAppN (.const ``GLift.up [lvl, u]) #[ty, e]
    return (eUp, eUpTy)

  -- In the return type, the first `Expr` is `eUp↓`, and the second `Expr` is
  --   the type of `e↑`
  partial def ULiftNeg (u : Level) (eUp : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "Auto.ULift :: Loose bound variable"
  | .mvar mid => throwError "Auto.ULift :: Not implemented"
  | .lam .. => throwError "Auto.ULift :: Malformed type"
  | .letE .. => throwError "Auto.ULift :: Malformed type"
  | .lit .. => throwError "Auto.ULift :: Malformed type"
  | .mdata data ty' => ULiftNeg u eUp ty'
  | .forallE name biTy body binfo => do
    -- `upFunc` is such that `upFunc binder` is equivalent to `binder↑`
    let (upFunc, biUpTy) ← Meta.withLocalDeclD `_ biTy fun bi => do
      -- To be safe, we call `instantiateMVars`
      let (biUp, biUpTy) ← ULiftPos u bi (← instantiateMVars biTy)
      let upFunc ← Meta.mkLambdaFVars #[bi] biUp
      return (upFunc, biUpTy)
    -- `downFunc` is such that `downFunc binder↑` is equivalent to `binder`
    let downFunc ← Meta.withLocalDeclD `_ biUpTy fun biUp => do
      let (biUpDown, _) ← ULiftNeg u biUp (← instantiateMVars biTy)
      Meta.mkLambdaFVars #[biUp] biUpDown
    let (e, eUpTyPre) ← Meta.withLocalDecl name binfo biTy fun bi => do
      -- `eUpApp = eUp (upFunc bi)`
      let biUp := Expr.headBeta (.app upFunc bi)
      let eUpApp := Expr.app eUp biUp
      let eAppTy := Expr.instantiate1 body bi
      -- To be safe, we call `instantiateMVars`
      let (eApp, eAppUpTy) ← ULiftNeg u eUpApp (← instantiateMVars eAppTy)
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

section Test

  universe tmp

  private def ulift (e : Expr) : Elab.TermElabM Unit := do
    let ety ← Meta.inferType e
    let (eup, eupTy) ← ULiftPos (.param `tmp) e ety
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
    (Auto.f₅ fun (a_1 : Nat → Nat) =>
      GLift.down.{1, tmp} (a fun (a : GLift.{1, tmp} Nat) => GLift.up.{1, tmp} (a_1 (GLift.down.{1, tmp} a))))

  set_option pp.explicit true in
  #getExprAndApply[@Nat.rec | ulift]
  universe u_1
  #check fun {motive : GLift.{1, tmp} Nat → GLift.{u_1 + 1, tmp} (Sort u_1)}
    (zero :
      GLift.{u_1, tmp}
        ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t))) Nat.zero))
    (succ :
      (n : GLift.{1, tmp} Nat) →
        GLift.{u_1, tmp}
            ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t)))
              (@GLift.down.{1, tmp} Nat n)) →
          GLift.{u_1, tmp}
            ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t)))
              (Nat.succ (@GLift.down.{1, tmp} Nat n))))
    (t : GLift.{1, tmp} Nat) =>
  @GLift.up.{u_1, tmp}
    ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t)))
      (@GLift.down.{1, tmp} Nat t))
    (@Nat.rec.{u_1} (fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t)))
      (@GLift.down.{u_1, tmp}
        ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t))) Nat.zero) zero)
      (fun (n : Nat) (n_ih : @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat n))) =>
        @GLift.down.{u_1, tmp}
          ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t))) (Nat.succ n))
          (succ (@GLift.up.{1, tmp} Nat n)
            (@GLift.up.{u_1, tmp}
              ((fun (t : Nat) => @GLift.down.{u_1 + 1, tmp} (Sort u_1) (motive (@GLift.up.{1, tmp} Nat t))) n) n_ih)))
      (@GLift.down.{1, tmp} Nat t))

  private axiom f₆ : ∀ (α : Nat → Type) (β : ∀ (f : Nat → Nat), α (f 0)), Nat
  #getExprAndApply [f₆ | ulift]
  #check fun (α : GLift.{1, tmp} Nat → GLift.{2, tmp} Type)
    (β :
      (f : GLift.{1, tmp} Nat → GLift.{1, tmp} Nat) →
        GLift.{1, tmp}
          ((fun (a : Nat) => GLift.down.{2, tmp} (α (GLift.up.{1, tmp} a)))
            ((fun (a : Nat) => GLift.down.{1, tmp} (f (GLift.up.{1, tmp} a))) 0))) =>
  GLift.up.{1, tmp}
    (Auto.f₆ (fun (a : Nat) => GLift.down.{2, tmp} (α (GLift.up.{1, tmp} a))) fun (f : Nat → Nat) =>
      GLift.down.{1, tmp} (β fun (a : GLift.{1, tmp} Nat) => GLift.up.{1, tmp} (f (GLift.down.{1, tmp} a))))
  #reduce (α : GLift.{1, tmp} Nat → GLift.{2, tmp} Type) →
  ((f : GLift.{1, tmp} Nat → GLift.{1, tmp} Nat) →
      GLift.{1, tmp}
        ((fun (a : Nat) => GLift.down.{2, tmp} (α (GLift.up.{1, tmp} a)))
          ((fun (a : Nat) => GLift.down.{1, tmp} (f (GLift.up.{1, tmp} a))) 0))) →
    GLift.{1, tmp} Nat

end Test

end Auto