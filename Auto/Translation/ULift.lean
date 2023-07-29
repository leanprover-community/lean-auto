-- Processing Universe Levels
import Lean
import Auto.Translation.Lift
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
-- **It's advised that** expressions should be β-reduced before being
--   sent to `ULiftPos` or `ULiftNeg`

mutual

  -- In the return type, the first `Expr` is `e↑`, and the second `Expr` is
  --   the type of `e↑`
  partial def ULiftPos (u : Level) (e : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "Auto.ULift :: Loose bound variable"
  | .fvar fid => return (e, .fvar fid) -- **TODO**
  | .mvar mid => throwError "Auto.ULift :: Not implemented"
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
    -- We assume that `e` is reduced, so the following types must be rigid
    --   1. `.sort u`
    --   2. `.const ..`
    --   3. `.app fn arg`
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
  | .fvar fid => return (eUp, .fvar fid) -- **TODO**
  | .mvar mid => throwError "Auto.ULift :: Not implemented"
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
    let eUpDown := mkAppN (.const ``GLift.down [lvl, u]) #[sort, eUp]
    let eUpTy := mkApp (.const ``GLift [lvl, u]) ty
    return (eUpDown, eUpTy)

end

end Auto