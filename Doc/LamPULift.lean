import Lean
import Auto.Embedding.Lift
import Auto.Translation.ReifM
import Auto.Lib.ExprExtra
import Auto.Lib.MonadUtils
open Lean
open Auto.Embedding

initialize
  registerTraceClass `auto.lamPULift

/-
  ULift for system `λP`, i.e. supports `types depending on terms`
    and `terms depending on terms`. This file is merely here to
    show what universe lifting means in the most general case.
  (1) For functions `f` used in user-provided facts, call
      `cstULift` to obtain a lifted version of `f` where
      all the arguments are lifted versions of the original
      argument
  (2) For user-provided fact `proof : ty`, we **assume**
      that all the `∀` has been turned into free variables,
      where the free variable corresponds to a monomorphized
      instance of the polymorphic `forallF` function, or a
      universe-level-instantiated instance of the `ImpF` function.
      We call `termULift` on `ty` to obtain an expression
      `ty'` that is definitionally equal to `GLift.up ty`,
      and that `ty'` only contains lifted counterparts of
      the original constants in `ty`

  Note that `types/terms depending on types` are not fully supported
  For example, if we have const/fvar `f : ∀ (α : Type), α → Prop`
    and `h : Nat → Nat`, then calling `termLift` on `f (Nat → Nat) h`
    would fail. This is because
  (1) `h` will be lifted to `hLift : GLift Nat → GLift Nat`, so
      The lifted version of `f (Nat → Nat)` must have type
      `(GLift Nat → GLift Nat) → GLift Prop`
  (2) However, `cstULift f` has type `∀ (α : GLift Type), α → GLift Prop`.
      We can't actually instantiate `α := GLift Nat → GLift Nat` because
      the type of `GLift Nat → GLift Nat` is not `GLift Type`.
-/

namespace Auto.LamPULift

/-
  For an expression `e`, we denote its lifted version as `e↑`. For the
    following discussion, we assume that we want to lift everything
    to universe level `u`.
  `cstULiftPos u e ty`:
    Given a type `ty` an expression `e : ty`, return
    (1) `e↑`
    (2) The type of `e↑`, i.e. `ty×`
  `cstULiftNeg u e↑ ty`:
    Given a type `ty` and an expression `e↑` where `e↑ : ty×`, return
    (1) `(e↑)↓`
    (2) The type of `e↑`, i.e. `ty×`.
    Note that the type of `e↑` is unknown when we call `cstULiftNeg`
    because there will be a free variable of unknown type acting
    as a hole inside `e↑`. This also explains why we need to
    return `ty×`.
  Note that `ULift` proceeds by structural recursion on
    `ty`, not on `e`.

  **Usage:** `cstULift` can be used to calculate ULift-ed version
    of expressions. However, un-lifted constants and free variables
    may still occur in the `ty×` returned by `cstULift`. So we'll
    have to use another function `termULift`, which will be described
    below
  Suppose we have a constant/free variable `A`. To calculate the
    ULift-ed version of `A` (denoted as `A↑`),
    (1) Compute the type of `A` (denoted as `ty`), instantiate
        metavariables in `ty` and β-reduce & ζ-reduce it to obtain `ty*`.
    (2) Let `u` be the universe level you want to lift to.
        Call `let A↑ ← cstULiftPos u A ty` to obtain the ULift-ed
        version of `A`
-/

mutual
  -- In the return type, the first `Expr` is `e↑`, and the second `Expr` is
  --   the type of `e↑`
  partial def cstULiftPos (u : Level) (e : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "{decl_name%} :: Loose bound variable"
  | .lam .. => throwError "{decl_name%} :: Please β-reduce type before calling cstULift"
  | .letE .. => throwError "{decl_name%} :: Please ζ-reduce type before calling cstULift"
  | .lit .. => throwError "{decl_name%} :: Malformed type"
  | .proj .. => throwError "{decl_name%} :: Please unfold projections in type before calling cstULift"
  | .forallE name biTy body binfo => do
    -- We want to reate a free variable (intended) of type `bity↑`.
    --   However, we still don't what's `bity↑`, so we first
    --   create a metavariable representing `bity↑`, and assign
    --   it after calling `cstULiftNeg`
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
      throwError "{decl_name%} :: Expected sort"
    let lvl := sort.sortLevel!
    let eUpTy := mkApp (.const ``GLift [lvl, u]) ty
    let eUp := mkAppN (.const ``GLift.up [lvl, u]) #[ty, e]
    return (eUp, eUpTy)

  /-- In the return type, the first `Expr` is `eUp↓`, and the second `Expr` is the type of `e↑` -/
  partial def cstULiftNeg (u : Level) (eUp : Expr) : (ty : Expr) → MetaM (Expr × Expr)
  | .bvar idx => throwError "{decl_name%} :: Loose bound variable"
  | .lam .. => throwError "{decl_name%} :: Please β-reduce type before calling cstULift"
  | .letE .. => throwError "{decl_name%} :: Please ζ-reduce type before calling cstULift"
  | .lit .. => throwError "{decl_name%} :: Malformed type"
  | .proj .. => throwError "{decl_name%} :: Please unfold projections in type before calling cstULift"
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
      throwError "{decl_name%} :: Expected sort"
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
    (Auto.LamPULift.f₅ fun (a_1 : Nat → Nat) =>
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
    (Auto.LamPULift.f₆ (fun (a : Nat) => GLift.down.{2, tmp} (α (GLift.up.{1, tmp} a))) fun (f : Nat → Nat) =>
      GLift.down.{1, tmp} (β fun (a : GLift.{1, tmp} Nat) => GLift.up.{1, tmp} (f (GLift.down.{1, tmp} a))))

end TestcstULift


/-- Auxiliary declaration for an example below -/
private axiom A_Constant : ∀ (α : Type) (β : α) (x : α) (y : Nat), α

noncomputable def A_Constant.Lift.{u} := fun
  (α : GLift.{2, u + 1} Type) (β : GLift (α.down)) (x : GLift (α.down)) (y : GLift Nat) =>
  A_Constant α.down β.down x.down y.down

/-
  Now, we want to implement a function `termULift` which lifts an expressions
    `e` to `GLift.up e`, such that all the constants occurring in `e↑` are [lifted
    counterparts of constants in `e`]. To do this, the function requires that
    all the constants in `e` has already had their lifted counterparts calculated.
  Before we implement this function, let's first look at what we'll obtain
    when we lift the following `example₁` (It's definitionally equal to
    `A_Constant`, but we were applying const-lift to `A_Constant`. Now that
    `A_Constant` is const-lifted, we'll apply expr-lift to `example₁`)
-/

private noncomputable def example₁ :=
  fun (α : Type) (β : α) (x : α) (y : Nat) => A_Constant α β x y
-- What we'll get is
noncomputable def example₁.Lift.{u} := fun
  (α : GLift.{2, u + 1} Type) (β : GLift (α.down)) (x : GLift (α.down)) (y : GLift Nat) =>
    A_Constant.Lift α β x y
/-
  We observe a dicrepency here: While binder `(y : Nat)` is lifted to `(y : GLift Nat)`,
    the binder `(β : α)` is lifted to `(β : GLift (α.down))`. In fact,
    this discrepency can be resolved by viewing `GLift Nat` as `GLift (GLift.up Nat).down`
  Now, it's easy to see that to Ulift an expression `e`, we only need to proceed by
    these three steps:
    (1) Replace all the atomic expressions (constants/fvars/mvars/sorts/nat lits/string lits)
        in `e` with their lifted counterparts to obtain `e₁`
    (2) For all binder `(x : ty)` occuring in `e₁`, replace it with `(x : GLift ty.down)`

  Now, we describe the procedure `withULiftedFact` that processes a user-provided fact `proof : ty`
    (1) Collect all atomic expressions that depends on `proof`. Call `withProcessedAtomic` on all of
        them
    (2) **Call `termULift` on `ty`. Since `ty` is always rigid, we obtain an**
        **expression `gLiftTy` definitionally equal to (GLift.up ty)**
    (3) Note that `ty` is definitionally equal to `GLift.down gLiftTy`, and
        `p : typ` is already within the local context. So, we don't need to
        introduce any binders
  We call `withULiftedFact` on each user-provided fact to process all user-provided facts.

  The procedure `withProcessedAtomic` works as follows:
    (1) We keep a map which maps atomic expressions to their lifted couonterpart's `fvarId`.
        The lifted-counterparts are stored as `let`-declarations in the local context
    (2) Suppose we're processing an atomic expression `p : typ`, we proceed in three steps
        (i)  Collect all the atomic expressions that `p` depends on
          Note: `p` depends on an atomic expression `c` iff either `c` occurs in `p`, or
            the type of a (constant/fvar/mvar/lit) occurring in `p` depends on `c` (this is
            a recursive definition)
        (ii) For all the unprocessed ones in the collected atomic expressions,
          process them. **Note that the same constant with different universe levels are**
          **considered different**
        (iii) If `p : typ` is not a user-provided fact, then `p` is intended to be used
          as a function in some user-provided fact. In this case, we
           (*) Call `typeULift` on `typ` to obtain `typ↑`
           (*) If `p` is a let-declaration, call `termULift` on the body of the
               let decaration to obtain `body↑`. Otherwise, call `cstULift` on `p` to
               obtain `body↑`
           (*) Introduce a let binder `let fvarp↑ : ty↑ := body↑` into the local context
-/

end Auto.LamPULift
