import Lean
import Auto.Embedding.Lift
import Auto.Translation.ReifM
import Auto.Util.ExprExtra
import Auto.Util.MonadUtils
open Lean
open Auto.Embedding

/-
  ULift for simply typed lambda calculus
  (1) For functions `f` used in user-provided facts, call
      `cstULift` to obtain a lifted version of `f` where
      all the arguments are lifted versions of the original
      argument
  (2) For user-provided fact `proof : ty`, we **assume**
      that all the `∀` has been turned into free variables,
      where the free variable corresponds to a monomorphized
      instance of the polymorphic `forallF` function.
      We call `termULift` on `ty` to obtain an expression
      `ty'` that is definitionally equal to `GLift.up ty`,
     but only contains lifted counterparts of the original
     constants in `ty`
-/

namespace Auto.LamULift

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
  | .bvar idx => throwError "Auto.cstULift :: Loose bound variable"
  | .lam .. => throwError "Auto.cstULift :: Please β-reduce type before calling cstULift"
  | .letE .. => throwError "Auto.cstULift :: Please ζ-reduce type before calling cstULift"
  | .lit .. => throwError "Auto.cstULift :: Malformed type"
  | .proj .. => throwError "Auto.cstULift :: Please unfold projections in type before calling cstULift"
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
    (Auto.LamULift.f₅ fun (a_1 : Nat → Nat) =>
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
    (Auto.LamULift.f₆ (fun (a : Nat) => GLift.down.{2, tmp} (α (GLift.up.{1, tmp} a))) fun (f : Nat → Nat) =>
      GLift.down.{1, tmp} (β fun (a : GLift.{1, tmp} Nat) => GLift.up.{1, tmp} (f (GLift.down.{1, tmp} a))))

end TestcstULift


-- Auxiliary declaration for an example below
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
            the type of a (constant/fvar/mvar) occurring in `p` depends on `c` (this is a
            recursive definition)
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

structure Context where
  -- Records the local context introduced when traversing an expression
  --   during `termULift` and `typeULift`.
  -- For example, suppose we call `termULift` on `λ x y. g`, then
  --   `boundFVars` should have `x -> 0, y -> 1` when we're inspecting `g`.
  -- The de-bruijn indice corresponding to a free variable `fvar` can be
  --   calculated by `boundFVars.size - 1 - boundFVars.get! fvar`
  -- Note that we don't need to calculate de-bruijin indices during
  --   `termULift`, but we'll need that during reification.
  boundFVars : HashMap FVarId Nat := HashMap.empty

-- Maps atomic expressions described above to their lifted counterpart
structure State where
  -- Maps constant name `c` to an array of (level, fvarId)
  --   such that `fvarId` is the lifted counterpart of `.const c level`
  constMap : HashMap Name (Array (List Level × FVarId)) := HashMap.empty
  -- Maps fvars and mvars to their lifted counterpart
  varMap : HashMap Expr FVarId                          := HashMap.empty
  -- Maps *lifted* [interpreted constants] into their un-lifted counterparts
  liftedInterped : HashMap FVarId FVarId                := HashMap.empty
  -- The universe level that all constants lift to. This is computed at
  --   the beginning of `withULiftedFacts`
  u : Level                                             := Level.zero

abbrev ULiftM := ReaderT Context <| StateRefT State Reif.ReifM

@[inline] def ULiftM.run (x : ULiftM α) (ctx : Context := {}) (s : State) :=
  x ctx |>.run s

@[inline] def ULiftM.run' (x : ULiftM α) (ctx : Context := {}) (s : State) :=
  Prod.fst <$> (x ctx |>.run s)

#genMonadState ULiftM
#genMonadContext ULiftM

@[inline] def mapULiftM [MonadControlT ULiftM m] [Monad m] (f : ∀ {α}, ULiftM α → ULiftM α) {α} (x : m α) : m α :=
  controlAt ULiftM fun runInBase => f <| runInBase x

@[inline] def map1ULiftM [MonadControlT ULiftM m] [Monad m] (f : forall {α}, (β → ULiftM α) → ULiftM α) {α} (k : β → m α) : m α :=
  controlAt ULiftM fun runInBase => f fun b => runInBase <| k b

@[inline] def map2ULiftM [MonadControlT ULiftM m] [Monad m] (f : forall {α}, (β → γ → ULiftM α) → ULiftM α) {α} (k : β → γ → m α) : m α :=
  controlAt ULiftM fun runInBase => f fun b c => runInBase <| k b c

def pushLifted (e : Expr) (eUp : FVarId) : ULiftM Unit :=
  match e with
  | .const name lvls => do
    let constMap ← getConstMap
    let arr :=
      (match constMap.find? name with
       | .some arr => arr
       | none => #[])
    let constMap := constMap.insert name (arr.push (lvls, eUp))
    setConstMap constMap
  | .fvar id => do
    let varMap ← getVarMap
    setVarMap (varMap.insert e eUp)
    -- If `e` is also an interpreted logical constant, add it to `liftedInterped`
    let iL ← Reif.getInterpreted
    if iL.contains id then
      let liftedInterped ← getLiftedInterped
      setLiftedInterped (liftedInterped.insert eUp id)
  | .mvar _ => do
    let varMap ← getVarMap
    setVarMap (varMap.insert e eUp)
  | .lit _ => do
    let varMap ← getVarMap
    setVarMap (varMap.insert e eUp)
  | .sort _ => do
    let varMap ← getVarMap
    setVarMap (varMap.insert e eUp)
  | _ => throwError "insertLifted :: Unexpected expression {e}"

def getLifted? (e : Expr) : ULiftM (Option FVarId) :=
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
  | .lit _ => do
    let varMap ← getVarMap
    return varMap.find? e
  | .sort _ => do
    let varMap ← getVarMap
    return varMap.find? e
  | _ => throwError "getLifted? :: Unexpected expression {e}"

private def withBoundFVarImp (id : FVarId) (k : ULiftM α) : ULiftM α :=
  withReader (fun ctx => ⟨ctx.boundFVars.insert id (ctx.boundFVars.size)⟩) k

def withBoundFVar [Monad n] [MonadControlT ULiftM n] (id : FVarId) (k : n α) :=
  mapULiftM (withBoundFVarImp id) k

private def withLocalDeclAsBoundFVarImp (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → ULiftM α) : ULiftM α :=
  Meta.withLocalDecl name bi type fun fvar =>
    LamULift.withBoundFVar fvar.fvarId! <| k fvar

def withLocalDeclAsBoundFVar
  [Monad n] [MonadControlT ULiftM n]
  (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → n α) :=
  map1ULiftM (withLocalDeclAsBoundFVarImp name bi type) k

def deBruijn! (id : FVarId) : ULiftM Nat := do
  let boundFVars ← getBoundFVars
  match boundFVars.find? id with
  | .some n => return boundFVars.size - 1 - n
  | .none   => throwError "deBruijn! :: Unknown bound fvar {Expr.fvar id}"

mutual

  -- Turn `e` into an expression `e'` definitionally equal
  --   to `GLift.up e` such that `e'` only contains
  --   lifted counterparts of constants
  partial def termULift : (e : Expr) → ULiftM Expr
  | .bvar _ => throwError "termULift :: Loose bound variable"
  | .mdata data e' => return .mdata data (← termULift e')
  | .app fn arg => do
    let fnUp ← termULift fn
    let argUp ← termULift arg
    return .app fnUp argUp
  | .lam name biTy body binfo => do
    let biTyUp ← typeULift biTy
    let biTyUpTy ← instantiateMVars (← Meta.inferType biTyUp)
    withLocalDeclAsBoundFVar (n:=ULiftM) name binfo biTyUpTy fun biUp => do
      -- This `body'` would not be type correct, but we
      --   do this anyway.
      let body' := Expr.instantiate1 body biUp
      -- Now `bodyUp` is type correct
      let bodyUp ← termULift body'
      Meta.mkLambdaFVars #[biUp] bodyUp
  | .forallE .. =>
    throwError ("∀ should have been turned into" ++
        " free variables representing `forallF` or `impF` during monomorphization")
  | .letE .. => throwError "termULift :: Not implemented"
  | .fvar id => do
    let varMap ← getVarMap
    match varMap.find? (.fvar id) with
    -- A free variable in the lctx where the orignal expression lives in
    | .some id' => return (.fvar id')
    | none =>
      let boundFVars ← getBoundFVars
      match boundFVars.find? id with
      -- A binder inside the original expression
      | .some _ => return (.fvar id)
      | none => throwError "termULift :: Unexpected error"
  | e => do
    let some eUp ← getLifted? e
      | throwError "termULift :: Cannot find lifted counterpart of {e}"
    return .fvar eUp

  -- If an expression `e : ty`, then `cstULift e : typeULift ty`
  partial def typeULift : (e : Expr) → ULiftM Expr
  | .mdata data e' => return .mdata data (← typeULift e')
  | .lam .. => throwError "typeULift :: Unexpected error"
  | .forallE name biTy body binfo => do
    let biUpTy ← typeULift biTy
    withLocalDeclAsBoundFVar (n:=ULiftM) name binfo biUpTy fun biUp => do
      -- This `body'` would not be type correct, but we
      --   do this anyway.
      let body' := Expr.instantiate1 body biUp
      -- Now `bodyUp` is type correct
      let bodyUp ← termULift body'
      Meta.mkForallFVars #[biUp] bodyUp
  | e => do
    let eUp ← termULift e
    let eUpTy ← Meta.inferType eUp
    let Expr.app (.const ``GLift _) (.sort v) := eUpTy
      | throwError "typeULift :: Unexpected error"
    let u ← getU
    return Expr.app (.const ``liftTyConv [v, u]) eUp

end

private def mergeArray (a1 a2 : Array α) :=
  if a1.size < a2.size then
    a2 ++ a1
  else
    a1 ++ a2

-- Runs in `MetaM`, but does not use `MetaM` facilities
def collectAtomic : (e : Expr) → ULiftM (Array Expr)
| .bvar _ => return #[]
| .app fn arg => do
  let fna ← collectAtomic fn
  let arga ← collectAtomic arg
  return mergeArray fna arga
| .lam _ ty body _ => do
  let tya ← collectAtomic ty
  let bodya ← collectAtomic body
  return mergeArray tya bodya
| .forallE _ ty body _ => do
  let tya ← collectAtomic ty
  let bodya ← collectAtomic body
  return mergeArray tya bodya
| .letE _ ty v body _ => do
  let tya ← collectAtomic ty
  let va ← collectAtomic v
  let bodya ← collectAtomic body
  return mergeArray (mergeArray tya va) bodya
| .mdata _ e => collectAtomic e
| .proj .. => throwError "collectAtomic :: Please unfold projections before calling me"
| e => return #[e]

private partial def withProcessedAtomicImp (e : Expr) (cont : ULiftM α) : ULiftM α := do
  -- If `e` is already processed, return
  if let .some _ ← getLifted? e then
    cont
  else
    let ea ← collectAtomic e
    -- `c` occurs in `e`
    let cont' := ea.foldl (β := ULiftM α) (fun cont' a => withProcessedAtomicImp a cont') (do
      let eTy ← Meta.inferType e
      let eTyUp ← typeULift eTy
      let (eUp, _) ← cstULiftPos (← getU) e eTy
      let freshId := (← mkFreshId).toString
      Meta.withLetDecl ("_lift_" ++ freshId) eTyUp eUp (fun newFVar => do
        pushLifted e newFVar.fvarId!
        Reif.pushFVar newFVar.fvarId!
        cont
      )
    )
    -- The type of some `const/fvar/mvar` in `e` depends on `c`
    ea.foldl (β := ULiftM α) (fun cont' a => do
      if let .fvar id := a then
        withProcessedAtomicImp (← id.getType) cont'
      else if a.isMVar ∨ a.isConst then
        withProcessedAtomicImp (← instantiateMVars (← Meta.inferType a)) cont'
      else
        cont') cont'

def withProcessedAtomic [Monad n] [MonadControlT ULiftM n] (e : Expr) (cont : n α) : n α :=
  mapULiftM (withProcessedAtomicImp e) cont

-- The first `Expr` is `proof` (of type `ty`), and the second
--   `Expr` is the lifted type, which is definitionally equal
--   to `GLift.up ty`
abbrev ULiftedFact := Expr × Expr

private def withULiftedFactsAux (fact : Reif.UMonoFact) {α : Type}
  (cont : Array ULiftedFact → ULiftM α) (arr : Array ULiftedFact) : ULiftM α := do
  let (proof, ty) := fact
  let tya ← collectAtomic ty
  tya.foldl (fun cont' a => withProcessedAtomicImp a cont') (do
    let gLiftTy ← termULift ty
    cont (arr.push (proof, gLiftTy))
  )

private def mergeHashSet {α : Type u} [BEq α] [Hashable α] (a1 a2 : HashSet α) :=
  if a1.size < a2.size then
    a2.insertMany a1.toArray
  else
    a1.insertMany a2.toArray

-- Note that we're not introducing binders into the local context.
partial def collectUniverseLevels : Expr → MetaM (HashSet Level)
| .bvar _ => return HashSet.empty
| e@(.fvar _) => do collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
| e@(.mvar _) => do collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
| .sort u => return HashSet.empty.insert u
| e@(.const _ us) => do
  let hus := HashSet.empty.insertMany us
  let tys ← collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
  return mergeHashSet hus tys
| .app fn arg => do
  let fns ← collectUniverseLevels fn
  let args ← collectUniverseLevels arg
  return mergeHashSet fns args
| .lam _ biTy body _ => do
  let tys ← collectUniverseLevels biTy
  let bodys ← collectUniverseLevels body
  return mergeHashSet tys bodys
| .forallE _ biTy body _ => do
  let tys ← collectUniverseLevels biTy
  let bodys ← collectUniverseLevels body
  return mergeHashSet tys bodys
| .letE _ ty v body _ => do
  let tys ← collectUniverseLevels ty
  let vs ← collectUniverseLevels v
  let bodys ← collectUniverseLevels body
  return mergeHashSet (mergeHashSet tys vs) bodys
| .lit _ => return HashSet.empty.insert (.succ .zero)
| .mdata _ e' => collectUniverseLevels e'
| .proj .. => throwError "Please unfold projections before collecting universe levels"

-- Note that the facts to be processed are stored in `ReifM.state`
private def withULiftedFactsImp (cont : Array ULiftedFact → ULiftM α) : ULiftM α := do
  let facts ← Reif.getFacts
  -- Collect universe levels
  let levels ← facts.foldlM (fun hs (proof, ty) => do
    let proofUs ← collectUniverseLevels proof
    let tyUs ← collectUniverseLevels ty
    return mergeHashSet (mergeHashSet proofUs tyUs) hs) HashSet.empty
  -- Compute the universe level that we need to lift to
  let level := Level.succ (levels.fold (fun l l' => Level.max l l') Level.zero)
  let normLevel := level.normalize
  setU normLevel
  -- Lift all facts to the required universe level
  let cont' := facts.foldl (β:= Array ULiftedFact → ULiftM α) (fun cont' fact => withULiftedFactsAux fact cont') cont
  cont' #[]

def withULiftedFacts [Monad n] [MonadControlT ULiftM n] (cont : Array ULiftedFact → n α) : n α :=
  map1ULiftM withULiftedFactsImp cont

end Auto.LamULift