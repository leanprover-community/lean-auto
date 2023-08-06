import Auto.Util.SigEq
namespace Auto.Embedding

@[reducible] def pushLCtx (lctx : Nat → α) (x : α) : Nat → α
| 0     => x
| n + 1 => lctx n

def pushLCtx.comm (f : α → β) (lctx : Nat → α) (x : α) :
  (n : Nat) → f (pushLCtx lctx x n) = pushLCtx (fun n => f (lctx n)) (f x) n
| 0       => rfl
| .succ _ => rfl

theorem pushLCtx.commFn (f : α → β) (lctx : Nat → α) (x : α) :
  (fun n => f (pushLCtx lctx x n)) = (fun n => pushLCtx (fun n => f (lctx n)) (f x) n) :=
  funext (pushLCtx.comm f lctx x)

@[reducible] def pushLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : ∀ n, lctxty (pushLCtx rty xty n)
| 0     => x
| n + 1 => lctx n

def pushLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n))
  {xty : α} (x : lctxty xty) : (n : Nat) →
  f _ (pushLCtxDep lctx x n) = pushLCtxDep (lctxty:=β) (fun n => f _ (lctx n)) (f xty x) n
| 0 => rfl
| _ + 1  => rfl

def pushLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
  (n : Nat) → HEq
    (@pushLCtxDep _ rty lctxty lctx _ x n)
    (@pushLCtxDep _ (lctxty ∘ rty) id lctx _ x n)
| 0 => HEq.refl _
| _ + 1 => HEq.refl _

theorem pushLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@pushLCtxDep _ rty lctxty lctx _ x) (@pushLCtxDep _ (lctxty ∘ rty) id lctx _ x) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (pushLCtxDep.absorbAux _ _)) (pushLCtx.commFn _ _ _)

def pushLCtxAt (lctx : Nat → α) (x : α) : (pos : Nat) → Nat → α
| 0 => pushLCtx lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAt (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAt.comm (f : α → β) (lctx : Nat → α) (x : α) :
  (pos : Nat) → (n : Nat) → f (pushLCtxAt lctx x pos n) = pushLCtxAt (f ∘ lctx) (f x) pos n
| 0 => fun n => by
  dsimp [pushLCtxAt]; apply pushLCtx.comm
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => pushLCtxAt.comm f (fun n => lctx (Nat.succ n)) x pos' n'

theorem pushLCtxAt.commFn (lctx : Nat → α) (f : α → β) (x : α) (pos : Nat) :
  (fun n => f (pushLCtxAt lctx x pos n)) = (fun n => pushLCtxAt (fun n => f (lctx n)) (f x) pos n) :=
  funext (pushLCtxAt.comm f lctx x pos)

-- Surprisingly, this is definitionally equal
def pushLCtx_pushLCtxAt (lctx : Nat → α) (x y : α) (pos : Nat) :
  pushLCtx (pushLCtxAt lctx x pos) y = pushLCtxAt (pushLCtx lctx y) x (Nat.succ pos)
  := rfl

def pushLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : (pos : Nat) → (n : Nat) → lctxty (pushLCtxAt rty xty pos n)
| 0 => pushLCtxDep lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAtDep (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAtDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n))
  {xty : α} (x : lctxty xty) : (pos : Nat) → (n : Nat) →
    f _ (pushLCtxAtDep lctx x pos n) = pushLCtxAtDep (lctxty:=β) (fun n => f _ (lctx n)) (f xty x) pos n
| 0 => fun _ => pushLCtxDep.comm _ _ _ _
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => pushLCtxAtDep.comm f (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAtDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
  (pos : Nat) → (n : Nat) → HEq
    (@pushLCtxAtDep _ rty lctxty lctx _ x pos n)
    (@pushLCtxAtDep _ (lctxty ∘ rty) id lctx _ x pos n)
| 0 => fun _ => pushLCtxDep.absorbAux _ _ _
| pos' + 1 => fun n =>
  match n with
  | 0 => HEq.refl _
  | n' + 1 => pushLCtxAtDep.absorbAux (fun n => lctx (.succ n)) x pos' n'

theorem pushLCtxAtDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (pos : Nat) :
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@pushLCtxAtDep _ rty lctxty lctx _ x pos) (@pushLCtxAtDep _ (lctxty ∘ rty) id lctx _ x pos) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (pushLCtxAtDep.absorbAux _ _ _)) (pushLCtxAt.commFn _ _ _ _)

-- Surprisingly, this is definitionally equal
def pushLCtxDep_pushLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) {yty : α} (y : lctxty yty) (pos : Nat) :
  pushLCtxDep (pushLCtxAtDep lctx x pos) y = pushLCtxAtDep (pushLCtxDep lctx y) x (Nat.succ pos) := rfl

def popLCtx (lctx : Nat → α) := fun n => lctx (n + 1)

def popLCtx.comm (f : α → β) (lctx : Nat → α) :
  (n : Nat) → f (popLCtx lctx n) = popLCtx (f ∘ lctx) n := fun _ => rfl

def popLCtx.commFn (f : α → β) (lctx : Nat → α) :
  (fun n => f (popLCtx lctx n)) = (fun n => popLCtx (f ∘ lctx) n) := rfl

def popLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) : ∀ n, lctxty (popLCtx rty n) :=
  fun n => lctx (n + 1)

def popLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
  f _ (popLCtxDep lctx n) = popLCtxDep (lctxty:=β) (fun n => f _ (lctx n)) n := rfl

def popLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) (n : Nat) : HEq
    (@popLCtxDep _ rty lctxty lctx n)
    (@popLCtxDep _ (lctxty ∘ rty) id lctx n) := HEq.refl _

theorem popLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) :
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@popLCtxDep _ rty lctxty lctx) (@popLCtxDep _ (lctxty ∘ rty) id lctx) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (popLCtxDep.absorbAux _)) (popLCtx.commFn _ _)

def popLCtxAt (lctx : Nat → α) (pos : Nat) := 
  match pos with
  | 0 => popLCtx lctx
  | pos' + 1 => fun n =>
    match n with
    | 0 => lctx 0
    | n' + 1 => popLCtxAt (fun n => lctx (Nat.succ n)) pos' n'

def popLCtxAt.comm (lctx : Nat → α) (f : α → β) (pos : Nat) :
  (n : Nat) → f (popLCtxAt lctx pos n) = popLCtxAt (f ∘ lctx) pos n :=
  match pos with
  | 0 => fun _ => rfl
  | pos' + 1 => fun n =>
    match n with
    | 0 => rfl
    | n' + 1 => popLCtxAt.comm (fun n => lctx (.succ n)) f pos' n'

def popLCtxAt.commFn (lctx : Nat → α) (f : α → β) (pos : Nat) :
  (fun n => f (popLCtxAt lctx pos n)) = (fun n => popLCtxAt (f ∘ lctx) pos n) :=
  funext (popLCtxAt.comm lctx f pos)

def popLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) : (pos : Nat) → (n : Nat) → lctxty (popLCtxAt rty pos n)
| 0 => popLCtxDep lctx
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => popLCtxAtDep (fun n => lctx (Nat.succ n)) pos' n'

def popLCtxAtDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) : (pos : Nat) → (n : Nat) → HEq
    (@popLCtxAtDep _ rty lctxty lctx pos n)
    (@popLCtxAtDep _ (lctxty ∘ rty) id lctx pos n)
| 0 => fun _ => HEq.refl _
| pos' + 1 => fun n =>
  match n with
  | 0 => HEq.refl _
  | n' + 1 => popLCtxAtDep.absorbAux (fun n => lctx (.succ n)) pos' n'

def popLCtxAtDep.absorbAux' {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) (pos : Nat) (n : Nat) : HEq
    (@popLCtxAtDep _ rty lctxty lctx pos n)
    (@popLCtxAtDep _ id (lctxty ∘ rty) lctx pos n) :=
  HEq.trans
    (b := @popLCtxAtDep _ (lctxty ∘ rty) id lctx pos n)
    (popLCtxAtDep.absorbAux lctx pos n)
    (HEq.symm (@popLCtxAtDep.absorbAux _ id (lctxty ∘ rty) lctx pos n))

def popLCtxAtDep.absorb {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) (pos : Nat):
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@popLCtxAtDep _ rty lctxty lctx pos) (@popLCtxAtDep _ (lctxty ∘ rty) id lctx pos) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (popLCtxAtDep.absorbAux _ _)) (popLCtxAt.commFn _ _ _)

def popLCtxAtDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n)) :
  (pos : Nat) → (n : Nat) → f _ (popLCtxAtDep lctx pos n) = popLCtxAtDep (lctxty:=β) (fun n => f _ (lctx n)) pos n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popLCtxAtDep.comm f (fun n => lctx (Nat.succ n)) pos' n'

def popLCtxAt.commDep
  {β : α → Sort u} (lctx : Nat → α) (f : ∀ (x : α), β x) :
  (pos n : Nat) → f (popLCtxAt lctx pos n) = popLCtxAtDep (fun n => f (lctx n)) pos n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popLCtxAt.commDep (fun n => lctx (.succ n)) f pos' n'
 
-- #reduce fun lctx => popLCtxAt lctx 3 4

def popLCtxs (lctx : Nat → α) : (i : Nat) → Nat → α
| 0 => lctx
| i' + 1 => popLCtx (popLCtxs lctx i')

-- Definitional equality :
-- #check fun lctx x => (Eq.refl _ : popLCtx (pushLCtx lctx x) = lctx)
-- #check fun lctx pops => (Eq.refl _ : popLCtx (popLCtxs lctx pops) = popLCtxs lctx (Nat.succ pops))

-- #reduce fun lctx x => popLCtx (pushLCtx lctx x)
--   popLCtxs lctx 0 = lctx
-- #reduce fun lctx => popLCtxs lctx 0
-- #reduce fun lctx x => pushLCtxAt lctx x (pos:=2) 4
-- #reduce (fun lctx x y t => (Eq.refl _ :
--   pushLCtx (pushLCtxAt lctx x t) y = pushLCtxAt (pushLCtx lctx y) x (t + 1)))

def push_pop_eq (lctx : Nat → α) :
  pushLCtx (popLCtx lctx) (lctx 0) = lctx := by
  apply funext
  intro n; cases n <;> rfl

def popAt_pushAt_eq (lctx : Nat → α) (x : α) :
  (pos : Nat) → (n : Nat) → popLCtxAt (pushLCtxAt lctx x pos) pos n = lctx n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popAt_pushAt_eq (fun n => lctx (Nat.succ n)) x pos' n'

def popAtDep_pushAtDep_eq
  {α : Sort w} {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : (pos n : Nat) →
  HEq (@popLCtxAtDep _ (pushLCtxAt rty xty pos) lctxty
        (@pushLCtxAtDep _ rty lctxty lctx xty x pos) pos n
      )
      (lctx n)
| 0 => fun _ => HEq.rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => HEq.rfl
  | n' + 1 => @popAtDep_pushAtDep_eq _ _ lctxty (fun n => lctx (Nat.succ n)) _ x pos' n'

end Auto.Embedding