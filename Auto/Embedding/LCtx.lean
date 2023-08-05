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

def pushLCtx.comm_cast₁ (f : α → β) (lctx : Nat → α) (g : β → Sort w) (x : α) :
  (n : Nat) → (H : g (f (pushLCtx lctx x n))) → g (pushLCtx (fun n => f (lctx n)) (f x) n)
| 0       => fun H => H
| .succ _ => fun H => H

def pushLCtx.comm_cast₂ (f : α → β) (lctx : Nat → α) (g : β → Sort w) (x : α) :
  (n : Nat) → (H : g (pushLCtx (fun n => f (lctx n)) (f x) n)) → g (f (pushLCtx lctx x n))
| 0       => fun H => H
| .succ _ => fun H => H

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

def popLCtx (lctx : Nat → α) := fun n => lctx (n + 1)

def popLCtxAt (lctx : Nat → α) (pos : Nat) :=
  match pos with
  | 0 => popLCtx lctx
  | pos' + 1 => fun n =>
    match n with
    | 0 => lctx 0
    | n' + 1 => popLCtxAt (fun n => lctx (Nat.succ n)) pos' n'

def popLCtxAt.comm_cast₁ (lctx : Nat → α) (f : α → β) (g : β → Sort w) (pos : Nat) :
  (n : Nat) → (H : g (f (popLCtxAt lctx pos n))) → g (popLCtxAt (fun n => f (lctx n)) pos n) :=
  match pos with
  | 0 => fun _ H => H
  | pos' + 1 => fun n =>
    match n with
    | 0 => fun H => H
    | n' + 1 => fun H => popLCtxAt.comm_cast₁ _ _ _ pos' n' H

def popLCtxAt.comm_cast₂ (lctx : Nat → α) (f : α → β) (g : β → Sort w) (pos : Nat) :
  (n : Nat) → (H : g (popLCtxAt (fun n => f (lctx n)) pos n)) → g (f (popLCtxAt lctx pos n)) :=
  match pos with
  | 0 => fun _ H => H
  | pos' + 1 => fun n =>
    match n with
    | 0 => fun H => H
    | n' + 1 => fun H => popLCtxAt.comm_cast₂ _ _ _ pos' n' H

def popAt_pushAt_eq (lctx : Nat → α) (x : α) :
  (pos : Nat) → (n : Nat) → popLCtxAt (pushLCtxAt lctx x pos) pos n = lctx n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popAt_pushAt_eq (fun n => lctx (Nat.succ n)) x pos' n'

def popAt_pushAt_eqFn (lctx : Nat → α) (x : α) (pos : Nat) :
  popLCtxAt (pushLCtxAt lctx x pos) pos = lctx :=
  funext (fun n => popAt_pushAt_eq lctx x pos n)

-- #reduce fun lctx => popLCtxAt lctx 3 4

def popLCtxs (lctx : Nat → α) : (i : Nat) → Nat → α
| 0 => lctx
| i' + 1 => popLCtx (popLCtxs lctx i')

def popLCtx.succ_cast₁ (lctx : Nat → α) (f : (Nat → α) → Sort u) (i : Nat)
  (H : f (popLCtxs (popLCtx lctx) i)) : f (popLCtxs lctx (Nat.succ i)) :=
  match i with
  | 0 => H
  | i' + 1 => popLCtx.succ_cast₁ lctx (fun lctx => f (popLCtx lctx)) i' H

def popLCtx.succ_cast₂ (lctx : Nat → α) (f : (Nat → α) → Sort u) (i : Nat)
  (H : f (popLCtxs lctx (Nat.succ i))) : f (popLCtxs (popLCtx lctx) i) :=
  match i with
  | 0 => H
  | i' + 1 => popLCtx.succ_cast₂ lctx (fun lctx => f (popLCtx lctx)) i' H

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

end Auto.Embedding