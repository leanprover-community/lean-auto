namespace Auto.Translation

@[reducible] def pushLCtx (lctx : Nat → α) (x : α) : Nat → α
| 0     => x
| n + 1 => lctx n

@[reducible] def pushLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : ∀ n, lctxty (pushLCtx rty xty n)
| 0     => x
| n + 1 => lctx n

def pushLCtxAt (lctx : Nat → α) (x : α) : (pos : Nat) → Nat → α
| 0 => pushLCtx lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAt (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : (pos : Nat) → (n : Nat) → lctxty (pushLCtxAt rty xty pos n)
| 0 => pushLCtxDep lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAtDep (fun n => lctx (Nat.succ n)) x pos' n'

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

theorem pushLCtx.comm (f : α → β) (lctx : Nat → α) (x : α) :
  (fun n => f (pushLCtx lctx x n)) = pushLCtx (fun n => f (lctx n)) (f x) := by
  apply funext; intro n; cases n <;> simp

end Auto.Translation