@[reducible] def pushLCtx (lctx : Nat → α) (x : α) : Nat → α
| 0     => x
| n + 1 => lctx n

@[reducible] def pushLCtxDep {f : Nat → Sort u} (lctx : ∀ n, f n) (x : α) : ∀ n, (pushLCtx f α n)
| 0     => x
| n + 1 => lctx n

def pushLCtxAt (lctx : Nat → α) (x : α) : (pos : Nat) → Nat → α
| 0 => pushLCtx lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAt (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAt_eqpos_cast₁ (lctx : Nat → α) (x : α) (pos : Nat) (f : α → Sort v)
  (H : f (pushLCtxAt lctx x pos pos)) : f x :=
  match pos with
  | 0 => H
  | pos' + 1 => pushLCtxAt_eqpos_cast₁ _ x pos' f H

def pushLCtxAt_eqpos_cast₂ (lctx : Nat → α) (x : α) (pos : Nat) (f : α → Sort v)
  (H : f x) : f (pushLCtxAt lctx x pos pos) :=
  match pos with
  | 0 => H
  | pos' + 1 => pushLCtxAt_eqpos_cast₂ _ x pos' f H

def popLCtx (lctx : Nat → α) := fun n => lctx (n + 1)

def popLCtxs (lctx : Nat → α) (i : Nat) := fun n => lctx (Nat.add n i)

-- Definitional equality :
--   popLCtx (pushLCtx lctx x) = lctx x
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