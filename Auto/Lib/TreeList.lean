import Lean
import Auto.MathlibEmulator
import Auto.Lib.BoolExtra
import Auto.Lib.NatExtra
import Auto.Lib.OptionExtra
import Auto.Lib.Containers
import Auto.Lib.Pos
import Auto.Lib.Bin
-- Make sure that `Lean.toExpr Nat` is overriden
import Auto.Lib.ToExprExtra

/-
  Polymorphic complete binary tree
  For definitions with `'`, the tree behaves as `{n : Nat // n ≠ 0} → α`
  For definitions without `'`, the tree behaves as `Nat → α`
-/

namespace Auto

inductive CBStatus
  | f -- full
  | p -- partially full
  | e -- empty

inductive CBTreeList (α : Type u) : Nat → CBStatus → Type u
  | f : α → CBTreeList α 1 .f
  | e : CBTreeList α 0 .e
  | ff {m n : Nat} : CBTreeList α m .f → CBTreeList α n .f → CBTreeList α (m + n) .f
  | fp {m n : Nat} : CBTreeList α m .f → CBTreeList α n .p → CBTreeList α (m + n) .p
  | fe {m n : Nat} : CBTreeList α m .f → CBTreeList α n .e → CBTreeList α (m + n) .p
  | pe {m n : Nat} : CBTreeList α m .p → CBTreeList α n .e → CBTreeList α (m + n) .p
  | ee {m n : Nat} : CBTreeList α m .e → CBTreeList α n .e → CBTreeList α (m + n) .e

namespace CBTreeList

theorem CBTreeList.empty_only_if_zero {α : Type u} {n : Nat} (t : CBTreeList α n .e) : n = 0 := by
  revert t; generalize h : CBStatus.e = s; intro t
  induction t <;> try contradiction
  case e => rfl
  case ee hl hr => rw [hl h, hr h]

def CBTreeList.fjoin {α : Type u} {m n : Nat} {s : CBStatus} (l : CBTreeList α m .f) (r : CBTreeList α n s) : (s' : CBStatus) × CBTreeList α (m + n) s' :=
  match s with
  | .f => ⟨.f, .ff l r⟩
  | .p => ⟨.p, .fp l r⟩
  | .e => ⟨.p, .fe l r⟩

def CBTreeList.clear {α : Type u} {n : Nat} (s : CBStatus) : CBTreeList α n s → CBTreeList α 0 .e
| .f _ => .e
| .e => .e
| .ff l r => .ee (clear _ l) (clear _ r)
| .fp l r => .ee (clear _ l) (clear _ r)
| .fe l r => .ee (clear _ l) (clear _ r)
| .pe l r => .ee (clear _ l) (CBTreeList.empty_only_if_zero r ▸ r)
| .ee l r => .ee (CBTreeList.empty_only_if_zero l ▸ l) (CBTreeList.empty_only_if_zero r ▸ r)

def CBTreeList.push {α : Type u} {n : Nat} {s : CBStatus} : CBTreeList α n s → (x : α) → (s' : CBStatus) × CBTreeList α (n + 1) s'
| .f l, x => ⟨.f, .ff (.f l) (.f x)⟩
| .e, x => ⟨.f, .f x⟩
| .ff l r, x => sorry
| .fp l r, x => sorry
| .fe l r, x => sorry
| .pe l r, x => sorry
| .ee l r, x => sorry

end CBTreeList

def TreeList (α : Type u) := (n : Nat) × (s : CBStatus) × CBTreeList α n s

end Auto
