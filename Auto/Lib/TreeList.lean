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
  | fe {m : Nat} : CBTreeList α m .f → CBTreeList α 0 .e → CBTreeList α m .p
  | pe {m : Nat} : CBTreeList α m .p → CBTreeList α 0 .e → CBTreeList α m .p
  | ee : CBTreeList α 0 .e → CBTreeList α 0 .e → CBTreeList α 0 .e
  deriving Repr

namespace CBTreeList

theorem empty_iff_zero {α : Type u} {n : Nat} {s : CBStatus} (t : CBTreeList α n s) : s = .e ↔ n = 0 := by
  induction t <;> simp_all

def fjoin {α : Type u} {m n : Nat} {s : CBStatus} (l : CBTreeList α m .f) (r : CBTreeList α n s) : (s' : CBStatus) × CBTreeList α (m + n) s' :=
  match s with
  | .f => ⟨.f, .ff l r⟩
  | .p => ⟨.p, .fp l r⟩
  | .e =>
    match r with
    | .e => ⟨.p, .fe l .e⟩
    | .ee rl rr => ⟨.p, .fe l (.ee rl rr)⟩

def joine {α : Type u} {m : Nat} {s : CBStatus} (l : CBTreeList α m s) (r : CBTreeList α 0 .e) : (s' : CBStatus) × CBTreeList α m s' :=
  match s with
  | .f => ⟨.p, .fe l r⟩
  | .p => ⟨.p, .pe l r⟩
  | .e =>
    match l with
    | .e => ⟨.e, .ee .e r⟩
    | .ee ll lr => ⟨.e, .ee (.ee ll lr) r⟩

def clear {α : Type u} {n : Nat} (s : CBStatus) : CBTreeList α n s → CBTreeList α 0 .e
| .f _ => .e
| .e => .e
| .ff l r => .ee (clear _ l) (clear _ r)
| .fp l r => .ee (clear _ l) (clear _ r)
| .fe l r => .ee (clear _ l) (clear _ r)
| .pe l r => .ee (clear _ l) r
| .ee l r => .ee l r

def pushEmpty {α : Type u} {n : Nat} : CBTreeList α n .e → (x : α) → (s' : CBStatus) × CBTreeList α 1 s'
| .e, x => ⟨.f, .f x⟩
| .ee l r, x =>
  match pushEmpty l x with
  | ⟨s', o⟩ => joine o r

def push {α : Type u} {n : Nat} {s : CBStatus} : CBTreeList α n s → (x : α) → (s' : CBStatus) × CBTreeList α (n + 1) s'
| .f l, x => ⟨.f, .ff (.f l) (.f x)⟩
| .e, x => ⟨.f, .f x⟩
| .ff l r, x => CBTreeList.fjoin (.ff l r) (pushEmpty (clear .f (.ff l r)) x).snd
| .fp l r, x => Nat.add_assoc _ _ _ ▸ CBTreeList.fjoin l (push r x).snd
| .fe l r, x => CBTreeList.fjoin l (push r x).snd
| .pe l r, x => joine (push l x).snd r
| .ee l r, x => joine (pushEmpty l x).snd r

end CBTreeList

def TreeList (α : Type u) := (n : Nat) × (s : CBStatus) × CBTreeList α n s

namespace TreeList

def push {α : Type u} : TreeList α → α → TreeList α
| ⟨n, _, t⟩, x =>
  match CBTreeList.push t x with
  | ⟨s', o⟩ => ⟨n + 1, s', o⟩

end TreeList

end Auto
