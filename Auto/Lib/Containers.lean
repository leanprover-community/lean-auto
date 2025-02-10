import Lean
open Lean

namespace Auto

def mergeHashSet {α : Type u} [BEq α] [Hashable α] (a1 a2 : Std.HashSet α) :=
  if a1.size < a2.size then
    a2.insertMany a1.toArray
  else
    a1.insertMany a2.toArray

def mergeArray (a1 a2 : Array α) :=
  if a1.size < a2.size then
    a2 ++ a1
  else
    a1 ++ a2

def tallyArrayHashable [Hashable α] [BEq α] (xs : Array α) : Array (α × Nat) := Id.run <| do
  let mut ret : Std.HashMap α Nat := Std.HashMap.empty
  for x in xs do
    match ret.get? x with
    | .some cnt => ret := ret.insert x (cnt + 1)
    | .none => ret := ret.insert x 1
  return ret.toArray

/-- Effectively a map from `α` to arbitrary type -/
class Container {α : Type u} (C : Type v → Type w) where
  get?   : ∀ {β}, C β → α → Option β
  insert : ∀ {β}, C β → α → β → C β
  insertCorrect₁ : ∀ (c : C β) (k : α) (v : β), get? (insert c k v) k = .some val
  insertCorrect₂ : ∀ (c : C β) (k₁ k₂ : α) (v : β), k₁ ≠ k₂ → get? (insert c k₁ v) k₂ = get? c k₂

end Auto
