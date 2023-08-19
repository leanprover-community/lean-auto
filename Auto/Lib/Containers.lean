import Lean
open Lean

namespace Auto

def mergeHashSet {α : Type u} [BEq α] [Hashable α] (a1 a2 : HashSet α) :=
  if a1.size < a2.size then
    a2.insertMany a1.toArray
  else
    a1.insertMany a2.toArray

def mergeArray (a1 a2 : Array α) :=
  if a1.size < a2.size then
    a2 ++ a1
  else
    a1 ++ a2

-- Effectively a map from `α` to arbitrary type
class Container {α : Type u} (C : Type v → Type w) where
  get?   : ∀ {β}, C β → α → Option β
  insert : ∀ {β}, C β → α → β → C β
  insertCorrect₁ : ∀ (c : C β) (k : α) (v : β), get? (insert c k v) k = .some val
  insertCorrect₂ : ∀ (c : C β) (k₁ k₂ : α) (v : β), k₁ ≠ k₂ → get? (insert c k₁ v) k₂ = get? c k₂

end Auto