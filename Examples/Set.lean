/-
Some set theoretic identities. These can all be solved by unfolding definitions
and then using first-order logic.

These are adapted from Mathematics in Lean. The relevant definitions are in the #check commands.
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Lattice

open Set

variable {α β : Type _}

section
variable (s t u : Set α)

#check subset_def
#check mem_inter_iff
#check mem_union
#check Set.ext

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  sorry

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  sorry

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

#check mem_diff

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

example : s ∩ t = t ∩ s := by
  sorry

example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

#check mem_setOf

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  sorry

#check mem_empty_iff_false
#check mem_univ

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  sorry

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry

end

section
variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  sorry

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end

end

section
variable {α I : Type _}
variable (A B : I → Set α)
variable (s : Set α)

open Set

#check mem_iUnion
#check mem_iInter

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  sorry

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  sorry

#check Nat.exists_prime_and_dvd

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  sorry

#check Nat.exists_infinite_primes

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section
open Set

variable {α : Type _} (s : Set (Set α))

#check mem_iUnion₂
#check mem_iInter₂

example : ⋃₀ s = ⋃ t ∈ s, t := by
  sorry

example : ⋂₀ s = ⋂ t ∈ s, t := by
  sorry

end

