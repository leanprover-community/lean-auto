import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Real.Basic

open Set

#check subset_def
#check mem_Icc
#check mem_Ico

example (a b c d : ℝ) (h1 : a < b) : Icc a b ⊆ Ico c d ↔ c ≤ a ∧ b < d := by
  sorry

variable {α : Type _} [LinearOrder α]

example (a b c d : α) (h1 : a < b) : Icc a b ⊆ Ico c d ↔ c ≤ a ∧ b < d := by
  sorry
