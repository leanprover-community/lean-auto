/-
Reasoning with Bool.
-/
import Auto.Tactic

example : ∀ b1 b2, (b1 && b2) = false ↔ (b1 = false ∨ b2 = false) := by
  auto [Bool.and_eq_true, Bool.eq_false_iff]
example : ∀ b1 b2, (b1 && b2) = true ↔ (b1 = true ∧ b2 = true) := by
  auto [Bool.and_eq_true]
example : ∀ b1 b2, (b1 || b2) = false ↔ (b1 = false ∧ b2 = false) := by
  sorry
example : ∀ b1 b2, (b1 || b2) = true ↔ (b1 = true ∨ b2 = true) := by
  auto [Bool.or_eq_true]
example : ∀ b, (!b) = true ↔ b = false := by
  -- Typeclass problem
  have em : ∀ (b : Bool), b = true ∨ b = false := sorry
  auto [em] u[not, cond.match_1] d[Bool.rec]
example : ∀ b, !b = false ↔ b = true := sorry
example : ∀ b c, b = c ↔ ¬ (b = !c) := sorry
example : ∀ b1 b2, b1 = b2 ↔ (b1 = true ↔ b2 = true) := sorry
