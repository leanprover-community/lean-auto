/-
Reasoning with Bool.
-/
import Auto.Tactic

example : ∀ b1 b2, (b1 && b2) = false ↔ (b1 = false ∨ b2 = false) := by auto
example : ∀ b1 b2, (b1 && b2) = true ↔ (b1 = true ∧ b2 = true) := by auto
example : ∀ b1 b2, (b1 || b2) = false ↔ (b1 = false ∧ b2 = false) := by auto
example : ∀ b1 b2, (b1 || b2) = true ↔ (b1 = true ∨ b2 = true) := by auto
example : ∀ b, (!b) = true ↔ b = false := by auto
example : ∀ b, !(b = true) ↔ b = false := by auto
example : ∀ b, (!b) = false ↔ b = true := by auto
example : ∀ b, !(b = false) ↔ b = true := by auto
example : ∀ b c, b = c ↔ ¬ (b = !c) := by auto
example : ∀ b1 b2, b1 = b2 ↔ (b1 = true ↔ b2 = true) := by auto
