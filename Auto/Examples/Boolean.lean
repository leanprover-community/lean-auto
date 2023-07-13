/-
Reasoning with Bool.
-/

example : ∀ b1 b2, b1 && b2 = false ↔ (b1 = false ∨ b2 = false) := sorry
example : ∀ b1 b2, b1 && b2 = true ↔ (b1 = true ∧ b2 = true) := sorry
example : ∀ b1 b2, b1 || b2 = false ↔ (b1 = false ∧ b2 = false) := sorry
example : ∀ b1 b2, b1 || b2 = true ↔ (b1 = true ∨ b2 = true) := sorry
example : ∀ b, !b = true ↔ b = false := sorry
example : ∀ b, !b = false ↔ b = true := sorry
example : ∀ b c, b = c ↔ ¬ (b = !c) := sorry
example : ∀ b1 b2, b1 = b2 ↔ (b1 = true ↔ b2 = true) := sorry


