import Auto.Tactic

-- Collecting `logical constructors`

set_option trace.auto.printLemmas true

example : True := by
  try auto [True.intro];
  exact .intro

example : True := by
  try auto [Or.inl, Or.inr];
  sorry

example (a b : Prop)
        (h₁ : a ∨ b) (h₂ : a ∧ b) : True := by
  try auto [];
  sorry

example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  try auto [];
  sorry