import Auto.Tactic
import Mathlib.Tactic

-- Collecting `logical constructors`

set_option trace.auto.printLemmas true

example : True := by
  try auto [True.intro]

example : True := by
  try auto [Or.inl, Or.inr]

example (a b : Prop)
        (h₁ : a ∨ b) (h₂ : a ∧ b) : True := by
  auto []

example (a b : Prop)
        (h₁ : a) (h₂ : a → b) : b := by
  try auto 👍
  auto [*]

example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by auto

example
  (h₁ : a ∨ b ∨ c)
  (h₂ : ¬ a ∨ ¬ d ∨ e)
  (h₄ : ¬ a ∨ b ∨ ¬ c)
  (h₅ : a ∨ b ∨ ¬ c)
  (h₆ : ¬ b ∨ c ∨ ¬ d)
  (h₇ : a ∨ ¬c ∨ ¬ d)
  (h₈ : d)
  : e := by auto