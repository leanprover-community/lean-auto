import Auto.Tactic

set_option trace.auto.lamReif.printResult true in
example (p q : α → Prop) (h₁ : ∃ f, p f) (h₂ : ∀ f, p f → q f) : ∃ f, q f :=
  by auto [*]

set_option trace.auto.lamReif.printResult true in
example (α : Prop) (h₁ : α) (h₂ : α) : α := by auto