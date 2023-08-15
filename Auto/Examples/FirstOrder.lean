/-
Problems in First Order Logic.
-/
import Mathlib.Data.Nat.Basic
import Auto.Tactic

-- From TPIL

section
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

set_option smt.solver.name "cvc5"

example : (∃ x : α, r) → r := by
  try auto;
  sorry
example (a : α) : r → (∃ x : α, r) := by
  try auto;
  sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  try auto;
  sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  try auto;
  sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  try auto;
  sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  try auto;
  sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  try auto;
  sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  try auto;
  sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  try auto;
  sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  try auto;
  sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  try auto;
  sorry

def p_ : Nat → Prop := fun x => False

example : (∃ x, r → p_ x) ↔ (r → ∃ x, p_ x) := by
  try auto;
  sorry

end

section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  try auto;
  sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  try auto;
  sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  try auto;
  sorry

end

section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example (_ : α) : ((∀ x : α, r) ↔ r) := by
  try auto;
  sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  try auto;
  sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  try auto;
  sorry

end

section
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  try auto;
  sorry

end

-- other examples

section
variable (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X)

example (H : ∀ x, P x → Q x) (H₁ : ∀ x, P x) : Q a := by
  try auto;
  sorry
example (H : ∀ x, P x → Q x) (H₁ : P a) : Q a := by
  try auto;
  sorry

example (H₁ : P a) (H₂ : P b) : ∃ x, P x := by
  try auto;
  sorry
example (H₁ : P a) (H₂ : P b) (H₃ : Q b) : ∃ x, P x ∧ Q x := by
  try auto;
  sorry
example (H₁ : P b) (H₂ : Q b) (H₃ : P a) : ∃ x, P x ∧ Q x := by
  try auto;
  sorry
example (H : ∀ x, P x → Q x ∧ R x) (a : X) (H₁ : P a) : R a ∧ Q a := by
  try auto;
  sorry
example (H : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by
  try auto;
  sorry

example (x : X) : ∃ x, ((∃ y, P y) → P x) := by
  try auto;
  sorry
example : (∃ x, ∀ y, T x y) → ∀ y, ∃ x, T x y := by
  try auto;
  sorry

end



