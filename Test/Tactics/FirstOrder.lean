import Auto.Tactic

open Auto Embedding

set_option profiler true
set_option auto.optimizeCheckerProof false

set_option pp.universes true in
set_option trace.auto.lamReif true in
example : True := by
  auto [True.intro];

set_option pp.explicit true in
set_option trace.auto.buildChecker true in
example (a b : Prop) : a ∨ b ∨ ¬ a := by
  auto

set_option pp.explicit true in
example (a b : Nat) (f : Nat → Nat)
 (eqNat : Nat → Nat → Prop) (H : eqNat (f a) (f b)) : True := by
  auto [H]

set_option trace.auto.tactic true in
set_option trace.auto.buildChecker true in
set_option trace.auto.printLemmas true in
set_option trace.auto.lamReif true in
example {α β : Type} (a : α) (b : β) (H : b = b) : a = a := by
  auto [H]

set_option pp.raw true in
set_option trace.auto.buildChecker true in
set_option trace.auto.tactic true in
set_option trace.auto.lamReif true in
example (a : Nat) (f : Nat → Nat) (H : ∀ x, f x = x) :
  f x = f (f (f (f (f (f (f (f (f x)))))))) := by
  auto [H]

set_option trace.auto.buildChecker true in
example (x y : Nat) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ f₁₄ : Nat → Nat → Nat)
  (H : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈,
    f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)) =
    f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁₂ (f₁₃ x₄ x₃) (f₁₄ x₂ x₁))) :
  True := by
  auto [H]

-- This example is not supposed to work because it contains
--   dependent type
-- example (β : Prop) (a : β → β) (H : ∃ x, x = a) : a = a := by
--   auto [H];
--   sorry

-- Multiple formulas
set_option trace.auto.buildChecker true in
example
  (f₁ f₂ f₃ g₁ g₂ g₃ : Nat → Nat → Nat)
  (H₁ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₂ x₁ x₂) (f₃ x₃ x₄) = g₁ (g₂ x₁ x₂) (g₃ x₃ x₄))
  (H₂ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₃ x₁ x₂) (f₂ x₃ x₄) = g₁ (g₂ x₁ x₂) (g₃ x₃ x₄))
  (H₃ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₁ x₁ x₂) (f₃ x₃ x₄) = g₁ (g₂ x₁ x₂) (g₃ x₃ x₄))
  (H₄ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₃ x₁ x₂) (f₁ x₃ x₄) = g₁ (g₂ x₁ x₂) (g₃ x₃ x₄))
  (H₅ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₁ x₁ x₂) (f₂ x₃ x₄) = g₁ (g₂ x₁ x₂) (g₃ x₃ x₄))
  (H₆ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₂ x₁ x₂) (f₁ x₃ x₄) = g₁ (g₂ x₁ x₂) (g₃ x₃ x₄))
  (H₇ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₂ x₁ x₂) (f₃ x₃ x₄) = g₁ (g₃ x₁ x₂) (g₃ x₃ x₄))
  (H₈ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₃ x₁ x₂) (f₂ x₃ x₄) = g₁ (g₃ x₁ x₂) (g₂ x₃ x₄))
  (H₉ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₁ x₁ x₂) (f₃ x₃ x₄) = g₁ (g₃ x₁ x₂) (g₂ x₃ x₄))
  (H₁₀ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₃ x₁ x₂) (f₁ x₃ x₄) = g₁ (g₃ x₁ x₂) (g₂ x₃ x₄))
  (H₁₁ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₁ x₁ x₂) (f₂ x₃ x₄) = g₁ (g₃ x₁ x₂) (g₂ x₃ x₄))
  (H₁₂ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₂ x₁ x₂) (f₁ x₃ x₄) = g₁ (g₃ x₁ x₂) (g₂ x₃ x₄))
  (H₁₃ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₂ x₁ x₂) (f₃ x₃ x₄) = g₂ (g₁ x₁ x₂) (g₃ x₃ x₄))
  (H₁₄ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₃ x₁ x₂) (f₂ x₃ x₄) = g₂ (g₁ x₁ x₂) (g₃ x₃ x₄))
  (H₁₅ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₁ x₁ x₂) (f₃ x₃ x₄) = g₂ (g₁ x₁ x₂) (g₃ x₃ x₄))
  (H₁₆ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₃ x₁ x₂) (f₁ x₃ x₄) = g₂ (g₁ x₁ x₂) (g₃ x₃ x₄))
  (H₁₇ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₁ x₁ x₂) (f₂ x₃ x₄) = g₂ (g₁ x₁ x₂) (g₃ x₃ x₄))
  (H₁₈ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₂ x₁ x₂) (f₁ x₃ x₄) = g₂ (g₁ x₁ x₂) (g₃ x₃ x₄))
  (H₁₉ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₂ x₁ x₂) (f₃ x₃ x₄) = g₂ (g₃ x₁ x₂) (g₁ x₃ x₄))
  (H₂₀ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₃ x₁ x₂) (f₂ x₃ x₄) = g₂ (g₃ x₁ x₂) (g₁ x₃ x₄))
  (H₂₁ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₁ x₁ x₂) (f₃ x₃ x₄) = g₂ (g₃ x₁ x₂) (g₁ x₃ x₄))
  (H₂₂ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₃ x₁ x₂) (f₁ x₃ x₄) = g₂ (g₃ x₁ x₂) (g₁ x₃ x₄))
  (H₂₃ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₁ x₁ x₂) (f₂ x₃ x₄) = g₂ (g₃ x₁ x₂) (g₁ x₃ x₄))
  (H₂₄ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₂ x₁ x₂) (f₁ x₃ x₄) = g₂ (g₃ x₁ x₂) (g₁ x₃ x₄))
  (H₂₅ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₂ x₁ x₂) (f₃ x₃ x₄) = g₃ (g₁ x₁ x₂) (g₂ x₃ x₄))
  (H₂₆ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₃ x₁ x₂) (f₂ x₃ x₄) = g₃ (g₁ x₁ x₂) (g₂ x₃ x₄))
  (H₂₇ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₁ x₁ x₂) (f₃ x₃ x₄) = g₃ (g₁ x₁ x₂) (g₂ x₃ x₄))
  (H₂₈ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₃ x₁ x₂) (f₁ x₃ x₄) = g₃ (g₁ x₁ x₂) (g₂ x₃ x₄))
  (H₂₉ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₁ x₁ x₂) (f₂ x₃ x₄) = g₃ (g₁ x₁ x₂) (g₂ x₃ x₄))
  (H₃₀ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₂ x₁ x₂) (f₁ x₃ x₄) = g₃ (g₁ x₁ x₂) (g₂ x₃ x₄))
  (H₃₁ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₂ x₁ x₂) (f₃ x₃ x₄) = g₃ (g₂ x₁ x₂) (g₁ x₃ x₄))
  (H₃₂ : ∀ (x₁ x₂ x₃ x₄), f₁ (f₃ x₁ x₂) (f₂ x₃ x₄) = g₃ (g₂ x₁ x₂) (g₁ x₃ x₄))
  (H₃₃ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₁ x₁ x₂) (f₃ x₃ x₄) = g₃ (g₂ x₁ x₂) (g₁ x₃ x₄))
  (H₃₄ : ∀ (x₁ x₂ x₃ x₄), f₂ (f₃ x₁ x₂) (f₁ x₃ x₄) = g₃ (g₂ x₁ x₂) (g₁ x₃ x₄))
  (H₃₅ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₁ x₁ x₂) (f₂ x₃ x₄) = g₃ (g₂ x₁ x₂) (g₁ x₃ x₄))
  (H₃₆ : ∀ (x₁ x₂ x₃ x₄), f₃ (f₂ x₁ x₂) (f₁ x₃ x₄) = g₃ (g₂ x₁ x₂) (g₁ x₃ x₄)) : True := by
  auto [H₁, H₂, H₃, H₄, H₅, H₆, H₇, H₈, H₉, H₁₀,
        H₁₁, H₁₂, H₁₃, H₁₄, H₁₅, H₁₆, H₁₇, H₁₈, H₁₉, H₂₀,
        H₂₁, H₂₂, H₂₃, H₂₄, H₂₅, H₂₆, H₂₇, H₂₈, H₂₉, H₃₀,
        H₃₁, H₃₂, H₃₃, H₃₄, H₃₅, H₃₆]

-- Multiple types
set_option trace.auto.buildChecker true in
example
  (α₁ α₂ α₃ α₄ : Type) (β₁ β₂ β₃ β₄ : Type 2)
  (f₁ : α₁ → β₁ → α₂ → β₂) (f₂ : α₃ → α₄ → β₃ → β₄) (g : β₄ → α₁)
  (α₁x₁ α₁x₂ : α₁) (α₂x₁ α₂x₂ : α₂) (α₃x₁ : α₃) (α₄x₁ : α₄)
  (β₁x₁ β₁x₂ : β₁) (β₃x₁ : β₃) (β₄x₁ : β₄)
  (H : f₁ α₁x₁ β₁x₁ α₂x₁ = f₁ α₁x₂ β₁x₂ α₂x₂)
  (I : ∀ x, β₄x₁ = f₂ α₃x₁ α₄x₁ x) (J : α₁x₂ = g β₄x₁) :
  f₁ α₁x₁ β₁x₁ α₂x₁ = f₁ (g (f₂ α₃x₁ α₄x₁ β₃x₁)) β₁x₂ α₂x₂ := by auto

-- Binder Test
set_option trace.auto.buildChecker true in
example (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ : Nat → Nat → Nat)
  (H₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₅) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₅) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₆) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₆) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₈) (f₇ x₅ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₈) (f₇ x₆ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₅) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₅) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₆) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₆) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₇) (f₇ x₅ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₇) (f₇ x₆ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉)))) :
  True := by auto