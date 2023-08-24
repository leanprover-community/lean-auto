import Auto.Tactic

open Auto Embedding

set_option pp.universes true
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
example {α β : Type} (a : α) (b : β) (H : b = b) : a = a := by
  auto [H]

set_option trace.auto.buildChecker true in
set_option trace.auto.tactic true in
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

-- Binder test
-- Checker typechecked in time 346
set_option pp.fullNames false in
set_option trace.auto.buildChecker true in
example (f : Nat → Nat → Nat)
  (H : (fun (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) =>
    f (f (f (f (f x0 x1) (f x2 x3)) (f (f x4 x5) (f x6 x7)))
         (f (f (f x8 x9) (f x10 x11)) (f (f x12 x13) (f x14 x15))))
      (f (f (f (f x16 x17) (f x18 x19)) (f (f x20 x21) (f x22 x23)))
         (f (f (f x24 x25) (f x26 x27)) (f (f x28 x29) (f x30 x31))))) =
        (fun (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) =>
    f (f (f (f (f x0 x1) (f x2 x3)) (f (f x4 x5) (f x6 x7)))
         (f (f (f x8 x9) (f x10 x11)) (f (f x12 x13) (f x14 x15))))
      (f (f (f (f x16 x17) (f x18 x19)) (f (f x20 x21) (f x22 x23)))
         (f (f (f x24 x25) (f x26 x27)) (f (f x28 x29) (f x30 x31)))))) : True := by
  auto [H]

-- Multiple formulas
-- Checker typechecked in time 1017
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
