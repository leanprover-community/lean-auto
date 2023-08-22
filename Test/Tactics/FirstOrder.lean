import Auto.Tactic

open Auto Embedding

set_option pp.universes true
set_option trace.auto.lamReif true
example : True := by
  try auto [True.intro];
  sorry

#check Lam.LamSort.interp.{2}
example (a b : Prop) : a ∨ b ∨ a := by
  try auto;
  sorry

set_option trace.auto.metaExtra true in
set_option pp.explicit true in
example (a b : Nat) (f : Nat → Nat)
 (eqNat : Nat → Nat → Prop) (H : eqNat (f a) (f b)) : True := by
  try auto [H];
  sorry

set_option trace.auto.printLemmas true
example (a : Nat) (H : ∀ x, x = a) : a = a := by
  try auto [H];
  sorry

set_option trace.auto.tactic true
example (a : Nat) (f : Nat → Nat) (H : ∀ x, f x = x) :
  f x = f (f (f (f (f (f (f (f (f x)))))))) := by
  try auto [H];
  sorry

example (x y : Nat) (f : Nat → Nat → Nat)
  (H : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈,
    f (f (f x₁ x₂) (f x₃ x₄)) (f (f x₅ x₆) (f x₇ x₈)) =
    f (f (f x₈ x₇) (f x₆ x₅)) (f (f x₄ x₃) (f x₂ x₁))) :
  True := by
  try auto [H];
  sorry

-- This example is not supposed to work because it contains
--   dependent type
-- example (β : Prop) (a : β → β) (H : ∃ x, x = a) : a = a := by
--   auto [H];
--   sorry