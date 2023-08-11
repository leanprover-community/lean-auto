import Auto.Tactic

open Auto Embedding

example : True := by
  try auto [True.intro];
  sorry

example (a b : Prop) : a ∨ b ∨ a := by
  try auto;
  sorry

example (a b : Nat) (f : Nat → Nat)
 (eqNat : Nat → Nat → Prop) (H : eqNat (f a) (f b)) : True := by
  try auto [H];
  sorry

set_option trace.auto.printLemmas true
example (a : Nat) (H : ∀ x, x = a) : a = a := by
  try auto [H];
  sorry