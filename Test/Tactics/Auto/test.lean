import Auto.Tactic

open Auto Embedding

-- Collecting `logical constructors`

set_option trace.auto.printLemmas true
set_option trace.auto.tactic true
set_option trace.auto.lamULift true
set_option pp.universes true

-- **TODO**
-- 1. Implement support for monomorphic logical constants.
-- 2. Check whether `LamULift` works for dependently typed terms

example : True := by
  auto [True.intro];

example : False := by
  auto [True.intro];

example (a b : Prop) : a ∨ b ∨ a := by
  auto;

example (a b : Prop) (H : a ∨ b) : True := by
  auto [H];

example (a b : Nat) (f : Nat → Nat)
 (eqNat : Nat → Nat → Prop) (H : eqNat (f a) (f b)) : True := by
  auto [H];

example (a b : Prop) (H : impF a b) : True := by
  auto [H];

example : True := by
  try auto p [Or.inl, Or.inr];
  sorry

example : True := by
  try auto p [And.intro];
  sorry