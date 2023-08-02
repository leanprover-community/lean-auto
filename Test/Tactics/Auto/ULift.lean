import Auto.Tactic

open Auto Embedding

-- All the following examples should pass the `ULift` stage

set_option trace.auto.printLemmas true
set_option trace.auto.tactic true
set_option trace.auto.lamULift true
set_option pp.universes true

example : True := by
  try auto [True.intro];
  sorry

example : False := by
  try auto [True.intro];
  sorry

example (a b : Prop) : a ∨ b ∨ a := by
  try auto;
  sorry

example (a b : Prop) (H : a ∨ b) : True := by
  try auto [H];
  sorry

example (a b : Nat) (f : Nat → Nat)
 (eqNat : Nat → Nat → Prop) (H : eqNat (f a) (f b)) : True := by
  try auto [H];
  sorry

example (a b : Prop) (H : ImpF a b) : True := by
  try auto [H];
  sorry

example (f : Nat → Nat) (iter : (Nat → Nat) → Nat → (Nat → Nat))
  (eqFunc : (Nat → Nat) → (Nat → Nat) → Prop) : eqFunc (iter f 1) f := by
  try auto [];
  sorry

example (eqNat : Nat → Nat → Prop) (x : Nat) : eqNat 2 (Nat.add 2 x) := by
  try auto [];
  sorry

example (H : 2 = 3)
  : True := by
  try auto [H];
  sorry

example (f : Nat → Nat) (eqFunc : (Nat → Nat) → (Nat → Nat) → Prop)
  (H : eqFunc f (fun (x : Nat) => Nat.succ x)) : True := by
  auto [H];

#check @Nat.rec (fun _ => Nat) 5 (fun x y => Nat.add x y) 7

example : True := by
  try auto p [And.intro];
  sorry