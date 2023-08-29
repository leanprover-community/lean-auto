import Auto.Tactic

open Auto Embedding

-- All the following examples should pass the `ULift` stage
-- To see whether an example passes the `ULift` stage,
--   remove the `try` before `auto`, and see whether there
--   are error messages. If there is an error message, and
--   that message comes from the `ULift` stage or stages
--   before the `ULift` stage, then the example does not
--   pass the `ULift` stage, which is an indication of bug.

set_option trace.auto.printLemmas true
set_option trace.auto.tactic true
set_option trace.auto.lamPULift true
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

variable (eqFunc : (Nat → Nat) → (Nat → Nat) → Prop)

example (f : Nat → Nat) (pFunc : (Nat → Nat) → Prop)
  (H : pFunc (fun (x : Nat) => Nat.succ x)) : True := by
  try auto [H];
  sorry

example (f : Nat → Nat) (g : (Nat → Nat) → (Nat → Nat))
  (eqFunc : (Nat → Nat) → (Nat → Nat) → Prop)
  (eqHFunc : ((Nat → Nat) → (Nat → Nat)) → ((Nat → Nat) → (Nat → Nat)) → Prop)
  (H₁ : eqHFunc g (fun h x => h (h x))) : eqFunc (fun x => f (f x)) (g f) := by
  try auto [H₁];
  sorry

example (eqNat : Nat → Nat → Prop) (x : Nat)
  (H : eqNat (@Nat.rec (fun _ => Nat) 5 (fun x y => Nat.add x y) x) 8) : True := by
  try auto [H];
  sorry

set_option trace.auto.mono true in
example (a : Nat) (H : ∀ x, x = a) : a = a := by
  try auto [H];
  sorry

set_option trace.auto.mono true in
-- When monomorphization is not implemented, this example will fail
example (f : Nat → Nat) : True :=
  let H : ∃ (z : Real), ∀ (x : Nat), x = 6 → ∃ (y : Prop), f x = 2 := sorry
  by try auto [H];
     sorry

-- This example should fail. It's not an indication of a bug.
--   Refer to `Translation/LamPULift.lean`
-- example (f : Nat → Nat) (H : f = f) : True := by
--   auto