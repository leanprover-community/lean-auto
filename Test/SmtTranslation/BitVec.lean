import Auto.Tactic
open Lean Std

set_option auto.smt true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.proofReconstruction false

example : (2 : BitVec 7) + (3 : BitVec 7) = (5 : BitVec 7) := by
  auto

example (a : BitVec k) : a = a := by
  auto

example (a b : BitVec 10) : a + b = b + a := by
  auto

example (a b c : BitVec 1) : a = b ∨ b = c ∨ c = a := by
  auto

example : (2 : BitVec 7).rotateLeft 3 = (16 : BitVec 7) := by
  auto

example : (2 : BitVec 7).rotateRight 3 = (0x20 : BitVec 7) := by
  auto

example (x : BitVec 15) : x.rotateLeft 3 = x.rotateRight 12 := by
  auto

open BitVec in
example :
  Std.BitVec.zeroExtend 20 5#10 = 5#20 ∧
  Std.BitVec.zeroExtend 3 5#10 = 5#3 ∧
  Std.BitVec.signExtend 20 645#10 = 1048197#20 ∧
  Std.BitVec.signExtend 9 645#10 = 133#9 := by
  auto

-- Permutation
open BitVec in
example : (2 : BitVec 7).rotateLeft 3 = 0b10000#7 := by
  auto

open BitVec in
example (x : Nat) : (2+x)#10 = BitVec.ofNat 10 x + (2 : BitVec 10) := by
  auto

open BitVec in
example (x : Nat) : (2*x)#10 = BitVec.ofNat 10 x * (2 : BitVec 10) := by
  auto

-- Issue: `toNat` `ofNat`
open BitVec in
example : (Std.BitVec.toNat x + Std.BitVec.toNat y)#10 = x + y := by
  auto

example :
  (2 : BitVec 7).rotateRight n = (2 : BitVec 7).rotateRight n ∧
  (3 : BitVec 7).rotateRight n = (3 : BitVec 7).rotateRight n ∧
  (w : BitVec 8).rotateRight n = (w : BitVec 8).rotateRight n := by
  auto