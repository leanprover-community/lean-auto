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

example :
  (2 : BitVec 7).rotateRight n = (2 : BitVec 7).rotateRight n ∧
  (3 : BitVec 7).rotateRight n = (3 : BitVec 7).rotateRight n ∧
  (w : BitVec 8).rotateRight n = (w : BitVec 8).rotateRight n := by
  auto