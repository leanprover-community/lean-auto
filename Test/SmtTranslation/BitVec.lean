import Auto.Tactic
open Lean Std

set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

set_option auto.smt true

open Std.BitVec

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

example : (extractLsb 127 64 a ++ extractLsb 63 0 a) = a := by
  auto

example :
  434#8 >>> 4 = 0x0b#8 ∧ 434#8 >>> 4#5 = 0x0b#8 ∧
  34#8 >>> 4 = 0x02#8 ∧ 34#8 >>> 4#12 = 0x02#8 ∧
  (434#8).sshiftRight 4 = 0xfb#8 ∧
  (34#8).sshiftRight 4 = 0x02#8 := by auto

example (x : BitVec 20) (y : BitVec 4) :
  (0#5).rotateLeft x.toNat = 0#5 ∧ (0#5).rotateLeft y.toNat = 0#5 := by
  auto

example (x : BitVec 20) (y : BitVec 4) :
  (0#5).rotateRight x.toNat = 0#5 ∧ (0#5).rotateRight y.toNat = 0#5 := by
  auto

example : (0#5).rotateLeft n = 0#5 ∧ (0#5).rotateRight n = 0#5 := by auto

example (x : BitVec 8) : x.rotateLeft (7 - 2 * 2) = x.rotateLeft (1 + 2) := by
  auto

example (x : BitVec 8) : x.rotateLeft 100 = x ∧ x.rotateRight 100 = x := by auto

example :
  Std.BitVec.zeroExtend 20 5#10 = 5#20 ∧
  Std.BitVec.zeroExtend 3 5#10 = 5#3 ∧
  Std.BitVec.signExtend 20 645#10 = 1048197#20 ∧
  Std.BitVec.signExtend 9 645#10 = 133#9 := by
  auto

-- Permutation
example : (2 : BitVec 7).rotateLeft 3 = 0b10000#7 := by
  auto

example (x : Nat) : (2+x)#10 = BitVec.ofNat 10 x + (2 : BitVec 10) := by
  auto

example (x : Nat) : (2*x)#10 = BitVec.ofNat 10 x * (2 : BitVec 10) := by
  auto

example : (Std.BitVec.toNat x + Std.BitVec.toNat y)#10 = x + y := by
  auto

example :
  (2 : BitVec 7).rotateRight n = (2 : BitVec 7).rotateRight n ∧
  (3 : BitVec 7).rotateRight n = (3 : BitVec 7).rotateRight n ∧
  (w : BitVec 8).rotateRight n = (w : BitVec 8).rotateRight n := by
  auto

example : 101#32 <<< 2#32 = 404#32 := by auto

example : (3#10).toNat = 3 := by auto

example (x : Nat) (h : x > 0) : ((25 * x) / x)#3 = 1#3 := by auto

example : (12#10).toInt = 12 && (686#10).toInt = -338 := by auto
example : (12#10).toInt = 12 ∧ (686#10).toInt = -338 := by auto
example : Std.BitVec.ofInt 4 (-6) = 10#4 ∧ Std.BitVec.ofInt 4 10 = 10#4 := by auto
