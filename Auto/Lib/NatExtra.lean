module

public import Auto.Lib.BoolExtra

@[expose] public section

namespace Auto

/-- A version of `Nat.beq_refl` that reduces to `Eq.refl` -/
theorem Nat.beq_refl' : (a : Nat) → (a.beq a) = true
| 0 => rfl
| n + 1 => Nat.beq_refl' n

theorem Nat.lt_of_ble_eq_false {n : Nat} (h : Nat.ble n pos = false) : pos < n := by
  simp only [Bool.eq_false_iff, ne_eq, Nat.ble_eq] at h; omega

theorem Nat.ble_eq_false_of_lt (n : Nat) (h : pos < n) : Nat.ble n pos = false := by
  simp only [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega

theorem Nat.beq_eq_false_of_ne {m n : Nat} (H : m ≠ n) : Nat.beq m n = false :=
  Bool.eq_false_iff.mpr fun h => H (Nat.eq_of_beq_eq_true h)

theorem Nat.zero_ble (b : Nat) : Nat.ble 0 b = true := rfl

theorem Nat.le_max_iff (m n k : Nat) : k ≤ max m n ↔ k ≤ m ∨ k ≤ n := Std.le_max

theorem Nat.le_pred_of_succ_le {n m : Nat} (_ : m > 0) (h : Nat.succ n ≤ m) : n ≤ Nat.pred m :=
  Nat.le_pred_of_lt h

theorem Nat.max_zero_left {a : Nat} : max 0 a = a := Nat.zero_max a

theorem Nat.max_zero_right {a : Nat} : max a 0 = a := Nat.max_zero a

/-- The reverse of `_root_.Nat.max_assoc` -/
theorem Nat.max_assoc {a b c : Nat} : max a (max b c) = max (max a b) c :=
  (_root_.Nat.max_assoc a b c).symm

theorem Nat.le_iff_div_eq_zero {a b : Nat} (h : b > 0) : a / b = 0 ↔ a < b :=
  Nat.div_eq_zero_iff_lt h

theorem Nat.le_pow (h : b ≥ 2) : a < b ^ a := Nat.lt_pow_self h

end Auto
