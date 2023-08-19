import Std.Data.Nat.Lemmas

namespace Auto

theorem Nat.lt_of_ble_eq_false {n : Nat} : Nat.ble n pos = false → pos < n := by
  intro H; apply Nat.lt_of_not_le;
  intro hle; rw [Nat.ble_eq_true_of_le hle] at H; cases H

theorem Nat.ble_eq_false_of_lt (n : Nat) : pos < n → Nat.ble n pos = false := by
  intro H;
  cases h₁ : Nat.ble n pos
  case false => rfl
  case true =>
    simp at h₁;
    have h₂ := Nat.not_le_of_lt H
    apply False.elim (h₂ h₁)

theorem Nat.ble_eq_false_eq_lt (n : Nat) : (pos < n) = (Nat.ble n pos = false) := by
  apply propext; apply Iff.intro
  case a.mp => apply Nat.ble_eq_false_of_lt
  case a.mpr => apply Nat.lt_of_ble_eq_false

theorem Nat.ble_add (a b e : Nat) : Nat.ble a b = Nat.ble (a + e) (b + e) := by
  induction e
  case zero => rfl
  case succ e => rw [e]; rfl

theorem Nat.eq_of_le_of_lt_succ {n m : Nat} (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ h₂) h₁

theorem Nat.one_add (n : Nat) : 1 + n = Nat.succ n := by simp [Nat.add_comm]

theorem Nat.pred_sub (n m : Nat) : Nat.pred n - m = Nat.pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, Nat.sub_succ]

end Auto