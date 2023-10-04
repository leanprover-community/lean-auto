import Std.Data.Nat.Lemmas

namespace Auto

-- A version of `Nat.beq_refl` that reduces to `Eq.refl`
def Nat.beq_refl' : (a : Nat) → (a.beq a) = true
| 0 => rfl
| n + 1 => Nat.beq_refl' n

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

theorem Nat.beq_eq_false_of_ne {m n : Nat} (H : m ≠ n) : Nat.beq m n = false := by
  cases h : Nat.beq m n
  case true => apply False.elim (H _); apply Nat.eq_of_beq_eq_true h
  case false => rfl

theorem Nat.ne_of_beq_eq_false {m n : Nat} (H : Nat.beq m n = false) : m ≠ n := by
  intro h; rw [h] at H; rw [Nat.beq_refl] at H; cases H

theorem Nat.ble_add (a b e : Nat) : Nat.ble a b = Nat.ble (a + e) (b + e) := by
  induction e
  case zero => rfl
  case succ e => rw [e]; rfl

theorem Nat.zero_ble (b : Nat) : Nat.ble 0 b = true := by cases b <;> rfl

theorem Nat.tricotomy {m n : Nat} : m < n ∨ m = n ∨ m > n := by
  cases Nat.le_or_le m n
  case inl h =>
    cases Nat.lt_or_eq_of_le h
    case inl h => exact Or.inl h
    case inr h => exact Or.inr (Or.inl h)
  case inr h =>
    cases Nat.lt_or_eq_of_le h
    case inl h => exact Or.inr (Or.inr h)
    case inr h => exact Or.inr (Or.inl h.symm)

theorem Nat.lt_or_gt_of_ne {m n : Nat} (H : m ≠ n) : m < n ∨ m > n :=
  match @Nat.tricotomy m n with
  | .inl h => Or.inl h
  | .inr (.inl h) => False.elim (H h)
  | .inr (.inr h) => Or.inr h

theorem Nat.eq_of_le_of_lt_succ {n m : Nat} (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ h₂) h₁

theorem Nat.one_add (n : Nat) : 1 + n = Nat.succ n := by simp [Nat.add_comm]

theorem Nat.pred_sub (n m : Nat) : Nat.pred n - m = Nat.pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, Nat.sub_succ]

theorem Nat.le_max_iff (m n k : Nat) : k ≤ max m n ↔ k ≤ m ∨ k ≤ n := by
  apply Iff.intro
  case mp =>
    intro h; rw [Nat.max_def] at h;
    cases h' : Nat.ble m n
    case false =>
      have h' := Nat.not_le_of_lt (Nat.lt_of_ble_eq_false h')
      simp [h'] at h; exact Or.inl h
    case true =>
      simp [Nat.le_of_ble_eq_true h'] at h; exact Or.inr h
  case mpr =>
    intro h; cases h
    case inl h => exact Nat.le_trans h (Nat.le_max_left _ _)
    case inr h => exact Nat.le_trans h (Nat.le_max_right _ _)

theorem Nat.gt_eq_succ_le {m n : Nat} : m > n ↔ .succ n ≤ m := by rfl

theorem Nat.le_pred_of_succ_le {n m : Nat} : m ≠ 0 → Nat.succ n ≤ m → n ≤ Nat.pred m :=
  match m with
  | 0 => fun h _ => by contradiction
  | _+1 => fun _ h => Nat.le_of_succ_le_succ h

theorem Nat.max_add {a b c : Nat} : max a b + c = max (a + c) (b + c) := by
  rw [Nat.max_def, Nat.max_def];
  cases Nat.decLe a b
  case isTrue h =>
    have aclebc : a + c ≤ b + c := Nat.add_le_add h .refl; simp [h, aclebc]
  case isFalse h =>
    have naleb : ¬ a + c ≤ b + c := by
      intro h'; apply h; apply Nat.le_of_add_le_add_right h'
    simp [h, naleb]

theorem Nat.max_lt {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.lt_eq]; dsimp [Nat.lt]; rw [← Nat.add_one]; rw [Nat.max_add]
  rw [Nat.max_le]; apply Iff.intro id id

theorem Nat.max_zero_left {a : Nat} : max 0 a = a := by
  rw [Nat.max_def]; simp

theorem Nat.max_zero_right {a : Nat} : max a 0 = a := by
  rw [Nat.max_comm]; apply Nat.max_zero_left

theorem Nat.max_assoc {a : Nat} : max a (max b c) = max (max a b) c := by
  cases Nat.decLe a b
  case isFalse h =>
    rw [Nat.max_def (m:=b)]; simp [h]
    cases Nat.decLe b c
    case isFalse h' =>
      rw [Nat.max_def (m:=c)]; simp [h']
      rw [Nat.max_def (m:=b)]; simp [h]
      have clta := Nat.lt_trans (Nat.lt_of_not_le h') (Nat.lt_of_not_le h)
      rw [Nat.max_def]; simp [Nat.not_le_of_lt clta]
    case isTrue h' =>
      rw [Nat.max_def (m:=c)]; simp [h']
  case isTrue h =>
    rw [Nat.max_def (m:=b)]; simp [h]
    cases Nat.decLe b c
    case isFalse h' =>
      rw [Nat.max_def (m:=c)]; simp [h']
      rw [Nat.max_def]; simp [h]
    case isTrue h' =>
      rw [Nat.max_def (m:=c)]; simp [h']
      rw [Nat.max_def]; simp [Nat.le_trans h h']

end Auto