import Std.Data.Nat.Lemmas
import Std.Data.Nat.Bitwise
import Auto.Lib.BoolExtra

namespace Auto

/-- A version of `Nat.beq_refl` that reduces to `Eq.refl` -/
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

theorem Nat.dichotomy {m n : Nat} : m ≤ n ∨ m > n :=
  match @Nat.tricotomy m n with
  | .inl hlt => Or.inl (Nat.le_of_lt hlt)
  | .inr (.inl heq) => Or.inl (Nat.le_of_eq heq)
  | .inr (.inr hgt) => Or.inr hgt

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

theorem Nat.lt_eq_succ_le {m n : Nat} : n < m ↔ .succ n ≤ m := by rfl

theorem Nat.gt_eq_succ_le {m n : Nat} : m > n ↔ .succ n ≤ m := by rfl

theorem Nat.le_pred_of_succ_le {n m : Nat} : m > 0 → Nat.succ n ≤ m → n ≤ Nat.pred m :=
  match m with
  | 0 => fun h _ => by contradiction
  | _+1 => fun _ h => Nat.le_of_succ_le_succ h

theorem Nat.pred_lt_iff_le {n m : Nat} : m > 0 → (Nat.pred n < m ↔ n ≤ m) := by
  intro h; cases n
  case zero => simp [h]
  case succ n => rfl

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
  rw [show (max a b < c ↔ max a b + 1 ≤ c) by rfl, Nat.max_add, Nat.max_le]
  apply Iff.intro id id

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

theorem Nat.zero_lt_of_ne_zero {n : Nat} (h : n ≠ 0) : n > 0 := by
  cases n <;> try contradiction
  apply Nat.succ_le_succ (Nat.zero_le _)

theorem Nat.ne_zero_of_zero_lt {n : Nat} (h : n > 0) : n ≠ 0 := by
  cases n <;> try contradiction
  intro h; cases h

theorem Nat.eq_zero_of_mul_right_lt {a : Nat} (h : a * b < a) : b = 0 := by
  cases b <;> try rfl
  rw [Nat.mul_succ] at h
  have h' := Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left _ _)) h
  apply False.elim (Nat.not_le_of_lt h' (Nat.le_refl _))

theorem Nat.eq_zero_of_mul_left_lt {a : Nat} (h : b * a < a) : b = 0 := by
  rw [Nat.mul_comm] at h; apply Nat.eq_zero_of_mul_right_lt h

theorem Nat.le_iff_div_eq_zero {a b : Nat} (h : b > 0) : a / b = 0 ↔ a < b := by
  conv => enter [2]; rw [← Nat.div_add_mod a b]
  apply Iff.intro
  case mp => intro h'; rw [h']; rw [Nat.mul_zero, Nat.zero_add]; apply Nat.mod_lt _ h
  case mpr =>
    cases (a / b) <;> intro h' <;> try rfl
    rw [Nat.mul_succ] at h'; have h' := Nat.le_trans (Nat.succ_le_succ (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))) h'
    apply False.elim (Nat.not_lt_of_le h' (Nat.le_refl _))

theorem Nat.le_pow (h : b ≥ 2) : a < b ^ a := by
  induction a
  case zero => apply Nat.le_refl
  case succ a IH =>
    rw [Nat.pow_succ]
    apply Nat.le_trans _ (Nat.mul_le_mul_right b IH)
    apply Nat.le_trans _ (Nat.mul_le_mul_left (Nat.succ a) h)
    rw [Nat.mul_two, Nat.succ_add]
    apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.le_add_left

  theorem Nat.mod_par {a b c : Nat} (h : a % b = c) : ∃ d, a = b * d + c := by
    exists (a / b); rw [← h, Nat.div_add_mod]

  theorem Nat.div_par {a b c : Nat} (h : a / b = c) (hnz : b > 0) : ∃ d, a = b * c + d ∧ d < b := by
    exists (a % b); rw [← h, Nat.div_add_mod]; apply And.intro rfl; apply Nat.mod_lt _ hnz

  theorem Nat.le_par {a b : Nat} (h : a ≤ b) : ∃ c, b = a + c := by
    exists (b - a); rw [Nat.add_comm, Nat.sub_add_cancel h]

  theorem Nat.lt_par {a b : Nat} (h : a < b) : ∃ c, b = (a + 1) + c := Nat.le_par h

  theorem Nat.sub_mod (a b n : Nat) (h : a ≥ b) : (a - b) % n = (a - b % n) % n := by
    have ⟨k, hk⟩ := Nat.le_par h
    generalize hl : b % n = l; have ⟨d, hd⟩ := Nat.mod_par hl
    have llb : l ≤ b := by rw [← hl]; apply Nat.mod_le
    have lla : l ≤ a := Nat.le_trans llb h
    cases hd; rw [Nat.add_comm, Nat.sub_add_eq, Nat.sub_mul_mod]
    rw [Nat.le_sub_iff_add_le lla]; apply h

  theorem Nat.testBit_true_iff (a i : Nat) : a.testBit i ↔ 2 ^ i ≤ a % 2 ^ (i + 1) := by
    rw [Nat.testBit_to_div_mod, decide_eq_true_iff]; apply Iff.intro <;> intro h
    case mp =>
      have ⟨k, hk⟩ := Nat.mod_par h; clear h
      have ⟨r, ⟨er, lr⟩⟩ := Nat.div_par hk (Nat.pow_two_pos _); clear hk; cases er
      have eqi : 2 ^ i * (2 * k + 1) + r = 2 ^ (i + 1) * k + (2 ^ i + r) := by
        rw [Nat.mul_add _ _ 1, ← Nat.mul_assoc, Nat.pow_add, Nat.add_assoc]; simp
      rw [eqi, Nat.mul_add_mod]
      have elt : 2 ^ i + r < 2 ^ (i + 1) := by
        rw [Nat.pow_add, show (2 ^ 1 = 2) by rfl, Nat.mul_two]
        rw [Nat.add_lt_add_iff_left]; apply lr
      rw [Nat.mod_eq_of_lt elt]; apply Nat.le_add_right
    case mpr =>
      generalize ek : a % 2 ^ (i + 1) = k at h
      have lk : k < 2 ^ (i + 1) := by cases ek; apply Nat.mod_lt; apply Nat.pow_two_pos
      have ⟨l, hl⟩ := Nat.mod_par ek; clear ek; cases hl
      have eqi : 2 ^ (i + 1) * l + k = 2 ^ i * (2 * l) + k := by
        rw [Nat.pow_add, Nat.mul_assoc]; simp
      rw [eqi, Nat.mul_add_div (Nat.pow_two_pos _), Nat.mul_add_mod]
      have kdge : k / (2 ^ i) > 0 := (Nat.le_div_iff_mul_le (Nat.pow_two_pos _)).mpr (by simp [h])
      have kdle : k / (2 ^ i) < 2 := (Nat.div_lt_iff_lt_mul (Nat.pow_two_pos _)).mpr (by rw [Nat.pow_add, Nat.mul_comm] at lk; apply lk)
      have kone : k / (2 ^ i) = 1 := Nat.eq_iff_le_and_ge.mpr (And.intro (Nat.le_of_succ_le_succ kdle) kdge)
      rw [kone]; rfl

  theorem Nat.testBit_false_iff (a i : Nat) : a.testBit i = false ↔ a % 2 ^ (i + 1) < 2 ^ i := by
    rw [Bool.eq_false_eq_not_eq_true, ne_eq, Nat.testBit_true_iff, Nat.not_le]

  theorem Nat.ones_testBit_true_of_lt (n i : Nat) (h : i < n) : (2 ^ n - 1).testBit i := by
    rw [Nat.testBit_true_iff]; have ⟨k, ek⟩ := Nat.lt_par h; clear h; cases ek
    have eqi : 2 ^ (i + 1 + k) - 1 = 2 ^ (i + 1) * (2 ^ k - 1) + (2 ^ (i + 1) - 1) := calc
      _ = 2 ^ (i + 1) * 2 ^ k - 1 := by rw [Nat.pow_add]
      _ = 2 ^ (i + 1) * (2 ^ k - 1 + 1) - 1 := by rw [Nat.sub_add_cancel]; apply Nat.pow_two_pos
      _ = _ := by
        have hle : 1 ≤ 2 ^ (i + 1) * 1 := by rw [Nat.mul_one]; apply Nat.pow_two_pos
        rw [Nat.mul_add]; rw [Nat.add_sub_assoc hle]; simp
    rw [eqi, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.pow_two_pos _) .refl)]
    rw [Nat.pow_add, show (2 ^ 1 = 2) by rfl, Nat.mul_two, show (Nat.succ 0 = 1) by rfl]
    rw [Nat.add_sub_assoc (Nat.pow_two_pos _)]; apply Nat.le_add_right

  theorem Nat.ones_testBit_false_of_ge (n i : Nat) (h : i ≥ n) : (2 ^ n - 1).testBit i = false := by
    have hl : 2 ^ n - 1 < 2 ^ i := by
      rw [Nat.lt_eq_succ_le, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pow_two_pos _)]
      apply Nat.pow_le_pow_of_le_right (Nat.le_step .refl) h
    have hls : 2 ^ i ≤ 2 ^ (i + 1) := Nat.pow_le_pow_of_le_right (Nat.le_step .refl) (Nat.le_add_right _ _)
    rw [Nat.testBit_false_iff]; rw [Nat.mod_eq_of_lt (Nat.le_trans hl hls)]; apply hl

  theorem Nat.xor_def (a b : Nat) : a ^^^ b = a.xor b := rfl

  theorem Nat.ones_xor (n a : Nat) (h : a < 2 ^ n) : (2 ^ n - 1) ^^^ a = 2 ^ n - 1 - a := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [xor_def, Nat.xor, Nat.testBit_bitwise (f:=bne) rfl]
    have texp : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [Nat.pow_add, show (2 ^ 1 = 2) by rfl, Nat.mul_two]
    cases @Nat.dichotomy n i
    case inl hl =>
      rw [Nat.ones_testBit_false_of_ge _ _ hl]
      rw [show (∀ b, (false != b) = b) by (intro b; simp)]
      have ple : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_of_le_right (Nat.le_step .refl) hl
      have lf : Nat.testBit a i = false := by
        rw [Nat.testBit_false_iff]
        apply Nat.le_trans _ (Nat.le_trans h ple); apply Nat.succ_le_succ
        apply Nat.mod_le
      have rf : Nat.testBit (2 ^ n - 1 - a) i = false := by
        rw [Nat.testBit_false_iff]
        have li : 2 ^ n - 1 - a < 2 ^ i := by
          rw [← Nat.sub_add_eq, Nat.lt_eq_succ_le, Nat.succ_eq_add_one]
          rw [← Nat.sub_add_comm (show 1 + a ≤ 2 ^ n by rw [Nat.add_comm]; exact h)]
          rw [Nat.sub_add_eq, Nat.add_sub_cancel]; rw [Nat.sub_le_iff_le_add]
          apply Nat.le_trans ple (Nat.le_add_right _ _)
        rw [Nat.mod_eq_of_lt (Nat.le_trans li (by rw [texp]; apply Nat.le_add_right))]
        apply li
      rw [lf, rf]
    case inr hl =>
      rw [Nat.ones_testBit_true_of_lt _ _ hl]
      rw [show (∀ b, (true != b) = !b) by (intro b; simp)]
      generalize hk : a % 2 ^ (i + 1) = k
      have kl : k < 2 ^ (i + 1) := by rw [← hk]; apply Nat.mod_lt; apply Nat.pow_two_pos
      have tr : (2 ^ n - 1 - a) % 2 ^ (i + 1) = 2 ^ (i + 1) - (k + 1) := by
        rw [Nat.sub_mod _ _ _ (show a ≤ 2 ^ n - 1 by exact (Nat.le_sub_iff_add_le (Nat.pow_two_pos _)).mpr h)]
        rw [hk]; have ⟨dn, hdn⟩ := Nat.lt_par hl; cases hdn
        rw [Nat.pow_add _ _ dn, show (2 ^ dn = 2 ^ dn - 1 + 1) by rw[Nat.sub_add_cancel (Nat.pow_two_pos _)]]
        rw [Nat.mul_add, Nat.mul_one, ← Nat.sub_add_eq]
        rw [Nat.add_sub_assoc (by rw [Nat.add_comm]; exact kl)]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt, Nat.add_comm 1 k]
        apply Nat.sub_lt (Nat.pow_two_pos _)
        rw [Nat.add_comm]; apply Nat.zero_lt_succ
      cases hai : Nat.testBit a i
      case false =>
        rw [Nat.testBit_false_iff] at hai
        apply Eq.symm; rw [show ((!false) = true) by rfl, Nat.testBit_true_iff]
        rw [hk] at hai; rw [tr, Nat.le_sub_iff_add_le kl, Nat.succ_eq_add_one]
        rw [texp]; apply Nat.add_le_add_left; exact hai
      case true =>
        rw [Nat.testBit_true_iff] at hai
        apply Eq.symm; rw [show ((!true) = false) by rfl, Nat.testBit_false_iff]
        rw [hk] at hai; rw [tr, Nat.lt_eq_succ_le, Nat.succ_eq_add_one]
        rw [← Nat.sub_add_comm kl, Nat.succ_eq_add_one]
        rw [Nat.add_comm k 1, Nat.sub_add_eq, Nat.add_sub_cancel]
        rw [Nat.sub_le_iff_le_add, texp]; apply Nat.add_le_add_left; exact hai

end Auto
