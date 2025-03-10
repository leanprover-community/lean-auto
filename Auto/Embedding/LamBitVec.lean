import Auto.Embedding.LamConv
import Auto.Lib.NatExtra

namespace Auto.Embedding.Lam

namespace BVLems

  open BitVec

  theorem toNat_ofNat (n a : Nat) : (BitVec.ofNat n a).toNat = a % (2 ^ n) := rfl

  theorem toNat_ofNatLt {n : Nat} (i : Nat) (p : i < 2 ^ n) : (BitVec.ofNatLt i p).toNat = i := rfl

  theorem toNat_le (a : BitVec n) : a.toNat < 2 ^ n := by
    rcases a with ⟨⟨_, isLt⟩⟩; exact isLt

  theorem eq_of_val_eq {a b : BitVec n} (h : a.toNat = b.toNat) : a = b := by
    rcases a with ⟨⟨a, isLta⟩⟩; rcases b with ⟨⟨b, isLtb⟩⟩
    dsimp [BitVec.toNat] at h; cases h; rfl

  theorem val_eq_of_eq {a b : BitVec n} (h : a = b) : a.toNat = b.toNat := by
    cases h; rfl

  theorem eq_iff_val_eq {a b : BitVec n} : a = b ↔ a.toNat = b.toNat :=
    Iff.intro val_eq_of_eq eq_of_val_eq

  theorem ne_of_val_ne {a b : BitVec n} (h : a.toNat ≠ b.toNat) : a ≠ b := by
    intro h'; cases h'; apply False.elim (h rfl)

  theorem val_ne_of_ne {a b : BitVec n} (h : a ≠ b) : a.toNat ≠ b.toNat := by
    intro h'; apply h; apply eq_of_val_eq h'

  theorem ne_iff_val_ne {a b : BitVec n} : a ≠ b ↔ a.toNat ≠ b.toNat :=
    Iff.intro val_ne_of_ne ne_of_val_ne

  theorem shiftLeft_def (a : BitVec n) (i : Nat) : a <<< i = a.shiftLeft i := rfl

  theorem smtshiftLeft_def (a : BitVec n) (b : BitVec m) : a <<< b = a <<< b.toNat := rfl

  theorem ushiftRight_def (a : BitVec n) (i : Nat) : a >>> i = a.ushiftRight i := rfl

  theorem smtushiftRight_def (a : BitVec n) (b : BitVec m) : a >>> b = a >>> b.toNat := rfl

  theorem neg_def (a : BitVec n) : -a = a.neg := rfl

  theorem sub_def (a b : BitVec n) : a - b = a.sub b := rfl

  theorem toNat_shiftLeft {a : BitVec n} (i : Nat) : (a <<< i).toNat = (a.toNat * (2 ^ i)) % (2 ^ n) := by
    rw [shiftLeft_def]; rcases a with ⟨⟨a, isLt⟩⟩
    unfold BitVec.shiftLeft BitVec.toNat BitVec.ofNat Fin.ofNat'
    dsimp; rw [Nat.shiftLeft_eq]

  theorem toNat_ushiftRight {a : BitVec n} (i : Nat) : (a >>> i).toNat = (a.toNat) / (2 ^ i) := by
    rw [ushiftRight_def]; rcases a with ⟨⟨a, isLt⟩⟩
    unfold BitVec.ushiftRight BitVec.toNat
    dsimp; rw [Nat.shiftRight_eq_div_pow]

  theorem toNat_zeroExtend' {a : BitVec n} (le : n ≤ m) : (a.setWidth' le).toNat = a.toNat := rfl

  theorem toNat_zeroExtend {a : BitVec n} (i : Nat) : (a.zeroExtend i).toNat = a.toNat % (2 ^ i) := by
    unfold BitVec.zeroExtend BitVec.setWidth; cases hdec : decide (n ≤ i)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.dite_eq_false (proof:=hnle)]; rfl
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.dite_eq_true (proof:=hle), toNat_zeroExtend']
      rw [Nat.mod_eq_of_lt]; rcases a with ⟨⟨a, isLt⟩⟩;
      apply Nat.le_trans isLt; apply Nat.pow_le_pow_of_le_right (Nat.le_step .refl) hle

  theorem toNat_sub (a b : BitVec n) : (a - b).toNat = (2 ^ n - b.toNat + a.toNat) % (2 ^ n) := rfl

  theorem toNat_sub' (a b : BitVec n) : (a - b).toNat = (a.toNat + (2 ^ n - b.toNat)) % (2 ^ n) := by
    rw [toNat_sub]; rw [Nat.add_comm]

  theorem toNat_neg (a : BitVec n) : (-a).toNat = (2^n - a.toNat) % (2^n) := by
    rw [neg_def]; unfold BitVec.neg; rw [toNat_ofNat]

  theorem toNat_and (a b : BitVec n) : (a &&& b).toNat = a.toNat &&& b.toNat := rfl

  theorem toNat_or (a b : BitVec n) : (a ||| b).toNat = a.toNat ||| b.toNat := rfl

  theorem toNat_xor (a b : BitVec n) : (a ^^^ b).toNat = a.toNat ^^^ b.toNat := rfl

  theorem toNat_not (a : BitVec n) : (~~~a).toNat = 2 ^ n - 1 - a.toNat :=
    _root_.BitVec.toNat_not

  theorem shiftLeft_ge_length_eq_zero (a : BitVec n) (i : Nat) : i ≥ n → a <<< i = 0#n := by
    intro h; apply eq_of_val_eq; rw [toNat_shiftLeft, toNat_ofNat]; apply Nat.mod_eq_zero_of_dvd
    have poweq : 2 ^ i = 2 ^ (i - n) * 2 ^ n := by rw [← Nat.pow_add, Nat.sub_add_cancel h]
    rw [poweq, ← Nat.mul_assoc, Nat.mul_comm _ (2^n)]; exact ⟨_, rfl⟩

  theorem ushiftRight_ge_length_eq_zero (a : BitVec n) (i : Nat) : i ≥ n → a >>> i = 0#n := by
    intro h; apply eq_of_val_eq; rw [toNat_ushiftRight, toNat_ofNat]
    apply (Nat.le_iff_div_eq_zero (Nat.two_pow_pos _)).mpr
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem ushiftRight_ge_length_eq_zero' (a : BitVec n) (i : Nat) : i ≥ n → BitVec.ofNat n (a.toNat >>> i) = 0#n := by
    intro h; apply congrArg (@BitVec.ofNat n)
    rw [Nat.shiftRight_eq_div_pow, Nat.le_iff_div_eq_zero (Nat.two_pow_pos _)]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem msb_equiv_lt (a : BitVec n) : !a.msb ↔ a.toNat < 2 ^ (n - 1) := by
    dsimp [BitVec.msb, BitVec.getMsbD, BitVec.getLsbD]
    cases n
    case zero => cases a <;> simp
    case succ n =>
      have dtrue : decide (0 < n + 1) = true := by simp
      rw [dtrue, Bool.not_eq_true', Bool.true_and, Nat.succ_sub_one, Nat.testBit_false_iff]
      rw [Nat.mod_eq_of_lt (toNat_le _)]

  theorem msb_equiv_lt' (a : BitVec n) : !a.msb ↔ 2 * a.toNat < 2 ^ n := by
    rw [msb_equiv_lt]
    cases n
    case zero => cases a <;> simp
    case succ n =>
      rw [Nat.succ_sub_one, Nat.pow_succ, Nat.mul_comm (m:=2)]
      apply Iff.symm; apply Nat.mul_lt_mul_left
      exact .step .refl

  theorem sshiftRight_ge_length_eq_msb (a : BitVec n) (i : Nat) : i ≥ n → a.sshiftRight i =
    if a.msb then (1#n).neg else 0#n := by
    intro h; simp [sshiftRight, BitVec.toInt, ← msb_equiv_lt']
    cases hmsb : a.msb <;> simp [hmsb, Int.shiftRight_def]
    case false =>
      rw [BitVec.ofNat]
      apply ushiftRight_ge_length_eq_zero'; exact h
    case true =>
      rw [← Int.subNatNat_eq_coe, Int.subNatNat_of_lt (toNat_le _)]
      simp [BitVec.toInt, BitVec.ofInt]
      have hzero : (2 ^ n - BitVec.toNat a - 1) >>> i = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; apply (Nat.le_iff_div_eq_zero (Nat.two_pow_pos _)).mpr
        rw [Nat.sub_one, Nat.pred_lt_iff_le (Nat.two_pow_pos _)]
        apply Nat.le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_of_le_right (.step .refl) h)
      apply eq_of_val_eq; rw [toNat_ofNatLt, hzero]
      rw [toNat_neg, Int.mod_def', Int.emod]
      rw [Nat.zero_mod, Int.natAbs_ofNat, Nat.succ_eq_add_one, Nat.zero_add]
      rw [Int.subNatNat_of_sub_eq_zero ((Nat.sub_eq_zero_iff_le).mpr (Nat.two_pow_pos _))]
      rw [Int.toNat_ofNat, BitVec.toNat_ofNat]
      cases n <;> try rfl
      case succ n =>
        have hlt : 2 ≤ 2 ^ Nat.succ n := @Nat.pow_le_pow_of_le_right 2 (.step .refl) 1 (.succ n) (Nat.succ_le_succ (Nat.zero_le _))
        rw [Nat.mod_eq_of_lt (a:=1) hlt]
        rw [Nat.mod_eq_of_lt]; apply Nat.sub_lt (Nat.le_trans (.step .refl) hlt) .refl

  theorem shiftRight_eq_zero_iff (a : BitVec n) (b : Nat) : a >>> b = 0#n ↔ a.toNat < 2 ^ b := by
    rw [ushiftRight_def]; rcases a with ⟨⟨a, isLt⟩⟩;
    unfold ushiftRight; rw [eq_iff_val_eq]
    dsimp [BitVec.toNat, BitVec.ofNat]
    rw [Nat.zero_mod, Nat.shiftRight_eq_div_pow]
    apply Iff.intro <;> intro h
    case mp =>
      rw [← Nat.le_iff_div_eq_zero (Nat.two_pow_pos _)]
      exact h
    case mpr => rw [(Nat.le_iff_div_eq_zero (Nat.two_pow_pos _)).mpr h]

  theorem ofNat_toNat (a : BitVec n) : .ofNat m a.toNat = a.zeroExtend m := by
    apply eq_of_val_eq; rw [toNat_ofNat, toNat_zeroExtend]

  theorem ofNat_add (n a b : Nat) : BitVec.ofNat n (a + b) = BitVec.ofNat n a + BitVec.ofNat n b := by
    apply congrArg (f:=BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.add_mod]; rfl

  theorem ofNat_mod_pow2 (n a : Nat) : BitVec.ofNat n (a % (2 ^ n)) = BitVec.ofNat n a := by
    apply congrArg (f:=BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; apply Nat.mod_mod

  theorem ofNat_sub (n a b : Nat) : BitVec.ofNat n (a - b) =
    if (a < b) then 0#n else (BitVec.ofNat n a - BitVec.ofNat n b) := by
    cases hdec : decide (a < b)
    case false =>
      have hnlt := of_decide_eq_false hdec; have hle := Nat.le_of_not_lt hnlt
      rw [Bool.ite_eq_false _ _ _ hnlt]; apply eq_of_val_eq
      rw [toNat_ofNat, toNat_sub', toNat_ofNat, toNat_ofNat]
      have exc : ∃ c, a = b + c := ⟨a - b, by rw [Nat.add_comm, Nat.sub_add_cancel hle]⟩
      rcases exc with ⟨c, ⟨⟩⟩
      rw [Nat.add_sub_cancel_left, Nat.mod_add_mod, Nat.add_assoc b c]
      rw [← Nat.mod_add_mod, ← Nat.add_assoc _ c, Nat.add_comm _ c, Nat.add_assoc c]
      rw [Nat.add_comm (b % _), Nat.sub_add_cancel, ← Nat.add_mod_mod, Nat.mod_self, Nat.add_zero]
      apply Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, Nat.sub_eq_zero_of_le]
      apply Nat.le_of_lt hle

  theorem ofNat_sub' (n a b : Nat) : BitVec.ofNat n (a - b) =
    (Bool.ite' (a < b) (GLift.up.{1, u} 0#n) (GLift.up.{1, u} (BitVec.ofNat n a - BitVec.ofNat n b))).down := by
    have h := ofNat_sub n a b; rw [Bool.ite_simp] at h; rw [Bool.ite'_comm (f:=GLift.down)]; exact h

  theorem ofNat_mul (n a b : Nat) : BitVec.ofNat n (a * b) = BitVec.ofNat n a * BitVec.ofNat n b := by
    apply congrArg (f:=BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.mul_mod]; rfl

  theorem shl_equiv (a : BitVec n) (b : Nat) : a <<< b = if (b < n) then (a <<< BitVec.ofNat n b) else 0 := by
    cases hdec : decide (b < n)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hnle, shiftLeft_ge_length_eq_zero _ _ (Nat.le_of_not_lt hnle)]; rfl
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, smtshiftLeft_def, toNat_ofNat, Nat.mod_eq_of_lt]
      apply Nat.le_trans hle (Nat.le_of_lt (Nat.le_pow .refl))

  theorem shl_equiv'.{u} (a : BitVec n) (b : Nat) : a <<< b =
    (Bool.ite' (b < n) (GLift.up.{1, u} (a <<< BitVec.ofNat n b)) (GLift.up.{1, u} 0)).down := by
    have h := shl_equiv a b; rw [Bool.ite_simp] at h; rw [Bool.ite'_comm (f := GLift.down)]; exact h

  theorem shl_toNat_equiv_short (a : BitVec n) (b : BitVec m) (h : m ≤ n) : a <<< b.toNat = a <<< (zeroExtend n b) := by
    apply eq_of_val_eq; rw [toNat_shiftLeft, smtshiftLeft_def, toNat_shiftLeft, toNat_zeroExtend, Nat.mod_eq_of_lt (a:=BitVec.toNat b)]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem shl_toNat_equiv_long (a : BitVec n) (b : BitVec m) (h : m > n) : a <<< b.toNat =
    if (b >>> (BitVec.ofNat m n)) = 0#m then a <<< (zeroExtend n b) else 0 := by
    have eqof : BitVec.toNat (BitVec.ofNat m n) = n := by
      rw [toNat_ofNat]; apply Nat.mod_eq_of_lt
      apply Nat.le_trans (Nat.succ_le_succ (Nat.le_of_lt h)) (Nat.le_pow (Nat.le_refl _))
    cases hdec : decide ((b >>> (BitVec.ofNat m n)) = 0#m)
    case false =>
      have hne := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hne]
      rw [smtushiftRight_def, eqof, shiftRight_eq_zero_iff] at hne
      rw [shiftLeft_ge_length_eq_zero]; rfl
      apply Nat.le_trans (m:=2^n) (Nat.le_of_lt (Nat.le_pow (Nat.le_refl _)))
      apply Nat.le_of_not_lt hne
    case true =>
      have heq := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ heq]; apply congrArg
      rw [smtushiftRight_def, eqof, shiftRight_eq_zero_iff] at heq
      rw [toNat_zeroExtend, Nat.mod_eq_of_lt heq]

  theorem shl_toNat_equiv_long'.{u} (a : BitVec n) (b : BitVec m) (h : m > n) : a <<< b.toNat =
    (Bool.ite' (GLift.up.{1, u} (b >>> (BitVec.ofNat m n)) = GLift.up.{1, u} 0#m)
      (GLift.up.{1, u} (a <<< (zeroExtend n b))) (GLift.up.{1, u} 0#n)).down := by
    have h := shl_toNat_equiv_long a b h; rw [Bool.ite_simp] at h
    rw [eqGLift_equiv, Bool.ite'_comm (f := GLift.down)]; exact h

  theorem lshr_equiv (a : BitVec n) (b : Nat) : a >>> b = if (b < n) then (a >>> BitVec.ofNat n b) else 0 := by
    cases hdec : decide (b < n)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hnle, ushiftRight_ge_length_eq_zero _ _ (Nat.le_of_not_lt hnle)]; rfl
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, smtushiftRight_def, toNat_ofNat, Nat.mod_eq_of_lt]
      apply Nat.le_trans hle (Nat.le_of_lt (Nat.le_pow .refl))

  theorem lshr_equiv'.{u} (a : BitVec n) (b : Nat) : a >>> b =
    (Bool.ite' (b < n) (GLift.up.{1, u} (a >>> BitVec.ofNat n b)) (GLift.up.{1, u} 0)).down := by
    have h := lshr_equiv a b; rw [Bool.ite_simp] at h; rw [Bool.ite'_comm (f := GLift.down)]; exact h

  theorem lshr_toNat_equiv_short (a : BitVec n) (b : BitVec m) (h : m ≤ n) : a >>> b.toNat = a >>> (zeroExtend n b) := by
    apply eq_of_val_eq; rw [toNat_ushiftRight, smtushiftRight_def, toNat_ushiftRight, toNat_zeroExtend, Nat.mod_eq_of_lt]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem lshr_toNat_equiv_long (a : BitVec n) (b : BitVec m) (h : m > n) : a >>> b.toNat =
    if (b >>> (BitVec.ofNat m n)) = 0#m then a >>> (zeroExtend n b) else 0 := by
    have eqof : BitVec.toNat (BitVec.ofNat m n) = n := by
      rw [toNat_ofNat]; apply Nat.mod_eq_of_lt
      apply Nat.le_trans (Nat.succ_le_succ (Nat.le_of_lt h)) (Nat.le_pow (Nat.le_refl _))
    cases hdec : decide ((b >>> (BitVec.ofNat m n)) = 0#m)
    case false =>
      have hne := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ (of_decide_eq_false hdec)]
      rw [smtushiftRight_def, eqof, shiftRight_eq_zero_iff] at hne
      rw [ushiftRight_ge_length_eq_zero]; rfl
      apply Nat.le_trans (m:=2^n) (Nat.le_of_lt (Nat.le_pow (Nat.le_refl _)))
      apply Nat.le_of_not_lt hne
    case true =>
      have heq := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ heq]; apply congrArg
      rw [smtushiftRight_def, eqof, shiftRight_eq_zero_iff] at heq
      rw [toNat_zeroExtend, Nat.mod_eq_of_lt heq]

  theorem lshr_toNat_equiv_long'.{u} (a : BitVec n) (b : BitVec m) (h : m > n) : a >>> b.toNat =
    (Bool.ite' (GLift.up.{1, u} (b >>> (BitVec.ofNat m n)) = GLift.up.{1, u} 0#m)
      (GLift.up.{1, u} (a >>> (zeroExtend n b))) (GLift.up.{1, u} 0)).down := by
    have h := lshr_toNat_equiv_long a b h; rw [Bool.ite_simp] at h
    rw [eqGLift_equiv, Bool.ite'_comm (f := GLift.down)]; exact h

  theorem ashr_equiv (a : BitVec n) (b : Nat) : a.sshiftRight b = if (b < n) then (a.sshiftRight (BitVec.ofNat n b).toNat) else (if a.msb then (1#n).neg else 0#n) := by
    cases hdec : decide (b < n)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hnle, sshiftRight_ge_length_eq_msb _ _ (Nat.le_of_not_lt hnle)]
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, toNat_ofNat, Nat.mod_eq_of_lt]
      apply Nat.le_trans hle (Nat.le_of_lt (Nat.le_pow .refl))

  theorem ashr_equiv'.{u} (a : BitVec n) (b : Nat) : a.sshiftRight b =
    (Bool.ite' (b < n) (GLift.up.{1, u} (a.sshiftRight (BitVec.ofNat n b).toNat))
      (Bool.ite' (GLift.up.{1, u} a.msb = GLift.up.{1, u} true) (GLift.up.{1, u} (1#n).neg) (GLift.up.{1, u} 0#n))).down := by
    have h := ashr_equiv a b; rw [Bool.ite_simp] at h; rw [eqGLift_equiv]
    rw [Bool.ite'_comm (f := GLift.down), Bool.ite'_comm (f := GLift.down)]; exact h

  theorem ashr_toNat_equiv_short (a : BitVec n) (b : BitVec m) (h : m ≤ n) : a.sshiftRight b.toNat = a.sshiftRight (zeroExtend n b).toNat := by
    apply eq_of_val_eq; rw [toNat_zeroExtend, Nat.mod_eq_of_lt]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem ashr_toNat_equiv_long (a : BitVec n) (b : BitVec m) (h : m > n) : a.sshiftRight b.toNat =
    if (b >>> (BitVec.ofNat m n)) = 0#m then a.sshiftRight (zeroExtend n b).toNat else (if a.msb then (1#n).neg else 0#n) := by
    have eqof : BitVec.toNat (BitVec.ofNat m n) = n := by
      rw [toNat_ofNat]; apply Nat.mod_eq_of_lt
      apply Nat.le_trans (Nat.succ_le_succ (Nat.le_of_lt h)) (Nat.le_pow (Nat.le_refl _))
    cases hdec : decide ((b >>> (BitVec.ofNat m n)) = 0#m)
    case false =>
      have hne := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ (of_decide_eq_false hdec)]
      rw [smtushiftRight_def, eqof, shiftRight_eq_zero_iff] at hne
      rw [sshiftRight_ge_length_eq_msb]
      apply Nat.le_trans (m:=2^n) (Nat.le_of_lt (Nat.le_pow (Nat.le_refl _)))
      apply Nat.le_of_not_lt hne
    case true =>
      have heq := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ heq]; apply congrArg
      rw [smtushiftRight_def, eqof, shiftRight_eq_zero_iff] at heq
      rw [toNat_zeroExtend, Nat.mod_eq_of_lt heq]

  theorem ashr_toNat_equiv_long'.{u} (a : BitVec n) (b : BitVec m) (h : m > n) : a.sshiftRight b.toNat =
    (Bool.ite' (GLift.up.{1, u} (b >>> (BitVec.ofNat m n)) = GLift.up.{1, u} 0#m)
      (GLift.up.{1, u} (a.sshiftRight (zeroExtend n b).toNat))
      (Bool.ite'
        (GLift.up.{1, u} a.msb = GLift.up.{1, u} true)
        (GLift.up.{1, u} (1#n).neg) (GLift.up.{1, u} 0#n))).down := by
    have h := ashr_toNat_equiv_long a b h; rw [Bool.ite_simp] at h
    rw [eqGLift_equiv, eqGLift_equiv]
    rw [Bool.ite'_comm (f := GLift.down),  Bool.ite'_comm (f := GLift.down)]; exact h

end BVLems

theorem LamEquiv.bvofNat :
  LamEquiv lval lctx (.base (.bv n)) (.mkBvofNat n (.mkNatVal i)) (.base (.bvVal n i)) :=
  ⟨.mkBvofNat (.ofBase (.ofNatVal i)), .ofBase (.ofBvVal n i), fun _ => rfl⟩

theorem LamEquiv.bvofNat_bvtoNat
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base (.bv n)⟩) :
  LamEquiv lval lctx (.base (.bv m))
    (.mkBvofNat m (.mkBvUOp n (.bvtoNat n) t))
    (.app (.base (.bv n)) (.base (.bvzeroExtend n m)) t) :=
  ⟨.mkBvofNat (.mkBvUOp (.ofBvtoNat n) wft),
   .ofApp _ (.ofBase (.ofBvzeroExtend n m)) wft, fun lctxTerm => by
    apply GLift.down.inj; apply BitVec.ofNat_toNat⟩

theorem LamEquiv.bvofNat_nadd
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nadd a b))
    (.mkBvBinOp n (.bvadd n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNadd wfa wfb),
   .mkBvBinOp (.ofBvadd _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
      apply GLift.down.inj; apply BVLems.ofNat_add⟩

def LamTerm.bvofNat_nsub (n : Nat) (a b bva bvb : LamTerm) :=
  LamTerm.mkIte (.base (.bv n)) (.mkNatBinOp .nlt a b)
    (.base (.bvVal n 0)) (.mkBvBinOp n (.bvsub n) bva bvb)

theorem LamEquiv.bvofNat_nsub
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nsub a b))
    (.bvofNat_nsub n a b (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNsub wfa wfb),
   .mkIte (.mkNatBinOp .ofNlt wfa wfb)
     (.ofBase (.ofBvVal n 0)) (.mkBvBinOp (.ofBvsub _) (.mkBvofNat wfa) (.mkBvofNat wfb)), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.ofNat_sub'⟩

theorem LamEquiv.bvofNat_nmul
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nmul a b))
    (.mkBvBinOp n (.bvmul n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNmul wfa wfb),
   .mkBvBinOp (.ofBvmul _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.ofNat_mul⟩

def LamTerm.shl_equiv (n : Nat) (a b bbv : LamTerm) :=
  LamTerm.mkIte (.base (.bv n)) (.mkNatBinOp .nlt b (.base (.natVal n)))
    (.mkBvBinOp n (.bvsmtshl n) a bbv) (.base (.bvVal n 0))

theorem LamTerm.congr_maxEVarSucc_shl_equiv
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂)
  (eqbbv : maxEVarSucc bbv₁ = maxEVarSucc bbv₂) :
  (shl_equiv n₁ a₁ b₁ bbv₁).maxEVarSucc = (shl_equiv n₂ a₂ b₂ bbv₂).maxEVarSucc := by
  dsimp [shl_equiv, mkIte, mkNatBinOp, mkBvBinOp, maxEVarSucc]; rw [eqa, eqb, eqbbv]

theorem LamEquiv.congr_shl_equiv
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base .nat) b₁ b₂)
  (eqbbv : LamEquiv lval lctx (.base (.bv n)) bbv₁ bbv₂) :
  LamEquiv lval lctx (.base (.bv n)) (.shl_equiv n a₁ b₁ bbv₁) (.shl_equiv n a₂ b₂ bbv₂) :=
  congrFun (congr (congrArg (.ofBase (.ofIte _))
    (congrFun (congrArg (.ofBase .ofNlt) eqb)
      (.ofBase (.ofNatVal _)))) (congr (congrArg (.ofBase (.ofBvsmtshl _)) eqa) eqbbv))
      (.ofBase (.ofBvVal _ _))

theorem LamEquiv.shl_equiv
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvshl n) a b)
    (.shl_equiv n a b (.mkBvofNat n b)) :=
  ⟨.mkBvNatBinOp (.ofBvshl _) wfa wfb,
   .mkIte (.mkNatBinOp (.ofNlt) wfb (.ofBase (.ofNatVal n)))
    (.mkBvBinOp (.ofBvsmtshl _) wfa (.mkBvofNat wfb)) (.ofBase (.ofBvVal _ _)), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.shl_equiv'⟩

abbrev LamTerm.shl_toNat_equiv_short (n : Nat) (a : LamTerm) (m : Nat) (b : LamTerm) :=
  LamTerm.mkBvBinOp n (.bvsmtshl n) a (.mkBvUOp m (.bvzeroExtend m n) b)

theorem LamTerm.congr_maxEVarSucc_shl_toNat_equiv_short
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂) :
  (shl_toNat_equiv_short n₁ a₁ m₁ b₁).maxEVarSucc = (shl_toNat_equiv_short n₂ a₂ m₂ b₂).maxEVarSucc := by
  dsimp [shl_toNat_equiv_short, mkBvBinOp, mkBvUOp, maxEVarSucc]; rw [eqa, eqb]

theorem LamEquiv.congr_shl_toNat_equiv_short
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base (.bv m)) b₁ b₂) :
  LamEquiv lval lctx (.base (.bv n)) (.shl_toNat_equiv_short n a₁ m b₁) (.shl_toNat_equiv_short n a₂ m b₂) :=
  congr (congrArg (.ofBase (.ofBvsmtshl _)) eqa) (congrArg (.ofBase (.ofBvzeroExtend _ _)) eqb)

theorem LamEquiv.shl_toNat_equiv_short
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base (.bv m)⟩)
  (h : m ≤ n) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvshl n) a (.mkBvUOp m (.bvtoNat m) b))
    (.shl_toNat_equiv_short n a m b) :=
  ⟨.mkBvNatBinOp (.ofBvshl _) wfa (.mkBvUOp (.ofBvtoNat _) wfb),
   .mkBvBinOp (.ofBvsmtshl _) wfa (.mkBvUOp (.ofBvzeroExtend _ _) wfb), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.shl_toNat_equiv_short _ _ h⟩

abbrev LamTerm.shl_toNat_equiv_long (n : Nat) (a : LamTerm) (m : Nat) (b : LamTerm) :=
  LamTerm.mkIte (.base (.bv n))
    (.mkEq (.base (.bv m)) (.mkBvBinOp m (.bvsmtlshr m) b (.base (.bvVal m n))) (.base (.bvVal m 0)))
    (.mkBvBinOp n (.bvsmtshl n) a (.mkBvUOp m (.bvzeroExtend m n) b)) (.base (.bvVal n 0))

theorem LamTerm.congr_maxEVarSucc_shl_toNat_equiv_long
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂) :
  (shl_toNat_equiv_long n₁ a₁ m₁ b₁).maxEVarSucc = (shl_toNat_equiv_long n₂ a₂ m₂ b₂).maxEVarSucc := by
  dsimp [shl_toNat_equiv_long, mkIte, mkEq, mkBvBinOp, mkBvUOp, maxEVarSucc]; rw [eqa, eqb]

theorem LamEquiv.congr_shl_toNat_equiv_long
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base (.bv m)) b₁ b₂) :
  LamEquiv lval lctx (.base (.bv n)) (.shl_toNat_equiv_long n a₁ m b₁) (.shl_toNat_equiv_long n a₂ m b₂) :=
  congrFun (congr (congrArg (.ofBase (.ofIte _))
    (congrFun (congrArg (.ofBase (.ofEq _)) (congrFun
      (congrArg (.ofBase (.ofBvsmtlshr _)) eqb) (.ofBase (.ofBvVal _ _))))
        (.ofBase (.ofBvVal _ _))))
    (congr (congrArg (.ofBase (.ofBvsmtshl _)) eqa) (congrArg (.ofBase (.ofBvzeroExtend _ _)) eqb)))
    (.ofBase (.ofBvVal _ _))

theorem LamEquiv.shl_toNat_equiv_long
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base (.bv m)⟩)
  (h : m > n) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvshl n) a (.mkBvUOp m (.bvtoNat m) b))
    (.shl_toNat_equiv_long n a m b) :=
  ⟨.mkBvNatBinOp (.ofBvshl _) wfa (.mkBvUOp (.ofBvtoNat _) wfb),
   .mkIte
    (.mkEq (.mkBvBinOp (.ofBvsmtlshr _) wfb (.ofBase (.ofBvVal _ _))) (.ofBase (.ofBvVal _ _)))
    (.mkBvBinOp (.ofBvsmtshl _) wfa (.mkBvUOp (.ofBvzeroExtend _ _) wfb)) (.ofBase (.ofBvVal _ _)), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.shl_toNat_equiv_long' _ _ h⟩

def LamTerm.lshr_equiv (n : Nat) (a b bbv : LamTerm) :=
  LamTerm.mkIte (.base (.bv n)) (.mkNatBinOp .nlt b (.base (.natVal n)))
    (.mkBvBinOp n (.bvsmtlshr n) a bbv) (.base (.bvVal n 0))

theorem LamTerm.congr_maxEVarSucc_lshr_equiv
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂)
  (eqbbv : maxEVarSucc bbv₁ = maxEVarSucc bbv₂) :
  (lshr_equiv n₁ a₁ b₁ bbv₁).maxEVarSucc = (lshr_equiv n₂ a₂ b₂ bbv₂).maxEVarSucc := by
  dsimp [lshr_equiv, mkIte, mkNatBinOp, mkBvBinOp, maxEVarSucc]; rw [eqa, eqb, eqbbv]

theorem LamEquiv.congr_lshr_equiv
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base .nat) b₁ b₂)
  (eqbbv : LamEquiv lval lctx (.base (.bv n)) bbv₁ bbv₂) :
  LamEquiv lval lctx (.base (.bv n)) (.lshr_equiv n a₁ b₁ bbv₁) (.lshr_equiv n a₂ b₂ bbv₂) :=
  congrFun (congr (congrArg (.ofBase (.ofIte _)) (congrFun (congrArg (.ofBase .ofNlt) eqb)
    (.ofBase (.ofNatVal _)))) (congr (congrArg (.ofBase (.ofBvsmtlshr _)) eqa) eqbbv))
    (.ofBase (.ofBvVal _ _))

theorem LamEquiv.lshr_equiv
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvlshr n) a b)
    (.lshr_equiv n a b (.mkBvofNat n b)) :=
  ⟨.mkBvNatBinOp (.ofBvlshr _) wfa wfb,
   .mkIte (.mkNatBinOp (.ofNlt) wfb (.ofBase (.ofNatVal n)))
    (.mkBvBinOp (.ofBvsmtlshr _) wfa (.mkBvofNat wfb)) (.ofBase (.ofBvVal _ _)), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.lshr_equiv'⟩

abbrev LamTerm.lshr_toNat_equiv_short (n : Nat) (a : LamTerm) (m : Nat) (b : LamTerm) :=
  LamTerm.mkBvBinOp n (.bvsmtlshr n) a (.mkBvUOp m (.bvzeroExtend m n) b)

theorem LamTerm.congr_maxEVarSucc_lshr_toNat_equiv_short
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂) :
  (lshr_toNat_equiv_short n₁ a₁ m₁ b₁).maxEVarSucc = (lshr_toNat_equiv_short n₂ a₂ m₂ b₂).maxEVarSucc := by
  dsimp [lshr_toNat_equiv_short, mkBvBinOp, mkBvUOp, maxEVarSucc]; rw [eqa, eqb]

theorem LamEquiv.congr_lshr_toNat_equiv_short
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base (.bv m)) b₁ b₂) :
  LamEquiv lval lctx (.base (.bv n)) (.lshr_toNat_equiv_short n a₁ m b₁) (.lshr_toNat_equiv_short n a₂ m b₂) :=
  congr (congrArg (.ofBase (.ofBvsmtlshr _)) eqa) (congrArg (.ofBase (.ofBvzeroExtend _ _)) eqb)

theorem LamEquiv.lshr_toNat_equiv_short
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base (.bv m)⟩)
  (h : m ≤ n) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvlshr n) a (.mkBvUOp m (.bvtoNat m) b))
    (.lshr_toNat_equiv_short n a m b) :=
  ⟨.mkBvNatBinOp (.ofBvlshr _) wfa (.mkBvUOp (.ofBvtoNat _) wfb),
   .mkBvBinOp (.ofBvsmtlshr _) wfa (.mkBvUOp (.ofBvzeroExtend _ _) wfb), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.lshr_toNat_equiv_short _ _ h⟩

abbrev LamTerm.lshr_toNat_equiv_long (n : Nat) (a : LamTerm) (m : Nat) (b : LamTerm) :=
  LamTerm.mkIte (.base (.bv n))
    (.mkEq (.base (.bv m)) (.mkBvBinOp m (.bvsmtlshr m) b (.base (.bvVal m n))) (.base (.bvVal m 0)))
    (.mkBvBinOp n (.bvsmtlshr n) a (.mkBvUOp m (.bvzeroExtend m n) b)) (.base (.bvVal n 0))

theorem LamTerm.congr_maxEVarSucc_lshr_toNat_equiv_long
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂) :
  (lshr_toNat_equiv_long n₁ a₁ m₁ b₁).maxEVarSucc = (lshr_toNat_equiv_long n₂ a₂ m₂ b₂).maxEVarSucc := by
  dsimp [lshr_toNat_equiv_long, mkIte, mkEq, mkBvBinOp, mkBvUOp, maxEVarSucc]; rw [eqa, eqb]

theorem LamEquiv.congr_lshr_toNat_equiv_long
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base (.bv m)) b₁ b₂) :
  LamEquiv lval lctx (.base (.bv n)) (.lshr_toNat_equiv_long n a₁ m b₁) (.lshr_toNat_equiv_long n a₂ m b₂) :=
  congrFun (congr (congrArg (.ofBase (.ofIte _))
    (congrFun (congrArg (.ofBase (.ofEq _)) (congrFun
      (congrArg (.ofBase (.ofBvsmtlshr _)) eqb)
        (.ofBase (.ofBvVal _ _)))) (.ofBase (.ofBvVal _ _))))
    (congr (congrArg (.ofBase (.ofBvsmtlshr _)) eqa) (congrArg (.ofBase (.ofBvzeroExtend _ _)) eqb)))
    (.ofBase (.ofBvVal _ _))

theorem LamEquiv.lshr_toNat_equiv_long
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base (.bv m)⟩)
  (h : m > n) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvlshr n) a (.mkBvUOp m (.bvtoNat m) b))
    (.lshr_toNat_equiv_long n a m b) :=
  ⟨.mkBvNatBinOp (.ofBvlshr _) wfa (.mkBvUOp (.ofBvtoNat _) wfb),
    .mkIte
      (.mkEq (.mkBvBinOp (.ofBvsmtlshr _) wfb (.ofBase (.ofBvVal _ _))) (.ofBase (.ofBvVal _ _)))
      (.mkBvBinOp (.ofBvsmtlshr _) wfa (.mkBvUOp (.ofBvzeroExtend _ _) wfb)) (.ofBase (.ofBvVal _ _)), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.lshr_toNat_equiv_long' _ _ h⟩

def LamTerm.ashr_equiv (n : Nat) (a b bbv : LamTerm) :=
  LamTerm.mkIte (.base (.bv n)) (.mkNatBinOp .nlt b (.base (.natVal n)))
    (.mkBvBinOp n (.bvsmtashr n) a bbv)
    (.mkIte (.base (.bv n)) (.mkEq (.base .bool) (.mkBvUOp n (.bvmsb n) a) (.base .trueb))
      (.mkBvUOp n (.bvneg n) (.base (.bvVal n 1))) (.base (.bvVal n 0)))

theorem LamTerm.congr_maxEVarSucc_ashr_equiv
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂)
  (eqbbv : maxEVarSucc bbv₁ = maxEVarSucc bbv₂) :
  (ashr_equiv n₁ a₁ b₁ bbv₁).maxEVarSucc = (ashr_equiv n₂ a₂ b₂ bbv₂).maxEVarSucc := by
  dsimp [ashr_equiv, mkIte, mkEq, mkNatBinOp, mkBvUOp, mkBvBinOp, maxEVarSucc]; rw [eqa, eqb, eqbbv]

theorem LamEquiv.congr_ashr_equiv
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base .nat) b₁ b₂)
  (eqbbv : LamEquiv lval lctx (.base (.bv n)) bbv₁ bbv₂) :
  LamEquiv lval lctx (.base (.bv n)) (.ashr_equiv n a₁ b₁ bbv₁) (.ashr_equiv n a₂ b₂ bbv₂) :=
  congr (congr (congrArg (.ofBase (.ofIte _)) (congrFun (congrArg (.ofBase .ofNlt) eqb) (.ofBase (.ofNatVal _))))
    (congr (congrArg (.ofBase (.ofBvsmtashr _)) eqa) eqbbv))
    (congrFun (congrFun (congrArg (.ofBase (.ofIte _)) (congrFun
      (congrArg (.ofBase (.ofEq _)) (congrArg (.ofBase (.ofBvmsb _)) eqa)) (.ofBase .ofTrueB)))
      (.ofApp _ (.ofBase (.ofBvneg _)) (.ofBase (.ofBvVal _ _))))
      (.ofBase (.ofBvVal _ _)))

theorem LamEquiv.ashr_equiv
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvashr n) a b)
    (.ashr_equiv n a b (.mkBvofNat n b)) :=
  ⟨.mkBvNatBinOp (.ofBvashr _) wfa wfb,
   .mkIte (.mkNatBinOp (.ofNlt) wfb (.ofBase (.ofNatVal n)))
    (.mkBvBinOp (.ofBvsmtashr _) wfa (.mkBvofNat wfb))
    (.mkIte (.mkEq (.mkBvUOp (.ofBvmsb _) wfa) (.ofBase .ofTrueB))
      (.mkBvUOp (.ofBvneg _) ((.ofBase (.ofBvVal _ _))))
      (.ofBase (.ofBvVal _ _))), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.ashr_equiv'⟩

abbrev LamTerm.ashr_toNat_equiv_short (n : Nat) (a : LamTerm) (m : Nat) (b : LamTerm) :=
  LamTerm.mkBvBinOp n (.bvsmtashr n) a (.mkBvUOp m (.bvzeroExtend m n) b)

theorem LamTerm.congr_maxEVarSucc_ashr_toNat_equiv_short
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂) :
  (ashr_toNat_equiv_short n₁ a₁ m₁ b₁).maxEVarSucc = (ashr_toNat_equiv_short n₂ a₂ m₂ b₂).maxEVarSucc := by
  dsimp [ashr_toNat_equiv_short, mkBvUOp, mkBvBinOp, maxEVarSucc]; rw [eqa, eqb]

theorem LamEquiv.congr_ashr_toNat_equiv_short
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base (.bv m)) b₁ b₂) :
  LamEquiv lval lctx (.base (.bv n)) (.ashr_toNat_equiv_short n a₁ m b₁) (.ashr_toNat_equiv_short n a₂ m b₂) :=
  congr (congrArg (.ofBase (.ofBvsmtashr _)) eqa) (congrArg (.ofBase (.ofBvzeroExtend _ _)) eqb)

theorem LamEquiv.ashr_toNat_equiv_short
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base (.bv m)⟩)
  (h : m ≤ n) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvashr n) a (.mkBvUOp m (.bvtoNat m) b))
    (.ashr_toNat_equiv_short n a m b) :=
  ⟨.mkBvNatBinOp (.ofBvashr _) wfa (.mkBvUOp (.ofBvtoNat _) wfb),
   .mkBvBinOp (.ofBvsmtashr _) wfa (.mkBvUOp (.ofBvzeroExtend _ _) wfb), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.ashr_toNat_equiv_short _ _ h⟩

def LamTerm.ashr_toNat_equiv_long (n : Nat) (a : LamTerm) (m : Nat) (b : LamTerm) :=
  LamTerm.mkIte (.base (.bv n))
    (.mkEq (.base (.bv m)) (.mkBvBinOp m (.bvsmtlshr m) b (.base (.bvVal m n))) (.base (.bvVal m 0)))
    (.mkBvBinOp n (.bvsmtashr n) a (.mkBvUOp m (.bvzeroExtend m n) b))
    (.mkIte (.base (.bv n)) (.mkEq (.base .bool) (.mkBvUOp n (.bvmsb n) a) (.base .trueb))
      (.mkBvUOp n (.bvneg n) (.base (.bvVal n 1)))
      (.base (.bvVal n 0)))

theorem LamTerm.congr_maxEVarSucc_ashr_toNat_equiv_long
  (eqa : maxEVarSucc a₁ = maxEVarSucc a₂)
  (eqb : maxEVarSucc b₁ = maxEVarSucc b₂) :
  (ashr_toNat_equiv_long n₁ a₁ m₁ b₁).maxEVarSucc = (ashr_toNat_equiv_long n₂ a₂ m₂ b₂).maxEVarSucc := by
  dsimp [ashr_toNat_equiv_long, mkIte, mkEq, mkBvUOp, mkBvBinOp, maxEVarSucc]; rw [eqa, eqb]

theorem LamEquiv.congr_ashr_toNat_equiv_long
  (eqa : LamEquiv lval lctx (.base (.bv n)) a₁ a₂)
  (eqb : LamEquiv lval lctx (.base (.bv m)) b₁ b₂) :
  LamEquiv lval lctx (.base (.bv n)) (.ashr_toNat_equiv_long n a₁ m b₁) (.ashr_toNat_equiv_long n a₂ m b₂) :=
  congr (congr (congrArg (.ofBase (.ofIte _)) (congrFun (congrArg (.ofBase (.ofEq _))
    (congrFun (congrArg (.ofBase (.ofBvsmtlshr _)) eqb) (.ofBase (.ofBvVal _ _)))) (.ofBase (.ofBvVal _ _))))
    (congr (congrArg (.ofBase (.ofBvsmtashr _)) eqa) (congrArg (.ofBase (.ofBvzeroExtend _ _)) eqb)))
    (congrFun (congrFun (congrArg (.ofBase (.ofIte _)) (congrFun (congrArg (.ofBase (.ofEq _))
      (congrArg (.ofBase (.ofBvmsb _)) eqa)) (.ofBase .ofTrueB))) (.mkBvUOp (.ofBvneg _) (.ofBase (.ofBvVal _ _))))
      (.ofBase (.ofBvVal _ _)))

theorem LamEquiv.ashr_toNat_equiv_long
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base (.bv n)⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base (.bv m)⟩)
  (h : m > n) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvNatBinOp n (.bvashr n) a (.mkBvUOp m (.bvtoNat m) b))
    (.ashr_toNat_equiv_long n a m b) :=
  ⟨.mkBvNatBinOp (.ofBvashr _) wfa (.mkBvUOp (.ofBvtoNat _) wfb),
    .mkIte
      (.mkEq (.mkBvBinOp (.ofBvsmtlshr _) wfb (.ofBase (.ofBvVal _ _))) (.ofBase (.ofBvVal _ _)))
      (.mkBvBinOp (.ofBvsmtashr _) wfa (.mkBvUOp (.ofBvzeroExtend _ _) wfb))
        (.mkIte (.mkEq (.mkBvUOp (.ofBvmsb _) wfa) (.ofBase .ofTrueB))
          (.mkBvUOp (.ofBvneg _) (.ofBase (.ofBvVal _ _)))
          (.ofBase (.ofBvVal _ _))), fun lctxTerm => by
    apply GLift.down.inj; apply BVLems.ashr_toNat_equiv_long' _ _ h⟩

inductive BVCastType where
  | ofNat : Nat → BVCastType
  | ofInt : Nat → BVCastType
  | none

def LamTerm.applyBVCast (ct : BVCastType) (t : LamTerm) : LamTerm :=
  match ct with
  | .ofNat n => mkBvofNat n t
  | .ofInt n => mkBvofInt n t
  | .none    => t

def LamTerm.pushBVCast (ct : BVCastType) (t : LamTerm) : LamTerm :=
  match ct with
  | .ofNat n =>
    match t with
    | .base (.ncst (.natVal i)) => .base (.bvcst (.bvVal n i))
    | .app _ (.base (.bvcst (.bvtoNat m))) arg =>
      .app (.base (.bv m)) (.base (.bvzeroExtend m n)) (pushBVCast .none arg)
    | .app _ (.app _ (.base (.ncst .nadd)) lhs) rhs =>
      mkBvBinOp n (.bvadd n) (pushBVCast (.ofNat n) lhs) (pushBVCast (.ofNat n) rhs)
    | .app _ (.app _ (.base (.ncst .nsub)) lhs) rhs =>
      bvofNat_nsub n lhs rhs (pushBVCast (.ofNat n ) lhs) (pushBVCast (.ofNat n ) rhs)
    | .app _ (.app _ (.base (.ncst .nmul)) lhs) rhs =>
      mkBvBinOp n (.bvmul n) (pushBVCast (.ofNat n) lhs) (pushBVCast (.ofNat n) rhs)
    | _ => mkBvofNat n t
  -- Not implemented
  | .ofInt n => mkBvofInt n t
  | .none =>
    match t with
    | .lam s body => .lam s (pushBVCast .none body)
    | .app _ (.base (.bvcst (.bvofNat n))) arg => pushBVCast (.ofNat n) arg
    | .app _ (.base (.bvcst (.bvofInt n))) arg => pushBVCast (.ofInt n) arg
    | .app _ (.app _ (.base (.bvcst (.bvshl n))) arg₁) (.app _ (.base (.bvcst (.bvtoNat m))) arg₂) =>
      match m.ble n with
      | true  => LamTerm.shl_toNat_equiv_short n (pushBVCast .none arg₁) m (pushBVCast .none arg₂)
      | false => LamTerm.shl_toNat_equiv_long n (pushBVCast .none arg₁) m (pushBVCast .none arg₂)
    | .app _ (.app _ (.base (.bvcst (.bvshl n))) arg₁) arg₂ =>
      LamTerm.shl_equiv n (pushBVCast .none arg₁) (pushBVCast .none arg₂) (pushBVCast (.ofNat n) arg₂)
    | .app _ (.app _ (.base (.bvcst (.bvlshr n))) arg₁) (.app _ (.base (.bvcst (.bvtoNat m))) arg₂) =>
      match m.ble n with
      | true  => LamTerm.lshr_toNat_equiv_short n (pushBVCast .none arg₁) m (pushBVCast .none arg₂)
      | false => LamTerm.lshr_toNat_equiv_long n (pushBVCast .none arg₁) m (pushBVCast .none arg₂)
    | .app _ (.app _ (.base (.bvcst (.bvlshr n))) arg₁) arg₂ =>
      LamTerm.lshr_equiv n (pushBVCast .none arg₁) (pushBVCast .none arg₂) (pushBVCast (.ofNat n) arg₂)
    | .app _ (.app _ (.base (.bvcst (.bvashr n))) arg₁) (.app _ (.base (.bvcst (.bvtoNat m))) arg₂) =>
      match m.ble n with
      | true  => LamTerm.ashr_toNat_equiv_short n (pushBVCast .none arg₁) m (pushBVCast .none arg₂)
      | false => LamTerm.ashr_toNat_equiv_long n (pushBVCast .none arg₁) m (pushBVCast .none arg₂)
    | .app _ (.app _ (.base (.bvcst (.bvashr n))) arg₁) arg₂ =>
      LamTerm.ashr_equiv n (pushBVCast .none arg₁) (pushBVCast .none arg₂) (pushBVCast (.ofNat n) arg₂)
    | .app s fn arg => .app s (pushBVCast .none fn) (pushBVCast .none arg)
    | _ => t

theorem LamTerm.maxEVarSucc_pushBVCast : maxEVarSucc (pushBVCast ct t) = maxEVarSucc t := by
  generalize tl' : t.size = l; have tl : t.size ≤ l := by cases tl'; exact .refl
  clear tl'
  induction l generalizing t ct <;>
    try apply False.elim (LamTerm.size_ne_zero (Nat.le_zero.mp tl))
  case succ l IH =>
    cases t <;> try (cases ct <;> rfl)
    case base b =>
      cases b <;> try (cases ct <;> rfl)
      case ncst nc =>
        cases nc <;> cases ct <;> rfl
    case lam s body =>
      cases ct <;> try apply Nat.max_zero_left
      case none =>
        dsimp [pushBVCast, maxEVarSucc]; apply IH
        apply Nat.le_of_succ_le_succ tl
    case app s fn arg =>
      have leFn : LamTerm.size fn ≤ l := Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_fn tl)
      have leArg : LamTerm.size arg ≤ l := Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
      cases ct
      case ofNat m =>
        cases fn <;> try apply Nat.max_zero_left
        case base b =>
          cases b <;> try apply Nat.max_zero_left
          case bvcst bvc =>
            cases bvc <;> try apply Nat.max_zero_left
            case bvtoNat =>
              dsimp [pushBVCast, maxEVarSucc]; rw [IH leArg]
        case app s fn arg₁ =>
          cases fn <;> try apply Nat.max_zero_left
          case base b =>
            cases b <;> try apply Nat.max_zero_left
            case ncst nc =>
              cases nc <;> (try apply Nat.max_zero_left) <;> try (
                dsimp [pushBVCast, maxEVarSucc, mkBvBinOp]
                simp [IH (Nat.le_trans LamTerm.size_app_ge_size_arg leFn), IH leArg])
              case nsub =>
                dsimp [pushBVCast, maxEVarSucc, bvofNat_nsub, mkIte, mkBvBinOp, mkNatBinOp, Nat.max]
                simp [IH (Nat.le_trans LamTerm.size_app_ge_size_arg leFn), IH leArg]
      case ofInt m => apply Nat.max_zero_left
      case none =>
        have fneq := fun ct => @IH ct _ leFn
        have argeq := fun ct => @IH ct _ leArg
        have hbr : maxEVarSucc (app s (pushBVCast BVCastType.none fn) (pushBVCast BVCastType.none arg))
          = maxEVarSucc (app s fn arg) := by
          rw [maxEVarSucc_app, fneq, argeq]; rfl
        cases fn <;> rw [maxEVarSucc_app] <;> try apply hbr
        case base b =>
          cases b <;> try (dsimp [maxEVarSucc, pushBVCast]; rw [IH leArg])
          case bvcst bvc =>
            cases bvc <;> dsimp [maxEVarSucc, pushBVCast] <;> rw [IH leArg]
            case bvofNat => rw [Nat.max_zero_left]
            case bvofInt => rw [Nat.max_zero_left]
        case app s'' fn arg₁ =>
          have leArg₁ := Nat.le_trans LamTerm.size_app_ge_size_arg leFn
          have argeq₁ := fun ct => @IH ct _ leArg₁
          cases fn <;> try apply hbr
          case base b =>
            cases b <;> try apply hbr
            case bvcst bvc =>
              cases bvc <;> try apply hbr
              case bvshOp n smt? shOp =>
                cases smt? <;> try apply hbr
                have maxlem₁ (a b : Nat) : max a (max b a) = max b a := by
                  rw [Nat.max_comm b, Nat.max_assoc, Nat.max_eq_left (Nat.le_refl _)]
                have maxlem₂ (a b : Nat) : max (max a (max b a)) b = max b a := by
                  rw [Nat.max_comm a, ← Nat.max_assoc, Nat.max_comm a b, Nat.max_eq_left (Nat.le_refl _)]
                cases shOp
                case shl =>
                  have h_none_shl :
                    ((LamTerm.shl_equiv n (.pushBVCast .none arg₁) (.pushBVCast .none arg) (.pushBVCast (.ofNat n) arg))).maxEVarSucc =
                    (LamTerm.mkBvNatBinOp n (BitVecConst.bvshl n) arg₁ arg).maxEVarSucc :=
                    Eq.trans (LamTerm.congr_maxEVarSucc_shl_equiv (n₁:=n) (n₂:=n)
                      (argeq₁ .none) (argeq .none) (argeq (.ofNat n)))
                      (by
                        dsimp [shl_equiv, mkIte, mkNatBinOp, mkBvBinOp, mkBvNatBinOp, maxEVarSucc, pushBVCast]
                        simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right]
                        apply maxlem₁)
                  cases arg
                  case app s''' fn' arg₂ =>
                    have leArg₂ := Nat.le_trans LamTerm.size_app_ge_size_arg leArg
                    have argeq₂ := fun ct => @IH ct _ leArg₂
                    cases fn'
                    case base b =>
                      cases b
                      case bvcst bvc =>
                        cases bvc
                        case bvtoNat m =>
                          dsimp [maxEVarSucc, pushBVCast]
                          cases m.ble n <;> dsimp [shl_toNat_equiv_short, shl_toNat_equiv_long, mkIte, mkEq, mkBvUOp, mkBvBinOp, maxEVarSucc] <;> rw [argeq₁, argeq₂]
                          simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right, maxlem₁]
                        all_goals apply h_none_shl
                      all_goals apply h_none_shl
                    all_goals apply h_none_shl
                  all_goals apply h_none_shl
                case lshr =>
                  have h_none_lshr :
                    ((LamTerm.lshr_equiv n (.pushBVCast .none arg₁) (.pushBVCast .none arg) (.pushBVCast (.ofNat n) arg))).maxEVarSucc =
                    (LamTerm.mkBvNatBinOp n (BitVecConst.bvshl n) arg₁ arg).maxEVarSucc :=
                    Eq.trans (LamTerm.congr_maxEVarSucc_lshr_equiv (n₁:=n) (n₂:=n)
                      (argeq₁ .none) (argeq .none) (argeq (.ofNat n)))
                      (by
                        dsimp [lshr_equiv, mkIte, mkNatBinOp, mkBvBinOp, mkBvNatBinOp, maxEVarSucc, pushBVCast]
                        simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right]
                        apply maxlem₁)
                  cases arg
                  case app s''' fn' arg₂ =>
                    have leArg₂ := Nat.le_trans LamTerm.size_app_ge_size_arg leArg
                    have argeq₂ := fun ct => @IH ct _ leArg₂
                    cases fn'
                    case base b =>
                      cases b
                      case bvcst bvc =>
                        cases bvc
                        case bvtoNat m =>
                          dsimp [maxEVarSucc, pushBVCast]
                          cases m.ble n <;> dsimp [lshr_toNat_equiv_short , lshr_toNat_equiv_long, mkIte, mkEq, mkBvUOp, mkBvBinOp, maxEVarSucc] <;> rw [argeq₁, argeq₂]
                          simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right, maxlem₁]
                        all_goals apply h_none_lshr
                      all_goals apply h_none_lshr
                    all_goals apply h_none_lshr
                  all_goals apply h_none_lshr
                case ashr =>
                  have h_none_ashr :
                    ((LamTerm.ashr_equiv n (.pushBVCast .none arg₁) (.pushBVCast .none arg) (.pushBVCast (.ofNat n) arg))).maxEVarSucc =
                    (LamTerm.mkBvNatBinOp n (BitVecConst.bvshl n) arg₁ arg).maxEVarSucc :=
                    Eq.trans (LamTerm.congr_maxEVarSucc_ashr_equiv (n₁:=n) (n₂:=n)
                      (argeq₁ .none) (argeq .none) (argeq (.ofNat n)))
                      (by
                        dsimp [ashr_equiv, mkIte, mkEq, mkNatBinOp, mkBvUOp, mkBvBinOp, mkBvNatBinOp, maxEVarSucc, pushBVCast]
                        simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right]
                        apply maxlem₂)
                  cases arg
                  case app s''' fn' arg₂ =>
                    have leArg₂ := Nat.le_trans LamTerm.size_app_ge_size_arg leArg
                    have argeq₂ := fun ct => @IH ct _ leArg₂
                    cases fn'
                    case base b =>
                      cases b
                      case bvcst bvc =>
                        cases bvc
                        case bvtoNat m =>
                          dsimp [maxEVarSucc, pushBVCast]
                          cases m.ble n <;> dsimp [ashr_toNat_equiv_short, ashr_toNat_equiv_long, mkIte, mkEq, mkBvUOp, mkBvBinOp, maxEVarSucc] <;> rw [argeq₁, argeq₂]
                          simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right, maxlem₂]
                        all_goals apply h_none_ashr
                      all_goals apply h_none_ashr
                    all_goals apply h_none_ashr
                  all_goals apply h_none_ashr

theorem LamTerm.evarEquiv_pushBVCast : evarEquiv (fun t => pushBVCast ct t) := by
  intro t t' heq; cases heq; apply maxEVarSucc_pushBVCast

theorem LamEquiv.pushBVCast
  (wft : LamWF lval.toLamTyVal ⟨lctx, LamTerm.applyBVCast ct t, s⟩) :
  LamEquiv lval lctx s (t.applyBVCast ct) (t.pushBVCast ct) := by
  generalize tl' : t.size = l; have tl : t.size ≤ l := by cases tl'; exact .refl
  clear tl'
  induction l generalizing t s ct lctx <;>
    try apply False.elim (LamTerm.size_ne_zero (Nat.le_zero.mp tl))
  case succ l IH =>
    have hequivRefl : LamEquiv lval lctx s (LamTerm.applyBVCast ct t) (LamTerm.applyBVCast ct t) := by
      cases ct <;> apply refl wft
    cases t <;> try (cases ct <;> apply hequivRefl)
    case base b =>
      cases ct <;> try apply hequivRefl
      case ofNat m =>
        cases b <;> try apply hequivRefl
        case ncst nc =>
          cases nc <;> dsimp [LamTerm.pushBVCast, LamTerm.applyBVCast] <;> try apply LamEquiv.refl wft
          cases wft.getFn.getBase.getBvcst; apply bvofNat
    case lam s' body =>
      cases ct <;> try apply hequivRefl
      case none =>
        dsimp [LamTerm.pushBVCast, LamTerm.applyBVCast]
        cases wft
        case ofLam s'' wfBody =>
          apply ofLam; apply IH (ct:=.none) (t:=body) wfBody
          apply Nat.le_of_succ_le_succ tl
    case app s' fn arg =>
      have leFn : LamTerm.size fn ≤ l := Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_fn tl)
      have leArg : LamTerm.size arg ≤ l := Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
      cases ct
      case ofNat m =>
        cases wft.getFn.getBase.getBvcst
        have wfapp' := wft.getArg
        cases fn <;> try apply hequivRefl
        case base b =>
          cases b <;> try apply hequivRefl
          case bvcst bvc =>
            cases bvc <;> try apply hequivRefl
            case bvtoNat =>
              cases wfapp'.getFn.getBase.getBvcst
              have wfbv := wfapp'.getArg
              dsimp [LamTerm.applyBVCast, LamTerm.pushBVCast]
              apply trans (bvofNat_bvtoNat wfbv)
              apply congrArg (.ofBase (.ofBvzeroExtend _ _))
              apply IH (ct:=.none) (t:=arg) wfbv leArg
        case app s'' fn arg₁ =>
          cases fn <;> try (dsimp [LamTerm.pushBVCast]; apply refl wft)
          have wfl := wfapp'.getFn.getArg; have wfr := wfapp'.getArg
          have leArg₁ := Nat.le_trans LamTerm.size_app_ge_size_arg leFn
          case base b =>
            cases b <;> try (dsimp [LamTerm.pushBVCast]; apply refl wft)
            case ncst nc =>
              cases nc <;> dsimp [LamTerm.pushBVCast] <;> (try apply refl wft) <;>
                (try cases wfapp'.getFn.getFn.getBase.getNcst; dsimp [LamTerm.applyBVCast])
              case nadd =>
                apply trans (bvofNat_nadd wfl wfr)
                apply congr (congrArg (.ofBase (.ofBvadd _)) ?eql) ?eqr
                case eql => apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl) leArg₁
                case eqr => apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr) leArg
              case nsub =>
                apply trans (bvofNat_nsub wfl wfr)
                apply congrArg
                  (.ofApp _ (.ofApp _ (.ofBase (.ofIte _)) (.mkNatBinOp .ofNlt wfl wfr)) (.ofBase (.ofBvVal _ _)))
                  (congr (congrArg (.ofBase (.ofBvsub _)) ?eql) ?eqr)
                case eql => apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl) leArg₁
                case eqr => apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr) leArg
              case nmul =>
                apply trans (bvofNat_nmul wfl wfr)
                apply congr (congrArg (.ofBase (.ofBvmul _)) ?eql) ?eqr
                case eql => apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl) leArg₁
                case eqr => apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr) leArg
      case ofInt m => dsimp [LamTerm.pushBVCast]; apply refl wft
      case none =>
        have eFn := IH (ct:=.none) wft.getFn leFn
        have eArg := IH (ct:=.none) wft.getArg leArg
        have h_none_app := congr eFn eArg
        cases fn <;> try apply h_none_app
        case base b =>
          have h_none_app_base := congrArg wft.getFn eArg
          cases b <;> try apply h_none_app_base
          case bvcst bvc =>
            cases bvc <;> try apply h_none_app_base
            case bvofNat m =>
              cases wft.getFn.getBase.getBvcst; apply IH (ct:=.ofNat m) (t:=arg) wft leArg
            case bvofInt m =>
              cases wft.getFn.getBase.getBvcst; apply IH (ct:=.ofInt m) (t:=arg) wft leArg
        case app s'' fn arg₁ =>
          have leArg₁ := Nat.le_trans LamTerm.size_app_ge_size_arg leFn
          have eArg₁ := IH (ct:=.none) wft.getFn.getArg leArg₁
          cases fn <;> try apply h_none_app
          case base b =>
            cases b <;> try apply h_none_app
            case bvcst bvc =>
              cases bvc <;> try apply h_none_app
              case bvshOp n smt? shOp =>
                cases smt? <;> try apply h_none_app
                cases wft.getFn.getFn.getBase.getBvcst
                cases shOp
                case shl =>
                  have h_none_shl := trans
                    (shl_equiv wft.getFn.getArg wft.getArg)
                    (congr_shl_equiv eArg₁ eArg (IH (ct:=.ofNat _) (.mkBvofNat wft.getArg) leArg))
                  cases arg <;> try apply h_none_shl
                  case app s''' fn' arg₂ =>
                    have leArg₂ := Nat.le_trans LamTerm.size_app_ge_size_arg leArg
                    have eArg₂ := IH (ct:=.none) wft.getArg.getArg leArg₂
                    cases fn' <;> try apply h_none_shl
                    case base b =>
                      cases b <;> try apply h_none_shl
                      case bvcst bvc =>
                        cases bvc <;> try apply h_none_shl
                        case bvtoNat m =>
                          cases wft.getArg.getFn.getBase.getBvcst
                          dsimp [LamTerm.applyBVCast, LamTerm.pushBVCast]
                          cases hble : m.ble n <;> dsimp
                          case true =>
                            have hle := Nat.le_of_ble_eq_true hble
                            apply trans (shl_toNat_equiv_short wft.getFn.getArg wft.getArg.getArg hle) _
                            apply congr_shl_toNat_equiv_short eArg₁ eArg₂
                          case false =>
                            have hlt := Nat.lt_of_ble_eq_false hble
                            apply trans (shl_toNat_equiv_long wft.getFn.getArg wft.getArg.getArg hlt) _
                            apply congr_shl_toNat_equiv_long eArg₁ eArg₂
                case lshr =>
                  have h_none_lshr := trans
                    (lshr_equiv wft.getFn.getArg wft.getArg)
                    (congr_lshr_equiv eArg₁ eArg (IH (ct:=.ofNat _) (.mkBvofNat wft.getArg) leArg))
                  cases arg <;> try apply h_none_lshr
                  case app s''' fn' arg₂ =>
                    have leArg₂ := Nat.le_trans LamTerm.size_app_ge_size_arg leArg
                    have eArg₂ := IH (ct:=.none) wft.getArg.getArg leArg₂
                    cases fn' <;> try apply h_none_lshr
                    case base b =>
                      cases b <;> try apply h_none_lshr
                      case bvcst bvc =>
                        cases bvc <;> try apply h_none_lshr
                        case bvtoNat m =>
                          cases wft.getArg.getFn.getBase.getBvcst
                          dsimp [LamTerm.applyBVCast, LamTerm.pushBVCast]
                          cases hble : m.ble n <;> dsimp
                          case true =>
                            have hle := Nat.le_of_ble_eq_true hble
                            apply trans (lshr_toNat_equiv_short wft.getFn.getArg wft.getArg.getArg hle) _
                            apply congr_lshr_toNat_equiv_short eArg₁ eArg₂
                          case false =>
                            have hlt := Nat.lt_of_ble_eq_false hble
                            apply trans (lshr_toNat_equiv_long wft.getFn.getArg wft.getArg.getArg hlt) _
                            apply congr_lshr_toNat_equiv_long eArg₁ eArg₂
                case ashr =>
                  have h_none_ashr := trans
                    (ashr_equiv wft.getFn.getArg wft.getArg)
                    (congr_ashr_equiv eArg₁ eArg (IH (ct:=.ofNat _) (.mkBvofNat wft.getArg) leArg))
                  cases arg <;> try apply h_none_ashr
                  case app s''' fn' arg₂ =>
                    have leArg₂ := Nat.le_trans LamTerm.size_app_ge_size_arg leArg
                    have eArg₂ := IH (ct:=.none) wft.getArg.getArg leArg₂
                    cases fn' <;> try apply h_none_ashr
                    case base b =>
                      cases b <;> try apply h_none_ashr
                      case bvcst bvc =>
                        cases bvc <;> try apply h_none_ashr
                        case bvtoNat m =>
                          cases wft.getArg.getFn.getBase.getBvcst
                          dsimp [LamTerm.applyBVCast, LamTerm.pushBVCast]
                          cases hble : m.ble n <;> dsimp
                          case true =>
                            have hle := Nat.le_of_ble_eq_true hble
                            apply trans (ashr_toNat_equiv_short wft.getFn.getArg wft.getArg.getArg hle) _
                            apply congr_ashr_toNat_equiv_short eArg₁ eArg₂
                          case false =>
                            have hlt := Nat.lt_of_ble_eq_false hble
                            apply trans (ashr_toNat_equiv_long wft.getFn.getArg wft.getArg.getArg hlt) _
                            apply congr_ashr_toNat_equiv_long eArg₁ eArg₂

theorem LamGenConv.pushBVCast : LamGenConv lval (fun t => LamTerm.pushBVCast .none t) := by
  intros t₁ t₂ heq lctx rty wf; cases heq
  apply LamEquiv.pushBVCast (ct:=.none) wf

end Auto.Embedding.Lam
