import Auto.Embedding.LamConv
import Auto.Lib.NatExtra
import Std.Data.Int.Lemmas
import Std.Data.Fin.Lemmas

namespace Auto.Embedding.Lam

namespace BitVec

  open Std.BitVec

  theorem toNat_ofNat (n a : Nat) : (Std.BitVec.ofNat n a).toNat = a % (2 ^ n) := rfl

  theorem toNat_le (a : Std.BitVec n) : a.toNat < 2 ^ n := by
    rcases a with ⟨⟨_, isLt⟩⟩; exact isLt

  theorem eq_of_val_eq {a b : Std.BitVec n} (h : a.toNat = b.toNat) : a = b := by
    rcases a with ⟨⟨a, isLta⟩⟩; rcases b with ⟨⟨b, isLtb⟩⟩
    dsimp [Std.BitVec.toNat] at h; cases h; rfl

  theorem val_eq_of_eq {a b : Std.BitVec n} (h : a = b) : a.toNat = b.toNat := by
    cases h; rfl

  theorem eq_iff_val_eq {a b : Std.BitVec n} : a = b ↔ a.toNat = b.toNat :=
    Iff.intro val_eq_of_eq eq_of_val_eq

  theorem ne_of_val_ne {a b : Std.BitVec n} (h : a.toNat ≠ b.toNat) : a ≠ b := by
    intro h'; cases h'; apply False.elim (h rfl)

  theorem val_ne_of_ne {a b : Std.BitVec n} (h : a ≠ b) : a.toNat ≠ b.toNat := by
    intro h'; apply h; apply eq_of_val_eq h'

  theorem ne_iff_val_ne {a b : Std.BitVec n} : a ≠ b ↔ a.toNat ≠ b.toNat :=
    Iff.intro val_ne_of_ne ne_of_val_ne

  theorem shiftLeft_def (a : Std.BitVec n) (i : Nat) : a <<< i = a.shiftLeft i := rfl

  theorem smtshiftLeft_def (a : Std.BitVec n) (b : Std.BitVec m) : a <<< b = a <<< b.toNat := rfl

  theorem ushiftRight_def (a : Std.BitVec n) (i : Nat) : a >>> i = a.ushiftRight i := rfl

  theorem smtushiftRight_def (a : Std.BitVec n) (b : Std.BitVec m) : a >>> b = a >>> b.toNat := rfl

  theorem neg_def (a : Std.BitVec n) : -a = a.neg := rfl

  theorem sub_def (a b : Std.BitVec n) : a - b = a.sub b := rfl

  theorem toNat_shiftLeft {a : Std.BitVec n} (i : Nat) : (a <<< i).toNat = (a.toNat * (2 ^ i)) % (2 ^ n) := by
    rw [shiftLeft_def]; rcases a with ⟨⟨a, isLt⟩⟩
    dsimp [Std.BitVec.shiftLeft, Std.BitVec.toNat, Std.BitVec.ofNat, Fin.ofNat']
    rw [Nat.shiftLeft_eq]

  theorem toNat_ushiftRight {a : Std.BitVec n} (i : Nat) : (a >>> i).toNat = (a.toNat) / (2 ^ i) := by
    rw [ushiftRight_def]; rcases a with ⟨⟨a, isLt⟩⟩
    dsimp [ushiftRight, Std.BitVec.toNat, Std.BitVec.ofNat, Fin.ofNat']
    rw [Nat.mod_eq_of_lt, Nat.shiftRight_eq_div_pow]
    apply Nat.le_trans (Nat.succ_le_succ _) isLt
    rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_le_self

  theorem toNat_zeroExtend {a : Std.BitVec n} (i : Nat) : (a.zeroExtend i).toNat = a.toNat % (2 ^ i) := rfl

  theorem toNat_sub (a b : Std.BitVec n) : (a - b).toNat = (a.toNat + (2 ^ n - b.toNat)) % (2 ^ n) := rfl

  theorem toNat_neg (a : Std.BitVec n) : (-a).toNat = (2^n - a.toNat) % (2^n) := by
    rw [neg_def]; dsimp [Std.BitVec.neg]
    rw [← sub_def, toNat_sub, toNat_ofNat, Nat.zero_mod, Nat.zero_add]

  theorem shiftLeft_ge_length_eq_zero (a : Std.BitVec n) (i : Nat) : i ≥ n → a <<< i = 0#n := by
    intro h; apply eq_of_val_eq; rw [toNat_shiftLeft, toNat_ofNat]; apply Nat.mod_eq_zero_of_dvd
    have poweq : 2 ^ i = 2 ^ (i - n) * 2 ^ n := by rw [← Nat.pow_add, Nat.sub_add_cancel h]
    rw [poweq, ← Nat.mul_assoc, Nat.mul_comm _ (2^n)]; exact ⟨_, rfl⟩

  theorem ushiftRight_ge_length_eq_zero (a : Std.BitVec n) (i : Nat) : i ≥ n → a >>> i = 0#n := by
    intro h; apply eq_of_val_eq; rw [toNat_ushiftRight, toNat_ofNat]; apply (Nat.le_iff_div_eq_zero ?l).mpr ?r
    case l => apply Nat.pow_two_pos
    case r => apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem sshiftRight_ge_length_eq_msb (a : Std.BitVec n) (i : Nat) : i ≥ n → a.sshiftRight i =
    if a.msb then (1#n).neg else 0#n := by
    intro h; cases hmsb : a.msb <;> simp [sshiftRight, Std.BitVec.toInt, hmsb, Int.shiftRight_def]
    case false => dsimp [Std.BitVec.ofInt]; apply ushiftRight_ge_length_eq_zero _ _ h
    case true =>
      rw [← Int.subNatNat_eq_coe, Int.subNatNat_of_lt (toNat_le _)]
      simp [Std.BitVec.toInt, Std.BitVec.ofInt]
      have hzero : Nat.pred (2 ^ n - Std.BitVec.toNat a) >>> i = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; apply (Nat.le_iff_div_eq_zero (Nat.pow_two_pos _)).mpr
        rw [Nat.pred_lt_iff_le (Nat.pow_two_pos _)]
        apply Nat.le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_of_le_right (.step .refl) h)
      rw [hzero, Nat.zero_mod, Nat.sub_zero]; apply eq_of_val_eq
      rw [toNat_ofNat, ← neg_def, toNat_neg, toNat_ofNat]
      cases n <;> try rfl
      case succ =>
        rw [Nat.mod_eq_of_lt (a:=1)]
        apply @Nat.pow_le_pow_of_le_right 2 (.step .refl) 1 _ (Nat.succ_le_succ (Nat.zero_le _))

  theorem shiftRight_eq_zero_iff (a : Std.BitVec n) (b : Nat) : a >>> b = 0#n ↔ a.toNat < 2 ^ b := by
    rw [ushiftRight_def]; rcases a with ⟨⟨a, isLt⟩⟩; dsimp [ushiftRight, Std.BitVec.toNat]
    rw [eq_iff_val_eq, toNat_ofNat, toNat_ofNat, Nat.zero_mod, Nat.shiftRight_eq_div_pow]
    apply Iff.intro <;> intro h
    case mp =>
      rw [← Nat.dvd_iff_mod_eq_zero] at h; rcases h with ⟨cst, hdvd⟩
      rw [← Nat.div_add_mod a (2^b)] at isLt; rw [hdvd] at isLt
      rw [← Nat.mul_assoc, Nat.mul_comm _ (2^n), Nat.mul_assoc] at isLt
      have isLt' := Nat.eq_zero_of_mul_right_lt (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ _)) isLt)
      rw [Nat.mul_eq_zero] at isLt'; cases isLt'
      case inl h => apply False.elim (Nat.ne_zero_of_zero_lt (Nat.pow_two_pos _) h)
      case inr h => cases h; rw [Nat.mul_zero] at hdvd; apply (Nat.le_iff_div_eq_zero (Nat.pow_two_pos _)).mp hdvd
    case mpr => rw [(Nat.le_iff_div_eq_zero (Nat.pow_two_pos _)).mpr h]; rfl

  theorem ofNat_add (n a b : Nat) : (a + b)#n = a#n + b#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.add_mod]; rfl

  theorem ofNat_mod_pow2 (n a : Nat) : (a % (2 ^ n))#n = a#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; apply Nat.mod_mod

  theorem ofNat_mul (n a b : Nat) : (a * b)#n = a#n * b#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.mul_mod]; rfl

  theorem shl_equiv (a : Std.BitVec n) (b : Nat) : a <<< b = if (b < n) then (a <<< b#n) else 0 := by
    cases hdec : decide (b < n)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hnle, shiftLeft_ge_length_eq_zero _ _ (Nat.le_of_not_lt hnle)]; rfl
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, smtshiftLeft_def, toNat_ofNat, Nat.mod_eq_of_lt]
      apply Nat.le_trans hle (Nat.le_of_lt (Nat.le_pow .refl))

  theorem shl_equiv' (a : Std.BitVec n) (b : Nat) : a <<< b = Bool.ite' (b < n) (a <<< b#n) 0 := by
    have h := shl_equiv a b; rw [Bool.ite_simp] at h; exact h

  theorem shl_toNat_equiv_short (a : Std.BitVec n) (b : Std.BitVec m) (h : m ≤ n) : a <<< b.toNat = a <<< (zeroExtend n b) := by
    apply eq_of_val_eq; rw [toNat_shiftLeft, smtshiftLeft_def, toNat_shiftLeft, toNat_zeroExtend, Nat.mod_eq_of_lt (a:=Std.BitVec.toNat b)]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem shl_toNat_equiv_long (a : Std.BitVec n) (b : Std.BitVec m) (h : m > n) : a <<< b.toNat =
    if (b >>> (n#m)) = 0#m then a <<< (zeroExtend n b) else 0 := by
    have eqof : Std.BitVec.toNat n#m = n := by
      rw [toNat_ofNat]; apply Nat.mod_eq_of_lt
      apply Nat.le_trans (Nat.succ_le_succ (Nat.le_of_lt h)) (Nat.le_pow (Nat.le_refl _))
    cases hdec : decide ((b >>> (n#m)) = 0#m)
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

  theorem shl_toNat_equiv_long' (a : Std.BitVec n) (b : Std.BitVec m) (h : m > n) : a <<< b.toNat =
    Bool.ite' ((b >>> (n#m)) = 0#m) (a <<< (zeroExtend n b)) 0 := by
    have h := shl_toNat_equiv_long a b h; rw [Bool.ite_simp] at h; exact h

  theorem ushr_equiv (a : Std.BitVec n) (b : Nat) : a >>> b = if (b < n) then (a >>> b#n) else 0 := by
    cases hdec : decide (b < n)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hnle, ushiftRight_ge_length_eq_zero _ _ (Nat.le_of_not_lt hnle)]; rfl
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, smtushiftRight_def, toNat_ofNat, Nat.mod_eq_of_lt]
      apply Nat.le_trans hle (Nat.le_of_lt (Nat.le_pow .refl))

  theorem ushr_equiv' (a : Std.BitVec n) (b : Nat) : a >>> b = Bool.ite' (b < n) (a >>> b#n) 0 := by
    have h := ushr_equiv a b; rw [Bool.ite_simp] at h; exact h

  theorem ushr_toNat_equiv_short (a : Std.BitVec n) (b : Std.BitVec m) (h : m ≤ n) : a >>> b.toNat = a >>> (zeroExtend n b) := by
    apply eq_of_val_eq; rw [toNat_ushiftRight, smtushiftRight_def, toNat_ushiftRight, toNat_zeroExtend, Nat.mod_eq_of_lt]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem ushr_toNat_equiv_long (a : Std.BitVec n) (b : Std.BitVec m) (h : m > n) : a >>> b.toNat =
    if (b >>> (n#m)) = 0#m then a >>> (zeroExtend n b) else 0 := by
    have eqof : Std.BitVec.toNat n#m = n := by
      rw [toNat_ofNat]; apply Nat.mod_eq_of_lt
      apply Nat.le_trans (Nat.succ_le_succ (Nat.le_of_lt h)) (Nat.le_pow (Nat.le_refl _))
    cases hdec : decide ((b >>> (n#m)) = 0#m)
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

  theorem ushr_toNat_equiv_long' (a : Std.BitVec n) (b : Std.BitVec m) (h : m > n) : a >>> b.toNat =
    Bool.ite' ((b >>> (n#m)) = 0#m) (a >>> (zeroExtend n b)) 0 := by
    have h := ushr_toNat_equiv_long a b h; rw [Bool.ite_simp] at h; exact h

  theorem sshr_equiv (a : Std.BitVec n) (b : Nat) : a.sshiftRight b = if (b < n) then (a.sshiftRight (b#n).toNat) else (if a.msb then (1#n).neg else 0#n) := by
    cases hdec : decide (b < n)
    case false =>
      have hnle := of_decide_eq_false hdec
      rw [Bool.ite_eq_false _ _ _ hnle, sshiftRight_ge_length_eq_msb _ _ (Nat.le_of_not_lt hnle)]
    case true =>
      have hle := of_decide_eq_true hdec
      rw [Bool.ite_eq_true _ _ _ hle, toNat_ofNat, Nat.mod_eq_of_lt]
      apply Nat.le_trans hle (Nat.le_of_lt (Nat.le_pow .refl))

  theorem sshr_toNat_equiv_short (a : Std.BitVec n) (b : Std.BitVec m) (h : m ≤ n) : a.sshiftRight b.toNat = a.sshiftRight (zeroExtend n b).toNat := by
    apply eq_of_val_eq; rw [toNat_zeroExtend, Nat.mod_eq_of_lt]
    apply Nat.le_trans (toNat_le _) (Nat.pow_le_pow_of_le_right (.step .refl) h)

  theorem sshr_toNat_equiv_long (a : Std.BitVec n) (b : Std.BitVec m) (h : m > n) : a.sshiftRight b.toNat =
    if (b >>> (n#m)) = 0#m then a.sshiftRight (zeroExtend n b).toNat else (if a.msb then (1#n).neg else 0#n) := by
    have eqof : Std.BitVec.toNat n#m = n := by
      rw [toNat_ofNat]; apply Nat.mod_eq_of_lt
      apply Nat.le_trans (Nat.succ_le_succ (Nat.le_of_lt h)) (Nat.le_pow (Nat.le_refl _))
    cases hdec : decide ((b >>> (n#m)) = 0#m)
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

  theorem sshr_toNat_equiv_long' (a : Std.BitVec n) (b : Std.BitVec m) (h : m > n) : a.sshiftRight b.toNat =
    Bool.ite' ((b >>> (n#m)) = 0#m) (a.sshiftRight (zeroExtend n b).toNat) (Bool.ite' a.msb (1#n).neg 0#n) := by
    have h := sshr_toNat_equiv_long a b h; rw [Bool.ite_simp] at h; exact h

end BitVec

theorem LamEquiv.bvofNat :
  LamEquiv lval lctx (.base (.bv n)) (.mkBvofNat n (.mkNatVal i)) (.base (.bvVal' n i)) :=
  ⟨.mkBvofNat (.ofBase (.ofNatVal' i)), .ofBase (.ofBvVal' n i), fun _ => rfl⟩

theorem LamEquiv.bvofNat_bvtoNat
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base (.bv n)⟩) :
  LamEquiv lval lctx (.base (.bv m))
    (.mkBvofNat m (.mkBvUOp n (.bvtoNat n) t))
    (.app (.base (.bv n)) (.base (.bvzeroExtend' n m)) t) :=
  ⟨.mkBvofNat (.mkBvUOp (.ofBvtoNat n) wft),
   .ofApp _ (.ofBase (.ofBvzeroExtend' n m)) wft, fun lctxTerm => rfl⟩

theorem LamEquiv.bvofNat_nadd
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nadd a b))
    (.mkBvBinOp n (.bvadd n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNadd wfa wfb),
   .mkBvBinOp (.ofBvadd _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
      apply GLift.down.inj; apply BitVec.ofNat_add⟩

theorem LamEquiv.bvofNat_nmul
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nmul a b))
    (.mkBvBinOp n (.bvmul n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNmul wfa wfb),
   .mkBvBinOp (.ofBvmul _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
      apply GLift.down.inj; apply BitVec.ofNat_mul⟩

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
      .app (.base (.bv m)) (.base (.bvzeroExtend' m n)) (pushBVCast .none arg)
    | .app _ (.app _ (.base (.ncst .nadd)) lhs) rhs =>
      mkBvBinOp n (.bvadd n) (pushBVCast (.ofNat n) lhs) (pushBVCast (.ofNat n) rhs)
    | .app _ (.app _ (.base (.ncst .nmul)) lhs) rhs =>
      mkBvBinOp n (.bvmul n) (pushBVCast (.ofNat n) lhs) (pushBVCast (.ofNat n) rhs)
    | _ => mkBvofNat n t
  -- Not implemented
  | .ofInt n => mkBvofInt n t
  | .none =>
    match t with
    | .lam s body => .lam s (pushBVCast .none body)
    | .app s fn arg =>
      match fn with
      | .base (.bvcst (.bvofNat n)) => pushBVCast (.ofNat n) arg
      | .base (.bvcst (.bvofInt n)) => pushBVCast (.ofInt n) arg
      | _ => .app s (pushBVCast .none fn) (pushBVCast .none arg)
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
              cases nc <;> (try apply Nat.max_zero_left) <;> (
                dsimp [pushBVCast, maxEVarSucc]
                rw [IH (Nat.le_trans LamTerm.size_app_ge_size_arg leFn), IH leArg])
      case ofInt m => apply Nat.max_zero_left
      case none =>
        dsimp [pushBVCast]
        have fneq : ∀ ct, maxEVarSucc (pushBVCast ct fn) = maxEVarSucc fn := by
          intro ct; apply IH leFn
        have argeq : ∀ ct, maxEVarSucc (pushBVCast ct arg) = maxEVarSucc arg := by
          intro ct; apply IH leArg
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
      cases ct <;> apply LamEquiv.refl wft
    cases t <;> try (cases ct <;> apply hequivRefl)
    case base b =>
      cases ct <;> try apply hequivRefl
      case ofNat m =>
        cases b <;> try apply hequivRefl
        case ncst nc =>
          cases nc <;> dsimp [LamTerm.pushBVCast, LamTerm.applyBVCast] <;> try apply LamEquiv.refl wft
          cases wft.getFn.getBase.getBvcst; apply LamEquiv.bvofNat
    case lam s' body =>
      cases ct <;> try apply hequivRefl
      case none =>
        dsimp [LamTerm.pushBVCast, LamTerm.applyBVCast]
        cases wft
        case ofLam s'' wfBody =>
          apply LamEquiv.ofLam; apply IH (ct:=.none) (t:=body) wfBody
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
              apply LamEquiv.trans (LamEquiv.bvofNat_bvtoNat wfbv)
              apply LamEquiv.congrArg (.ofBase (.ofBvzeroExtend' _ _))
              apply IH (ct:=.none) (t:=arg) wfbv leArg
        case app s'' fn arg₁ =>
          cases fn <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
          have wfl := wfapp'.getFn.getArg; have wfr := wfapp'.getArg
          have leArg₁ := Nat.le_trans LamTerm.size_app_ge_size_arg leFn
          case base b =>
            cases b <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
            case ncst nc =>
              cases nc <;> dsimp [LamTerm.pushBVCast] <;> (try apply LamEquiv.refl wft) <;>
                (try cases wfapp'.getFn.getFn.getBase.getNcst; dsimp [LamTerm.applyBVCast])
              case nadd =>
                apply LamEquiv.trans (LamEquiv.bvofNat_nadd wfl wfr)
                apply LamEquiv.congr (LamEquiv.congrArg (.ofBase (.ofBvadd' _)) ?eql) ?eqr
                case eql => apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl) leArg₁
                case eqr => apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr) leArg
              case nmul =>
                apply LamEquiv.trans (LamEquiv.bvofNat_nmul wfl wfr)
                apply LamEquiv.congr (LamEquiv.congrArg (.ofBase (.ofBvmul' _)) ?eql) ?eqr
                case eql => apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl) leArg₁
                case eqr => apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr) leArg
      case ofInt m => dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft
      case none =>
        have eFn := IH (ct:=.none) wft.getFn leFn
        have eArg := IH (ct:=.none) wft.getArg leArg
        have h_none_app := LamEquiv.congr eFn eArg
        cases fn <;> try apply h_none_app
        case base b =>
          have h_none_app_base := LamEquiv.congrArg wft.getFn eArg
          cases b <;> try apply h_none_app_base
          case bvcst bvc =>
            cases bvc <;> try apply h_none_app_base
            case bvofNat m =>
              cases wft.getFn.getBase.getBvcst; apply IH (ct:=.ofNat m) (t:=arg) wft leArg
            case bvofInt m =>
              cases wft.getFn.getBase.getBvcst; apply IH (ct:=.ofInt m) (t:=arg) wft leArg

theorem LamGenConv.pushBVCast : LamGenConv lval (fun t => LamTerm.pushBVCast .none t) := by
  intros t₁ t₂ heq lctx rty wf; cases heq
  apply LamEquiv.pushBVCast (ct:=.none) wf

end Auto.Embedding.Lam
