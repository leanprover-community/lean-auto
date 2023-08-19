import Std.Data.Nat.Lemmas

namespace Auto.BinNat

inductive Pos where
  | xH : Pos
  | xO : Pos → Pos
  | xI : Pos → Pos
deriving Inhabited

abbrev Pos.one := xH

inductive Bin where
  | zero : Bin
  | pos : Pos → Bin

abbrev Bin.one := pos .xH

def Pos.toNat : Pos → Nat
| xH => 1
| xO p' => p'.toNat * 2
| xI p' => p'.toNat * 2 + 1

theorem Pos.toNat_not_zero (p : Pos) : Pos.toNat p ≠ 0 := by
  induction p
  case xH => intro H; contradiction
  case xO p' IH =>
    simp [Pos.toNat]; intro H
    rw [Nat.mul_eq_zero] at H
    cases H
    case inl H' => revert H'; exact IH
    case inr H' => cases H'
  case xI p' _ =>
    simp [Pos.toNat] 

private theorem Pos.ofNatWFAux (n n' : Nat) : n = n' + 2 → n / 2 < n := by
  intro H; apply Nat.div_lt_self
  case hLtN =>
    cases n;
    contradiction;
    apply Nat.succ_le_succ; apply Nat.zero_le
  case hLtK => apply Nat.le_refl

def Pos.ofNatWF (n : Nat) :=
  match h : n with
  | 0 => xH
  | 1 => xH
  | _ + 2 =>
    match n % 2 with
    | 0 => .xO (Pos.ofNatWF (n / 2))
    | _ => .xI (Pos.ofNatWF (n / 2))
decreasing_by apply Pos.ofNatWFAux; assumption

theorem Pos.ofNatWF.inductionOn.{u}
  {motive : Nat → Sort u} (x : Nat)
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : motive x :=
  match h : x with
  | 0 => base₀
  | 1 => base₁
  | x' + 2 => ind x' (inductionOn ((x' + 2) / 2) ind base₀ base₁)
decreasing_by apply Pos.ofNatWFAux; rfl

theorem Pos.ofNatWF.induction
  {motive : Nat → Sort u}
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : ∀ x, motive x :=
  fun x => Pos.ofNatWF.inductionOn x ind base₀ base₁

theorem Pos.ofNatWF.succSucc (n : Nat) :
  Pos.ofNatWF (n + 2) =
    match (n + 2) % 2 with
    | 0 => .xO (Pos.ofNatWF ((n + 2) / 2))
    | _ => .xI (Pos.ofNatWF ((n + 2) / 2)) := rfl

theorem Pos.ofNatWF.double_xO (n : Nat) :
  n ≠ 0 → Pos.ofNatWF (n * 2) = xO (Pos.ofNatWF n) :=
  match n with
  | 0 => by intro H; contradiction
  | 1 => fun _ => by simp [ofNatWF]
  | n' + 2 => fun H => by
    simp; rw [Nat.mul_comm, Nat.mul_add];
    rw [Pos.ofNatWF.succSucc];
    have heq : (2 * n' + 2 + 2) % 2 = 0 := by
      rw [Nat.add_mod_right]; rw [Nat.add_mod_right]
      rw [Nat.mul_mod]; simp
    rw [heq]; simp

theorem Pos.ofNatWF.doubleSucc_xI (n : Nat) :
  n ≠ 0 → Pos.ofNatWF ((n * 2) + 1) = xI (Pos.ofNatWF n) :=
  match n with
  | 0 => by intro H; contradiction
  | 1 => fun _ => by simp [ofNatWF]
  | n' + 2 => fun H => by
    simp; rw [Nat.mul_comm, Nat.mul_add];
    have : (2 * n' + 2 * 2 + 1) = (2 * n') + 3 + 2 := rfl
    rw [Pos.ofNatWF.succSucc];
    have heq : (2 * n' + 3 + 2) % 2 = 1 := by
      rw [Nat.add_mod_right]; rw [Nat.add_mod]
      rw [Nat.mul_mod]; simp
    rw [heq]; simp
    have heq' : Nat.succ ((2 * n' + 3) / 2) = n' + 2 := by
      apply congrArg; rw [Nat.add_comm];
      rw [Nat.add_mul_div_left _ _ (by simp)]; rw [Nat.add_comm]; rfl;
    rw [heq']

theorem Pos.ofNatWF_toNat (p : Pos) : Pos.ofNatWF (Pos.toNat p) = p := by
  induction p
  case xH => rfl
  case xO p' IH =>
    dsimp [Pos.toNat];
    rw [Pos.ofNatWF.double_xO];
    rw [IH]; apply Pos.toNat_not_zero
  case xI p' IH =>
    dsimp [Pos.toNat];
    rw [Pos.ofNatWF.doubleSucc_xI];
    rw [IH]; apply Pos.toNat_not_zero

theorem Pos.toNat_ofNatWF (n : Nat) : n ≠ 0 → Pos.toNat (Pos.ofNatWF n) = n := by
  revert n; apply Pos.ofNatWF.induction
  case base₀ => intro H; contradiction
  case base₁ => intro H; rfl
  case ind =>
    intro x IH _
    have hne : (x + 2) / 2 ≠ 0 := by
      rw [Nat.add_div_right]; simp; simp
    have IH' := IH hne
    rw [ofNatWF.succSucc];
    have heq : (x + 2) / 2 = Nat.succ (x / 2) := Nat.add_div_right _ (by simp)
    rw [heq] at IH'
    match h : (x + 2) % 2 with
    | 0 =>
      simp [toNat]; rw [IH'];
      rw [← Nat.mod_add_div (x + 2) 2];
      rw [h]; simp; apply Nat.mul_comm
    | 1 =>
      simp [toNat]; rw [IH'];
      rw [Nat.add_mul _ 1]; simp
      calc
        _ = 2 * (x / 2) + x % 2 := by
          rw [Nat.add_mod_right] at h
          rw [h]; rw [Nat.mul_comm]
        _ = _ := by apply Nat.div_add_mod
    | w' + 2 =>
      have h' := Nat.not_lt_of_le (Nat.le_of_eq (Eq.symm h))
      apply False.elim; apply h'
      apply Nat.le_trans (m:=2)
      apply Nat.mod_lt; simp
      apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le

def Pos.ofNatRD (rd : Nat) (n : Nat) :=
  match rd with
  | 0 => xH
  | .succ rd' =>
    match n with
    | 0 => xH
    | 1 => xH
    | _ =>
      match Nat.mod n 2 with
      | 0 => .xO (Pos.ofNatRD rd' (Nat.div n 2))
      | _ => .xI (Pos.ofNatRD rd' (Nat.div n 2))

theorem Pos.ofNat.equivAux (rd n : Nat) : rd ≥ n → Pos.ofNatWF n = Pos.ofNatRD rd n := by
  revert n; induction rd <;> intros n H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero]; rfl
  case succ rd' IH =>
    dsimp [ofNatRD]
    match n with
    | 0 => rfl
    | 1 => rfl
    | n' + 2 =>
      rw [Pos.ofNatWF.succSucc]; simp;
      have heq' : Nat.mod (n' + 2) 2 = n' % 2 := by
        suffices (n' + 2) % 2 = n' % 2 by exact this
        rw [Nat.add_mod_right]
      have heqDiv : Nat.div (n' + 2) 2 = Nat.succ (n' / 2) := by
        suffices (n' + 2) / 2 = Nat.succ (n' / 2) by exact this
        rw [Nat.add_div_right]; simp
      rw [IH, heq', heqDiv];
      apply Nat.le_trans (m := n' + 1)
      case a.a => apply Nat.succ_le_succ; apply Nat.div_le_self
      case a.a => apply Nat.le_of_succ_le_succ H

def Pos.ofNat n := Pos.ofNatRD n n

theorem Pos.ofNat.equiv (n : Nat) : Pos.ofNatWF n = Pos.ofNat n :=
  Pos.ofNat.equivAux n n (Nat.le_refl _)

def Bin.ofNat (n : Nat) : Bin :=
  match n with
  | 0 => zero
  | _ => pos (Pos.ofNat n)

def Pos.beq : (p q : Pos) → Bool
| xH,    xH    => true
| xO p', xO q' => p'.beq q'
| xI p', xI q' => p'.beq q'
| _,     _     => false

theorem Pos.beq_refl (p : Pos) : p.beq p = true := by
  induction p
  case xH => rfl
  case xO p' IH => simp [beq, IH]
  case xI p' IH => simp [beq, IH]

theorem Pos.beq_eq : (p q : Pos) → p.beq q = true → p = q
| xH,    xH    => fun _ => rfl
| xH,    xO  _ => fun H => by cases H
| xH,    xI _  => fun H => by cases H
| xO _,  xH    => fun H => by cases H
| xO p', xO q' => fun H => by simp [beq, Pos.beq_eq p' q' H]
| xO p', xI q' => fun H => by cases H
| xI _,  xH    => fun H => by cases H
| xI _,  xO _  => fun H => by cases H
| xI p', xI q' => fun H => by simp [beq, Pos.beq_eq p' q' H]

instance : BEq Pos where
  beq := Pos.beq

def Pos.succ (p : Pos) : Pos :=
  match p with
  | xH     => .xO .xH
  | .xO p' => .xI p'
  | .xI p' => .xO (Pos.succ p')

def Pos.predXO : Pos → Pos
| xH   => xH
| xO p => xI (predXO p)
| xI p => xI (xO p)

def Pos.pred (p : Pos) : Pos :=
  match p with
  | xH      => .xH
  | xO p'  => p'.predXO
  | xI p'  => .xO p'

def Bin.ofPredPos : (p : Pos) → Bin
| .xH    => zero
| .xO p' => pos (.predXO p')
| .xI p' => pos (.xO p')

theorem Pos.succ_neq (p : Pos) : p ≠ Pos.succ p := by
  cases p <;> intro h <;> contradiction

theorem Pos.pred_neq (p : Pos) : p ≠ .xH → p ≠ Pos.pred p := by
  cases p <;> intro h₁ h₂ <;> try contradiction
  case xO p' => cases p' <;> try contradiction

theorem Pos.predXO_spec (p : Pos) : p.predXO = (xO p).pred := by
  cases p <;> rfl

theorem Pos.succ_predXO (p : Pos) : succ (predXO p) = xO p := by
  induction p <;> try rfl
  case xO a IH => simp [predXO, succ, IH]

theorem Pos.predXO_succ (p : Pos) : predXO (succ p) = xI p := by
  induction p <;> try rfl
  case xI a IH => simp [predXO, succ, IH]

theorem Pos.double_succ (p : Pos) : xO (succ p) = succ (succ (xO p)) := by
  cases p <;> rfl

theorem Pos.predXO_neq_xO (p : Pos) : predXO p ≠ xO p := by
  cases p <;> intro h <;> contradiction

theorem succ_not_1 (p : Pos) : Pos.succ p ≠ .one := by
  cases p <;> intro h <;> try contradiction

theorem Pos.pred_succ_eq (p : Pos) : Pos.pred (.succ p) = p := by
  cases p <;> try rfl
  case xI p' => apply predXO_succ

theorem Pos.succ_pred_xO (p : Pos) : succ (pred (xO p)) = xO p := by
  induction p <;> try rfl
  case xO p' IH =>
    dsimp [succ, pred]; dsimp [succ, pred] at IH; rw [IH]

theorem Pos.succ_pred_xI (p : Pos) : succ (pred (xI p)) = xI p := by
  cases p <;> rfl

theorem Pos.neq_XH_succ_pred_eq (p : Pos) : p ≠ .xH → Pos.succ (Pos.pred p) = p := by
  cases p <;> intro h
  case xH => contradiction
  case xO _ => apply Pos.succ_pred_xO
  case xI _ => apply Pos.succ_pred_xI

theorem Pos.succ_inj (p q : Pos) : Pos.succ p = Pos.succ q → p = q := fun H =>
  Pos.pred_succ_eq p ▸ Pos.pred_succ_eq q ▸ (congrArg _ H : pred (succ p) = pred (succ q))

end Auto.BinNat