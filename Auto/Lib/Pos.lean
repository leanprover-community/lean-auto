import Auto.MathlibEmulator

set_option linter.unusedVariables false

namespace Auto

inductive Pos where
  | xH : Pos
  | xO : Pos → Pos
  | xI : Pos → Pos
deriving Inhabited, Hashable, Lean.ToExpr

namespace Pos

abbrev one := xH

def toNat' : Pos → Nat
| xH => 1
| xO p' => p'.toNat' * 2
| xI p' => p'.toNat' * 2 + 1

def toNat (p : Pos) := Nat.pred (toNat' p)

theorem toNat'_not_zero (p : Pos) : toNat' p ≠ 0 := by
  induction p
  case xH => intro H; contradiction
  case xO p' IH =>
    simp [toNat']; intro H
    rw [Nat.mul_eq_zero] at H
    cases H
    case inl H' => revert H'; exact IH
    case inr H' => cases H'
  case xI p' _ =>
    simp [toNat']

private theorem ofNat'WFAux (n n' : Nat) : n = n' + 2 → n / 2 < n := by
  intro H; apply Nat.div_lt_self
  case hLtN =>
    cases n;
    contradiction;
    apply Nat.succ_le_succ; apply Nat.zero_le
  case hLtK => apply Nat.le_refl

def ofNat'WF (n : Nat) :=
  match h : n with
  | 0 => xH
  | 1 => xH
  | _ + 2 =>
    match n % 2 with
    | 0 => .xO (ofNat'WF (n / 2))
    | _ => .xI (ofNat'WF (n / 2))
decreasing_by rw [h]; apply ofNat'WFAux _ _ rfl

def ofNat'WF.inductionOn.{u}
  {motive : Nat → Sort u} (x : Nat)
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : motive x :=
  match x with
  | 0 => base₀
  | 1 => base₁
  | x' + 2 => ind x' (inductionOn ((x' + 2) / 2) ind base₀ base₁)
decreasing_by apply ofNat'WFAux _ _ rfl

@[irreducible] def ofNat'WF.induction
  {motive : Nat → Sort u}
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : ∀ x, motive x :=
  fun x => ofNat'WF.inductionOn x ind base₀ base₁

theorem ofNat'WF.succSucc (n : Nat) :
  ofNat'WF (n + 2) =
    match (n + 2) % 2 with
    | 0 => .xO (ofNat'WF ((n + 2) / 2))
    | _ => .xI (ofNat'WF ((n + 2) / 2)) := by
  rw [ofNat'WF]

theorem ofNat'WF.double_xO (n : Nat) :
  n ≠ 0 → ofNat'WF (n * 2) = xO (ofNat'WF n) :=
  match n with
  | 0 => by intro H; contradiction
  | 1 => fun _ => by simp [ofNat'WF]
  | n' + 2 => fun _ => by
    rw [Nat.mul_comm, Nat.mul_add];
    rw [ofNat'WF.succSucc];
    have heq : (2 * n' + 2 + 2) % 2 = 0 := by
      rw [Nat.add_mod_right]; rw [Nat.add_mod_right]
      rw [Nat.mul_mod]; simp
    rw [heq]; simp

theorem ofNat'WF.doubleSucc_xI (n : Nat) :
  n ≠ 0 → ofNat'WF ((n * 2) + 1) = xI (ofNat'WF n) :=
  match n with
  | 0 => by intro H; contradiction
  | 1 => fun _ => by simp [ofNat'WF]
  | n' + 2 => fun _ => by
    rw [Nat.mul_comm, Nat.mul_add];
    have : (2 * n' + 2 * 2 + 1) = (2 * n') + 3 + 2 := rfl
    rw [ofNat'WF.succSucc];
    have heq : (2 * n' + 3 + 2) % 2 = 1 := by
      rw [Nat.add_mod_right]; rw [Nat.add_mod]
      rw [Nat.mul_mod]; simp
    rw [heq]; simp
    have heq' : ((2 * n' + 3) / 2) + 1 = n' + 2 := by
      apply congrArg (f := fun x => Nat.add x 1); rw [Nat.add_comm];
      rw [Nat.add_mul_div_left _ _ (by simp)]; rw [Nat.add_comm]
    rw [heq']

theorem ofNat'WF_toNat' (p : Pos) : ofNat'WF (toNat' p) = p := by
  induction p
  case xH => rw [toNat', ofNat'WF]
  case xO p' IH =>
    dsimp [toNat'];
    rw [ofNat'WF.double_xO];
    rw [IH]; apply toNat'_not_zero
  case xI p' IH =>
    dsimp [toNat'];
    rw [ofNat'WF.doubleSucc_xI];
    rw [IH]; apply toNat'_not_zero

theorem toNat'_ofNat'WF (n : Nat) : n ≠ 0 → toNat' (ofNat'WF n) = n := by
  revert n; apply ofNat'WF.induction
  case base₀ => intro H; contradiction
  case base₁ => intro _; rw [ofNat'WF, toNat']
  case ind =>
    intro x IH _
    have hne : (x + 2) / 2 ≠ 0 := by
      rw [Nat.add_div_right]; simp; simp
    have IH' := IH hne
    rw [ofNat'WF.succSucc];
    have heq : (x + 2) / 2 = Nat.succ (x / 2) := Nat.add_div_right _ (by simp)
    rw [heq] at IH'
    match h : (x + 2) % 2 with
    | 0 =>
      simp [toNat']; rw [IH'];
      rw [← Nat.mod_add_div (x + 2) 2];
      rw [h]; simp; apply Nat.mul_comm
    | 1 =>
      simp [toNat']; rw [IH'];
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

def ofNat'RD (rd : Nat) (n : Nat) :=
  match rd with
  | 0 => xH
  | .succ rd' =>
    match n with
    | 0 => xH
    | 1 => xH
    | _ =>
      match Nat.mod n 2 with
      | 0 => .xO (ofNat'RD rd' (Nat.div n 2))
      | _ => .xI (ofNat'RD rd' (Nat.div n 2))

theorem ofNat'.equivAux (rd n : Nat) : rd ≥ n → ofNat'WF n = ofNat'RD rd n := by
  induction rd generalizing n  <;> intro H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero]; rw [ofNat'WF, ofNat'RD]
  case succ rd' IH =>
    dsimp [ofNat'RD]
    match n with
    | 0 => rw [ofNat'WF]
    | 1 => rw [ofNat'WF]
    | n' + 2 =>
      rw [ofNat'WF.succSucc]; simp;
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

def ofNat' n := ofNat'RD n n

theorem ofNat'.equiv (n : Nat) : ofNat'WF n = ofNat' n :=
  ofNat'.equivAux n n (Nat.le_refl _)

def ofNat n := ofNat' (.succ n)

def reprPrec (p : Pos) (_ : Nat) : Lean.Format :=
  f!"Pos.ofNat {p.toNat}"

instance : Repr Pos where
  reprPrec := Pos.reprPrec

def beq : (p q : Pos) → Bool
| xH,    xH    => true
| xO p', xO q' => p'.beq q'
| xI p', xI q' => p'.beq q'
| _,     _     => false

theorem beq_refl {p : Pos} : p.beq p = true := by
  induction p
  case xH => rfl
  case xO p' IH => simp [beq, IH]
  case xI p' IH => simp [beq, IH]

theorem eq_of_beq_eq_true : {p q : Pos} → p.beq q = true → p = q
| xH,    xH    => fun _ => rfl
| xH,    xO  _ => fun H => by cases H
| xH,    xI _  => fun H => by cases H
| xO _,  xH    => fun H => by cases H
| xO p', xO q' => fun H => by dsimp [beq] at H; rw [eq_of_beq_eq_true H]
| xO p', xI q' => fun H => by cases H
| xI _,  xH    => fun H => by cases H
| xI _,  xO _  => fun H => by cases H
| xI p', xI q' => fun H => by dsimp [beq] at H; rw [eq_of_beq_eq_true H]

theorem ne_of_beq_eq_false {p q : Pos} : p.beq q = false → p ≠ q :=
  match he : p.beq q with
  | true => fun h => by cases h
  | false => fun _ he' => by cases he'; rw [beq_refl] at he; cases he

instance : BEq Pos where
  beq := beq

instance : LawfulBEq Pos where
  eq_of_beq := eq_of_beq_eq_true
  rfl := beq_refl

def succ (p : Pos) : Pos :=
  match p with
  | xH     => .xO .xH
  | .xO p' => .xI p'
  | .xI p' => .xO (succ p')

def predXO : Pos → Pos
| xH   => xH
| xO p => xI (predXO p)
| xI p => xI (xO p)

def pred (p : Pos) : Pos :=
  match p with
  | xH      => .xH
  | xO p'  => p'.predXO
  | xI p'  => .xO p'

theorem succ_neq (p : Pos) : p ≠ succ p := by
  cases p <;> intro h <;> contradiction

theorem pred_neq (p : Pos) : p ≠ .xH → p ≠ pred p := by
  cases p <;> intro h₁ h₂ <;> try contradiction
  case xO p' => cases p' <;> try contradiction

theorem predXO_spec (p : Pos) : p.predXO = (xO p).pred := by
  cases p <;> rfl

theorem succ_predXO (p : Pos) : succ (predXO p) = xO p := by
  induction p <;> try rfl
  case xO a IH => simp [predXO, succ, IH]

theorem predXO_succ (p : Pos) : predXO (succ p) = xI p := by
  induction p <;> try rfl
  case xI a IH => simp [predXO, succ, IH]

theorem double_succ (p : Pos) : xO (succ p) = succ (succ (xO p)) := by
  cases p <;> rfl

theorem predXO_neq_xO (p : Pos) : predXO p ≠ xO p := by
  cases p <;> intro h <;> contradiction

theorem succ_not_1 (p : Pos) : succ p ≠ .one := by
  cases p <;> intro h <;> try contradiction

theorem pred_succ_eq (p : Pos) : pred (.succ p) = p := by
  cases p <;> try rfl
  case xI p' => apply predXO_succ

theorem succ_pred_xO (p : Pos) : succ (pred (xO p)) = xO p := by
  induction p <;> try rfl
  case xO p' IH =>
    dsimp [succ, pred, predXO]; dsimp [succ, pred] at IH; rw [IH]

theorem succ_pred_xI (p : Pos) : succ (pred (xI p)) = xI p := by
  cases p <;> rfl

theorem neq_XH_succ_pred_eq (p : Pos) : p ≠ .xH → succ (pred p) = p := by
  cases p <;> intro h
  case xH => contradiction
  case xO _ => apply succ_pred_xO
  case xI _ => apply succ_pred_xI

theorem succ_inj (p q : Pos) : succ p = succ q → p = q := fun H =>
  pred_succ_eq p ▸ pred_succ_eq q ▸ (congrArg _ H : pred (succ p) = pred (succ q))

end Pos

end Auto
