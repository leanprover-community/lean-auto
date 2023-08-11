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

private partial def Pos.ofNatAux (n : Nat) :=
  match n with
  | 0 => xH
  | 1 => xH
  | _ =>
    match n % 2 with
    | 0 => .xO (Pos.ofNatAux (n / 2))
    | _ => .xI (Pos.ofNatAux (n / 2))

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

