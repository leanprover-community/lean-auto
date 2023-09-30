import Auto.Embedding.LamConv

namespace Auto.Embedding.Lam

theorem eq_not_of_ne (h : a ≠ b) : a = (¬ b) :=
  propext (Iff.intro
    (fun ha hb => h (Eq.trans (eq_true ha) (eq_true hb).symm))
    (fun nb => Classical.byContradiction (fun na => h (Eq.trans (eq_false na) (eq_false nb).symm))))

theorem ne_of_eq_not (h : a = (¬ b)) : a ≠ b := fun h' =>
  have hb : b := Classical.byContradiction (fun nb => nb (Eq.mp h' (Eq.mp h.symm nb)))
  have hnb : ¬ b := Eq.mp h (Eq.mp h'.symm hb)
  hnb hb

def LamTerm.equalize (t : LamTerm) : LamTerm := .mkEq (.base .prop) t (.base .trueE)

theorem LamEquiv.not_true_equiv_false :
  LamEquiv lval lctx (.base .prop) (.mkNot (.base .trueE)) (.base .falseE) := by
  exists LamWF.mkNot (.ofBase .ofTrueE); exists LamWF.ofBase .ofFalseE; intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, notLift]
  apply GLift.down.inj; dsimp; apply eq_false; exact fun h => h .intro

theorem LamEquiv.not_false_equiv_true :
  LamEquiv lval lctx (.base .prop) (.mkNot (.base .falseE)) (.base .trueE) := by
  exists LamWF.mkNot (.ofBase .ofFalseE); exists LamWF.ofBase .ofTrueE; intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, notLift]
  apply GLift.down.inj; dsimp; apply eq_true; exact id

theorem LamEquiv.prop_ne_equiv_eq_not
  (wfl : LamWF lval.toLamTyVal ⟨lctx, lhs, .base .prop⟩)
  (wfr : LamWF lval.toLamTyVal ⟨lctx, rhs, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) (.mkNot (.mkEq (.base .prop) lhs rhs)) (.mkEq (.base .prop) lhs (.mkNot rhs)) := by
  exists LamWF.mkNot (LamWF.mkEq wfl wfr); exists LamWF.mkEq wfl (.mkNot wfr); intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, notLift, eqLiftFn]
  apply GLift.down.inj; apply propext (Iff.intro ?mp ?mpr)
  case mp =>
    intro h; apply GLift.down.inj; apply eq_not_of_ne
    intro h'; apply h; apply GLift.down.inj _ _ h'
  case mpr =>
    intro h h'; have h' := _root_.congrArg GLift.down h'; revert h'
    apply ne_of_eq_not; dsimp at h; rw [h]

-- (a ≠ b) ↔ (a = (¬ b))
def LamTerm.prop_ne_equiv_eq_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq (.base .prop))) lhs) rhs) =>
    .some (.mkEq (.base .prop) lhs (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_prop_ne_equiv_eq_not?
  (heq : prop_ne_equiv_eq_not? t = .some t') : t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq (.base .prop))) lhs) rhs), Eq.refl _ => by
    dsimp [maxEVarSucc]; simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.prop_ne_equiv_eq_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.prop_ne_equiv_eq_not? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq (.base .prop))) lhs) rhs), Eq.refl _ => by
    cases wft.getFn.getBase; cases wft.getArg.getFn.getFn.getBase
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) Hrhs) =>
      apply LamEquiv.prop_ne_equiv_eq_not Hlhs Hrhs

theorem LamThmEquiv.prop_ne_equiv_eq_not?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.prop_ne_equiv_eq_not? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.prop_ne_equiv_eq_not? (wft lctx') heq

theorem LamTerm.maxEVarSucc_equalize : (LamTerm.equalize t).maxEVarSucc = t.maxEVarSucc := by
  simp [maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.equalize (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) t t.equalize := by
  dsimp [LamTerm.equalize]; exists wft; exists (.mkEq wft (.ofBase .ofTrueE))
  intro lctxTerm; apply GLift.down.inj
  apply propext (Iff.intro
    (fun h => GLift.down.inj _ _ (eq_true h))
    (fun h => of_eq_true (_root_.congrArg GLift.down h)))

theorem LamThmEquiv.equalize (wft : LamThmWF lval lctx (.base .prop) t) :
  LamThmEquiv lval lctx (.base .prop) t t.equalize :=
  fun lctx' => LamEquiv.equalize (wft lctx')

-- (True = False) ↔ False
def LamTerm.true_eq_false_equiv_false? (t : LamTerm) : Option LamTerm :=
  match t.beq (.mkEq (.base .prop) (.base .trueE) (.base .falseE)) with
  | true => .some (.base .falseE)
  | false => .none

theorem LamTerm.maxEVarSucc_true_eq_false_equiv_false?
  (heq : LamTerm.true_eq_false_equiv_false? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc := by
  dsimp [LamTerm.true_eq_false_equiv_false?] at heq; revert heq
  cases hbeq : t.beq (.mkEq (.base .prop) (.base .trueE) (.base .falseE))
  case true =>
    intro h; cases h; cases (LamTerm.eq_of_beq_eq_true hbeq)
    dsimp [maxEVarSucc]; rfl
  case false =>
    intro h; cases h

theorem LamEquiv.true_eq_false_equiv_false?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.true_eq_false_equiv_false? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' := by
  dsimp [LamTerm.true_eq_false_equiv_false?] at heq; revert heq
  cases hbeq : t.beq (.mkEq (.base .prop) (.base .trueE) (.base .falseE))
  case true =>
    intro h; cases h; cases (LamTerm.eq_of_beq_eq_true hbeq)
    cases wft.getFn.getFn.getBase; exists wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofBase .ofTrueE)) (.ofBase .ofFalseE) =>
      exists (.ofBase .ofFalseE); intro lctxTerm; apply GLift.down.inj
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply propext (Iff.intro ?mp False.elim)
      case mp =>
        intro h; have h' := GLift.up.inj h; contradiction
  case false =>
    intro h; cases h

theorem LamThmEquiv.true_eq_false_equiv_false?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.true_eq_false_equiv_false? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.true_eq_false_equiv_false? (wft lctx') heq

-- (False = True) ↔ False
def LamTerm.false_eq_true_equiv_false? (t : LamTerm) : Option LamTerm :=
  match t.beq (.mkEq (.base .prop) (.base .falseE) (.base .trueE)) with
  | true => .some (.base .falseE)
  | false => .none

theorem LamTerm.maxEVarSucc_false_eq_true_equiv_false?
  (heq : LamTerm.false_eq_true_equiv_false? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc := by
  dsimp [LamTerm.false_eq_true_equiv_false?] at heq; revert heq
  cases hbeq : t.beq (.mkEq (.base .prop) (.base .falseE) (.base .trueE))
  case true =>
    intro h; cases h; cases (LamTerm.eq_of_beq_eq_true hbeq)
    dsimp [maxEVarSucc]; rfl
  case false =>
    intro h; cases h

theorem LamEquiv.false_eq_true_equiv_false?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.false_eq_true_equiv_false? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' := by
  dsimp [LamTerm.false_eq_true_equiv_false?] at heq; revert heq
  cases hbeq : t.beq (.mkEq (.base .prop) (.base .falseE) (.base .trueE) )
  case true =>
    intro h; cases h; cases (LamTerm.eq_of_beq_eq_true hbeq)
    cases wft.getFn.getFn.getBase; exists wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofBase .ofFalseE)) (.ofBase .ofTrueE) =>
      exists (.ofBase .ofFalseE); intro lctxTerm; apply GLift.down.inj
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply propext (Iff.intro ?mp False.elim)
      case mp =>
        intro h; have h' := GLift.up.inj h; contradiction
  case false =>
    intro h; cases h

theorem LamThmEquiv.false_eq_true_equiv_false?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.false_eq_true_equiv_false? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.false_eq_true_equiv_false? (wft lctx') heq

-- (a = True) ↔ a
def LamTerm.eq_true_equiv? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .trueE) => .some lhs
  | _ => .none

theorem LamTerm.maxEVarSucc_eq_true_equiv?
  (heq : LamTerm.eq_true_equiv? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .trueE), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.eq_true_equiv?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.eq_true_equiv? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .trueE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getArg.getBase; exists wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofTrueE) =>
      exists Hlhs; intro lctxTerm
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h; apply of_eq_true (_root_.congrArg _ h)
      case mpr =>
        intro h; apply GLift.down.inj _ _ (eq_true h)

theorem LamThmEquiv.eq_true_equiv?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.eq_true_equiv? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.eq_true_equiv? (wft lctx') heq

-- (a = False) ↔ (¬ a)
def LamTerm.eq_false_equiv? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .falseE) => .some (.mkNot lhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_eq_false_equiv?
  (heq : LamTerm.eq_false_equiv? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .falseE), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.eq_false_equiv?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.eq_false_equiv? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .falseE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getArg.getBase; exists wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofFalseE) =>
      exists LamWF.mkNot Hlhs; intro lctxTerm
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h h'; rw [h] at h'; exact h'
      case mpr =>
        intro h; apply GLift.down.inj _ _ (eq_false h)

theorem LamThmEquiv.eq_false_equiv?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.eq_false_equiv? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.eq_false_equiv? (wft lctx') heq

-- (a ≠ True) ↔ (a = False)
def LamTerm.ne_true_equiv_eq_false? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app s (.app _ (.base (.eq _)) lhs) (.base .trueE)) =>
    .some (.app s (.app s (.base (.eq s)) lhs) (.base .falseE))
  | _ => .none

theorem LamTerm.maxEVarSucc_ne_true_equiv_eq_false?
  (heq : LamTerm.ne_true_equiv_eq_false? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq _)) lhs) (.base .trueE)), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.ne_true_equiv_eq_false?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.ne_true_equiv_eq_false? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq _)) lhs) (.base .trueE)), Eq.refl _ =>
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofTrueE)) => by
      apply LamEquiv.trans (prop_ne_equiv_eq_not Hlhs (.ofBase .ofTrueE))
      apply LamEquiv.congrArg (.ofApp _ (.ofBase (.ofEq _)) Hlhs)
      apply LamEquiv.not_true_equiv_false

theorem LamThmEquiv.ne_true_equiv_eq_false?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.ne_true_equiv_eq_false? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.ne_true_equiv_eq_false? (wft lctx') heq

-- (a ≠ False) ↔ (a = True)
def LamTerm.ne_false_equiv_eq_true? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app s (.app _ (.base (.eq _)) lhs) (.base .falseE)) =>
    .some (.app s (.app s (.base (.eq s)) lhs) (.base .trueE))
  | _ => .none

theorem LamTerm.maxEVarSucc_ne_false_equiv_eq_true?
  (heq : LamTerm.ne_false_equiv_eq_true? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq _)) lhs) (.base .falseE)), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.ne_false_equiv_eq_true?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.ne_false_equiv_eq_true? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq _)) lhs) (.base .falseE)), Eq.refl _ =>
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofFalseE)) => by
      apply LamEquiv.trans (prop_ne_equiv_eq_not Hlhs (.ofBase .ofFalseE))
      apply LamEquiv.congrArg (.ofApp _ (.ofBase (.ofEq _)) Hlhs)
      apply LamEquiv.not_false_equiv_true

theorem LamThmEquiv.ne_false_equiv_eq_true?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.ne_false_equiv_eq_true? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.ne_false_equiv_eq_true? (wft lctx') heq

-- ((¬ a) = True) ↔ (a = False)
def LamTerm.not_eq_true_equiv_eq_false? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .trueE) =>
    .some (.mkEq (.base .prop) lhs (.base .falseE))
  | _ => .none

def LamTerm.maxEVarSucc_not_eq_true_equiv_eq_false?
  (heq : LamTerm.not_eq_true_equiv_eq_false? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .trueE), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_true_equiv_eq_false?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_true_equiv_eq_false? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .trueE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getFn.getArg.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) (.ofBase .ofTrueE) =>
      apply trans (eqSymm? wft rfl)
      apply trans (symm (prop_ne_equiv_eq_not (.ofBase .ofTrueE) Hlhs))
      apply trans _ (ne_true_equiv_eq_false? (LamWF.mkNot (.mkEq Hlhs (.ofBase .ofTrueE))) rfl)
      apply congrArg (.ofBase .ofNot); apply eqSymm? (.mkEq (.ofBase .ofTrueE) Hlhs) rfl

theorem LamThmEquiv.not_eq_true_equiv_eq_false?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.not_eq_true_equiv_eq_false? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.not_eq_true_equiv_eq_false? (wft lctx') heq

def LamTerm.not_eq_false_equiv_eq_true? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .falseE) =>
    .some (.mkEq (.base .prop) lhs (.base .trueE))
  | _ => .none

def LamTerm.maxEVarSucc_not_eq_false_equiv_eq_true?
  (heq : LamTerm.not_eq_false_equiv_eq_true? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .falseE), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_false_equiv_eq_true?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_false_equiv_eq_true? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .falseE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getFn.getArg.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) (.ofBase .ofFalseE) =>
      apply trans (eqSymm? wft rfl)
      apply trans (symm (prop_ne_equiv_eq_not (.ofBase .ofFalseE) Hlhs))
      apply trans _ (ne_false_equiv_eq_true? (LamWF.mkNot (.mkEq Hlhs (.ofBase .ofFalseE))) rfl)
      apply congrArg (.ofBase .ofNot); apply eqSymm? (.mkEq (.ofBase .ofFalseE) Hlhs) rfl

theorem LamThmEquiv.not_eq_false_equiv_eq_true?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.not_eq_false_equiv_eq_true? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.not_eq_false_equiv_eq_true? (wft lctx') heq

-- (¬¬a) ↔ a
theorem LamEquiv.not_not_equiv
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) (.mkNot (.mkNot t)) t := by
  exists (.mkNot (.mkNot wft)); exists wft; intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, notLift]
  apply GLift.down.inj; dsimp
  apply propext (Iff.intro Classical.byContradiction (fun a b => b a))

theorem LamThmEquiv.not_not_equiv
  (wft : LamThmWF lval lctx (.base .prop) t) :
  LamThmEquiv lval lctx (.base .prop) (.mkNot (.mkNot t)) t :=
  fun lctx' => LamEquiv.not_not_equiv (wft lctx')

-- ((¬ a) = b) ↔ (a = (¬ b))
def LamTerm.not_eq_equiv_eq_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) rhs =>
    .some (.mkEq (.base .prop) lhs (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_not_eq_equiv_eq_not?
  (heq : LamTerm.not_eq_equiv_eq_not? t = .some t') :
  t.maxEVarSucc = t'.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) rhs, Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_equiv_eq_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_equiv_eq_not? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) rhs, Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getFn.getArg.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) Hrhs =>
      apply trans (eqSymm? (.mkEq (.mkNot Hlhs) Hrhs) rfl) (trans _ (prop_ne_equiv_eq_not Hlhs Hrhs))
      apply trans (symm (prop_ne_equiv_eq_not Hrhs Hlhs)) (neSymm? (.mkNot (.mkEq Hrhs Hlhs)) rfl)

-- ((¬ a) = (¬ b)) ↔ (a = b)
def LamTerm.not_eq_not_equiv_eq? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.app _ (.base .not) rhs) =>
    .some (.mkEq (.base .prop) lhs rhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_not_eq_not_equiv_eq?
  (heq : LamTerm.not_eq_not_equiv_eq? t = .some t') :
  t.maxEVarSucc = t'.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.app _ (.base .not) rhs), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_not_equiv_eq?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_not_equiv_eq? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.app _ (.base .not) rhs), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getArg.getFn.getBase; cases wft.getFn.getArg.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) (.ofApp _ (.ofBase .ofNot) Hrhs) =>
      apply trans (symm (not_eq_equiv_eq_not? (.mkEq (.mkNot (.mkNot Hlhs)) Hrhs) rfl))
      apply congrFun (congrArg (.ofBase (.ofEq _)) (not_not_equiv Hlhs)) Hrhs

theorem LamThmEquiv.not_eq_not_equiv_eq?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.not_eq_not_equiv_eq? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.not_eq_not_equiv_eq? (wft lctx') heq

-- (a ↔ b) ↔ (a = b)
def LamTerm.iff_equiv_eq? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base .iff) lhs) rhs => .some (.mkEq (.base .prop) lhs rhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_iff_equiv_eq?
  (heq : LamTerm.iff_equiv_eq? t = .some t') :
  t.maxEVarSucc = t'.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base .iff) lhs) rhs, Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.iff_equiv_eq?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.iff_equiv_eq?  t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base .iff) lhs) rhs, Eq.refl _ => by
    cases wft.getFn.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase .ofIff) Hlhs) Hrhs =>
      exists (.mkIff Hlhs Hrhs); exists (.mkEq Hlhs Hrhs); intro lctxTerm
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, iffLift, eqLiftFn]
      apply GLift.down.inj; apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h; apply GLift.down.inj; apply propext h
      case mpr =>
        intro h; apply iff_of_eq (_root_.congrArg GLift.down h)

theorem LamThmEquiv.iff_equiv_eq?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.iff_equiv_eq?  t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.iff_equiv_eq? (wft lctx') heq