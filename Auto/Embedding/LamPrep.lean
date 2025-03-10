import Auto.Embedding.LamConv

namespace Auto.Embedding.Lam

def LamTerm.andLeft? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base .and) lhs) _ => lhs
  | _ => .none

theorem LamTerm.evarBounded_andLeft? : evarBounded andLeft? 0 := by
  intro t t' heq
  match t, heq with
  | .app _ (.app _ (.base .and) _) _, Eq.refl _ =>
    dsimp [maxEVarSucc]; simp [Nat.max, Nat.max_zero_left]
    apply Nat.le_max_left

theorem LamGenModify.andLeft? : LamGenModify lval LamTerm.andLeft? true := by
  intro t₁ t₂ heq lctx hwf; dsimp
  match t₁, heq with
  | .app _ (.app _ (.base .and) _) _, Eq.refl _ =>
    cases hwf.getFn.getFn.getBase.getPcst
    apply LamValid.and_left hwf.getFn.getArg hwf.getArg

def LamTerm.andRight? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base .and) _) rhs => rhs
  | _ => .none

theorem LamTerm.evarBounded_andRight? : evarBounded andRight? 0 := by
  intro t t' heq
  match t, heq with
  | .app _ (.app _ (.base .and) _) _, Eq.refl _ =>
    dsimp [maxEVarSucc]; simp [Nat.max, Nat.max_zero_left]
    apply Nat.le_max_right

theorem LamGenModify.andRight? : LamGenModify lval LamTerm.andRight? true := by
  intro t₁ t₂ heq lctx hwf; dsimp
  match t₁, heq with
  | .app _ (.app _ (.base .and) _) _, Eq.refl _ =>
    cases hwf.getFn.getFn.getBase.getPcst
    apply LamValid.and_right hwf.getFn.getArg hwf.getArg

theorem eq_not_of_ne (h : a ≠ b) : a = (¬ b) :=
  propext (Iff.intro
    (fun ha hb => h (Eq.trans (eq_true ha) (eq_true hb).symm))
    (fun nb => Classical.byContradiction (fun na => h (Eq.trans (eq_false na) (eq_false nb).symm))))

theorem ne_of_eq_not (h : a = (¬ b)) : a ≠ b := fun h' =>
  have hb : b := Classical.byContradiction (fun nb => nb (Eq.mp h' (Eq.mp h.symm nb)))
  have hnb : ¬ b := Eq.mp h (Eq.mp h'.symm hb)
  hnb hb

theorem equiv_eq : (a ↔ b) = (a = b) := propext (Iff.intro propext (fun h => by cases h; apply Iff.rfl))

theorem not_equiv_eq : (¬ (a ↔ b)) = (a ≠ b) := by rw [equiv_eq]

theorem propeq_equiv {a b : Prop} : (a = b) ↔ (a ∨ ¬ b) ∧ (¬ a ∨ b) := by
  apply Iff.intro
  case mp => intro h; cases h; cases Classical.em a <;> simp [*]
  case mpr => intro ⟨hl, hr⟩; cases hl <;> cases hr <;> simp [*] <;> contradiction

theorem propne_equiv {a b : Prop} : (a ≠ b) ↔ (a ∨ b) ∧ (¬ a ∨ ¬ b) := by
  apply Iff.intro
  case mp => intro h; cases (eq_not_of_ne h); cases (Classical.em b) <;> simp [*]
  case mpr => intro h h'; cases h'; simp at h

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
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamWF.mkEq, notLift, eqLiftFn]
  apply GLift.down.inj; apply propext (Iff.intro ?mp ?mpr)
  case mp =>
    intro h; apply GLift.down.inj; apply eq_not_of_ne
    intro h'; apply h; apply GLift.down.inj _ _ h'
  case mpr =>
    intro h h'; have h' := _root_.congrArg GLift.down h'; revert h'
    apply ne_of_eq_not; dsimp [LamTerm.mkEq] at h; rw [h]; rfl

/-- (a ≠ b) ↔ (a = (¬ b)) -/
def LamTerm.prop_ne_equiv_eq_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq (.base .prop))) lhs) rhs) =>
    .some (.mkEq (.base .prop) lhs (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_prop_ne_equiv_eq_not?
  (heq : prop_ne_equiv_eq_not? t = .some t') : t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq (.base .prop))) lhs) rhs), Eq.refl _ => by
    dsimp [mkEq, mkNot, maxEVarSucc]; simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.prop_ne_equiv_eq_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.prop_ne_equiv_eq_not? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq (.base .prop))) lhs) rhs), Eq.refl _ => by
    cases wft.getArg.getFn.getFn.getBase
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) Hrhs) =>
      apply LamEquiv.prop_ne_equiv_eq_not Hlhs Hrhs

theorem LamGenConv.prop_ne_equiv_eq_not? : LamGenConv lval LamTerm.prop_ne_equiv_eq_not? := by
  intros t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.prop_ne_equiv_eq_not? wf heq
  have ⟨wf', _⟩ := hequiv; cases (wf'.unique wf).left; exact hequiv

def LamTerm.equalize (t : LamTerm) : LamTerm := .mkEq (.base .prop) t (.base .trueE)

theorem LamTerm.maxEVarSucc_equalize : (LamTerm.equalize t).maxEVarSucc = t.maxEVarSucc := by
  simp [equalize, mkEq, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.equalize (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) t t.equalize := by
  dsimp [LamTerm.equalize]; exists wft; exists (.mkEq wft (.ofBase .ofTrueE))
  intro lctxTerm; apply GLift.down.inj
  apply propext (Iff.intro
    (fun h => GLift.down.inj _ _ (eq_true h))
    (fun h => of_eq_true (_root_.congrArg GLift.down h)))

def LamTerm.equalize? (s : LamSort) (t : LamTerm) : Option LamTerm :=
  match s with
  | .base .prop => .some (.mkEq (.base .prop) t (.base .trueE))
  | _ => .none

theorem LamTerm.maxEVarSucc_equalize? (heq : equalize? s t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc := by
  match s, heq with
  | .base .prop, Eq.refl _ =>
    simp [mkEq, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.equalize?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩)
  (heq : t.equalize? s = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' := by
  match s, heq with
  | .base .prop, Eq.refl _ =>
    apply And.intro rfl; apply LamEquiv.equalize wft

theorem LamGenConv.equalize? : LamGenConvWith lval LamTerm.equalize? := by
  intros rty t₁ t₂ heq lctx wf
  match rty, heq with
  | .base .prop, Eq.refl _ => apply LamEquiv.equalize wf

/-- (True = False) ↔ False -/
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
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' := by
  dsimp [LamTerm.true_eq_false_equiv_false?] at heq; revert heq
  cases hbeq : t.beq (.mkEq (.base .prop) (.base .trueE) (.base .falseE))
  case true =>
    intro h; cases h; cases (LamTerm.eq_of_beq_eq_true hbeq)
    cases wft.getFn.getFn.getBase; exists rfl, wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofBase .ofTrueE)) (.ofBase .ofFalseE) =>
      exists (.ofBase .ofFalseE); intro lctxTerm; apply GLift.down.inj
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply propext (Iff.intro ?mp False.elim)
      case mp =>
        intro h; have h' := GLift.up.inj h; contradiction
  case false =>
    intro h; cases h

theorem LamGenConv.true_eq_false_equiv_false? : LamGenConv lval LamTerm.true_eq_false_equiv_false? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.true_eq_false_equiv_false? wf heq
  cases heq; apply hequiv

/-- (False = True) ↔ False -/
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
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' := by
  dsimp [LamTerm.false_eq_true_equiv_false?] at heq; revert heq
  cases hbeq : t.beq (.mkEq (.base .prop) (.base .falseE) (.base .trueE) )
  case true =>
    intro h; cases h; cases (LamTerm.eq_of_beq_eq_true hbeq)
    cases wft.getFn.getFn.getBase; exists rfl, wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofBase .ofFalseE)) (.ofBase .ofTrueE) =>
      exists (.ofBase .ofFalseE); intro lctxTerm; apply GLift.down.inj
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply propext (Iff.intro ?mp False.elim)
      case mp =>
        intro h; have h' := GLift.up.inj h; contradiction
  case false =>
    intro h; cases h

theorem LamGenConv.false_eq_true_equiv_false? : LamGenConv lval LamTerm.false_eq_true_equiv_false? := by
  intros t₁ t₂ heq rty lctx wf
  have ⟨heq, hequiv⟩ := LamEquiv.false_eq_true_equiv_false? wf heq
  cases heq; apply hequiv

/--
  (a = True) ↔ a

  At first sight, it seems that this theorem will never be used
    in clausification. However, it will, as we need to turn
    `(a = b) = True` into `a = b`
-/
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
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .trueE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; exists rfl, wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofTrueE) =>
      exists Hlhs; intro lctxTerm
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h; apply of_eq_true (_root_.congrArg _ h)
      case mpr =>
        intro h; apply GLift.down.inj _ _ (eq_true h)

theorem LamGenConv.eq_true_equiv? : LamGenConv lval LamTerm.eq_true_equiv? := by
  intros t₁ t₂ heq rty lctx wf
  have ⟨heq, hequiv⟩ := LamEquiv.eq_true_equiv? wf heq
  cases heq; apply hequiv

/--
  (a = False) ↔ (¬ a)

  At first sight, it seems that this theorem will never be used
    in clausification. However, it will, as we need to turn
    `(a = b) = False` into `a ≠ b`
-/
def LamTerm.eq_false_equiv? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .falseE) => .some (.mkNot lhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_eq_false_equiv?
  (heq : LamTerm.eq_false_equiv? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .falseE), Eq.refl _ => by
    simp [mkNot, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.eq_false_equiv?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.eq_false_equiv? t = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) lhs) (.base .falseE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; exists rfl, wft
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofFalseE) =>
      exists LamWF.mkNot Hlhs; intro lctxTerm
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h h'; rw [h] at h'; exact h'
      case mpr =>
        intro h; apply GLift.down.inj _ _ (eq_false h)

theorem LamGenConv.eq_false_equiv? : LamGenConv lval LamTerm.eq_false_equiv? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.eq_false_equiv? wf heq
  cases heq; apply hequiv

/-- (a ≠ True) ↔ (a = False) -/
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
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq _)) lhs) (.base .trueE)), Eq.refl _ =>
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofTrueE)) => by
      apply And.intro rfl
      apply LamEquiv.trans (prop_ne_equiv_eq_not Hlhs (.ofBase .ofTrueE))
      apply LamEquiv.congrArg (.ofApp _ (.ofBase (.ofEq _)) Hlhs)
      apply LamEquiv.not_true_equiv_false

theorem LamGenConv.ne_true_equiv_eq_false? : LamGenConv lval LamTerm.ne_true_equiv_eq_false? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.ne_true_equiv_eq_false? wf heq
  cases heq; apply hequiv

/-- (a ≠ False) ↔ (a = True) -/
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
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base (.eq _)) lhs) (.base .falseE)), Eq.refl _ =>
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofFalseE)) => by
      apply And.intro rfl
      apply LamEquiv.trans (prop_ne_equiv_eq_not Hlhs (.ofBase .ofFalseE))
      apply LamEquiv.congrArg (.ofApp _ (.ofBase (.ofEq _)) Hlhs)
      apply LamEquiv.not_false_equiv_true

theorem LamGenConv.ne_false_equiv_eq_true? : LamGenConv lval LamTerm.ne_false_equiv_eq_true? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.ne_false_equiv_eq_true? wf heq
  cases heq; apply hequiv

/-- ((¬ a) = True) ↔ (a = False) -/
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
    simp [mkEq, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_true_equiv_eq_false?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_true_equiv_eq_false? t = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .trueE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getFn.getArg.getFn.getBase.getPcst
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) (.ofBase .ofTrueE) =>
      apply And.intro rfl
      apply trans (eqSymm? wft rfl)
      apply trans (symm (prop_ne_equiv_eq_not (.ofBase .ofTrueE) Hlhs))
      apply trans _ (ne_true_equiv_eq_false? (LamWF.mkNot (.mkEq Hlhs (.ofBase .ofTrueE))) rfl).right
      apply congrArg (.ofBase .ofNot); apply eqSymm? (.mkEq (.ofBase .ofTrueE) Hlhs) rfl

theorem LamGenConv.not_eq_true_equiv_eq_false? : LamGenConv lval LamTerm.not_eq_true_equiv_eq_false? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.not_eq_true_equiv_eq_false? wf heq
  cases heq; apply hequiv

/-- ((¬ a) = False) ↔ (a = True) -/
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
    simp [mkEq, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_false_equiv_eq_true?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_false_equiv_eq_true? t = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.base .falseE), Eq.refl _ => by
    cases wft.getFn.getFn.getBase; cases wft.getFn.getArg.getFn.getBase.getPcst
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) (.ofBase .ofFalseE) =>
      apply And.intro rfl
      apply trans (eqSymm? wft rfl)
      apply trans (symm (prop_ne_equiv_eq_not (.ofBase .ofFalseE) Hlhs))
      apply trans _ (ne_false_equiv_eq_true? (LamWF.mkNot (.mkEq Hlhs (.ofBase .ofFalseE))) rfl).right
      apply congrArg (.ofBase .ofNot); apply eqSymm? (.mkEq (.ofBase .ofFalseE) Hlhs) rfl

theorem LamGenConv.not_eq_false_equiv_eq_true? : LamGenConv lval LamTerm.not_eq_false_equiv_eq_true? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.not_eq_false_equiv_eq_true? wf heq
  cases heq; apply hequiv

/-- (¬¬a) ↔ a -/
theorem LamEquiv.not_not_equiv
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) (.mkNot (.mkNot t)) t := by
  exists (.mkNot (.mkNot wft)); exists wft; intro lctxTerm
  dsimp [LamTerm.mkNot, LamWF.interp, LamBaseTerm.LamWF.interp, notLift]
  apply GLift.down.inj; dsimp
  apply propext (Iff.intro Classical.byContradiction (fun a b => b a))

def LamTerm.not_not_equiv? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app _ (.base .not) t') => .some t'
  | _ => .none

theorem LamTerm.maxEVarSucc_not_not_equiv? (heq : not_not_equiv? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc := by
  match t, heq with
  | .app _ (.base .not) (.app _ (.base .not) t'), Eq.refl _ =>
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_not_equiv?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : t.not_not_equiv? = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' := by
  match t, heq with
  | .app _ (.base .not) (.app _ (.base .not) t'), Eq.refl _ =>
    cases wft.getFn.getBase.getPcst; cases wft.getArg.getFn.getBase.getPcst
    apply And.intro rfl (LamEquiv.not_not_equiv wft.getArg.getArg)

theorem LamGenConv.not_not_equiv? : LamGenConv lval LamTerm.not_not_equiv? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.not_not_equiv? wf heq
  cases heq; apply hequiv

/-- ((¬ a) = b) ↔ (a = (¬ b)) -/
def LamTerm.not_eq_equiv_eq_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) rhs =>
    .some (.mkEq (.base .prop) lhs (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_not_eq_equiv_eq_not?
  (heq : LamTerm.not_eq_equiv_eq_not? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) rhs, Eq.refl _ => by
    simp [mkEq, mkNot, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_equiv_eq_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_equiv_eq_not? t = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) rhs, Eq.refl _ => by
    cases wft.getFn.getArg.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) Hrhs =>
      apply And.intro rfl
      apply trans (eqSymm? (.mkEq (.mkNot Hlhs) Hrhs) rfl) (trans _ (prop_ne_equiv_eq_not Hlhs Hrhs))
      apply trans (symm (prop_ne_equiv_eq_not Hrhs Hlhs)) (neSymm? (.mkNot (.mkEq Hrhs Hlhs)) rfl)

theorem LamGenConv.not_eq_equiv_eq_not? : LamGenConv lval LamTerm.not_eq_equiv_eq_not? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.not_eq_equiv_eq_not? wf heq
  cases heq; apply hequiv

/-- ((¬ a) = (¬ b)) ↔ (a = b) -/
def LamTerm.not_eq_not_equiv_eq? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.app _ (.base .not) rhs) =>
    .some (.mkEq (.base .prop) lhs rhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_not_eq_not_equiv_eq?
  (heq : LamTerm.not_eq_not_equiv_eq? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.app _ (.base .not) rhs), Eq.refl _ => by
    simp [mkEq, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_eq_not_equiv_eq?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_eq_not_equiv_eq? t = .some t') :
  s = .base .prop ∧ LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base (.eq _)) (.app _ (.base .not) lhs)) (.app _ (.base .not) rhs), Eq.refl _ => by
    cases wft.getFn.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ (.ofBase .ofNot) Hlhs)) (.ofApp _ (.ofBase .ofNot) Hrhs) =>
      apply And.intro rfl
      apply trans (symm (not_eq_equiv_eq_not? (.mkEq (.mkNot (.mkNot Hlhs)) Hrhs) rfl).right)
      apply congrFun (congrArg (.ofBase (.ofEq _)) (not_not_equiv Hlhs)) Hrhs

theorem LamGenConv.not_eq_not_equiv_eq? : LamGenConv lval LamTerm.not_eq_not_equiv_eq? := by
  intros t₁ t₂ heq lctx rty wf
  have ⟨heq, hequiv⟩ := LamEquiv.not_eq_not_equiv_eq? wf heq
  cases heq; apply hequiv

/-- (a ↔ b) ↔ (a = b) -/
def LamTerm.propext? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base .iff) lhs) rhs => .some (.mkEq (.base .prop) lhs rhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_propext?
  (heq : LamTerm.propext? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base .iff) lhs) rhs, Eq.refl _ => by
    simp [mkEq, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.propext?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.propext? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base .iff) lhs) rhs, Eq.refl _ => by
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase .ofIff) Hlhs) Hrhs =>
      exists (.mkIff Hlhs Hrhs); exists (.mkEq Hlhs Hrhs); intro lctxTerm
      dsimp [LamWF.mkEq, LamWF.interp, LamBaseTerm.LamWF.interp, iffLift, eqLiftFn]
      apply GLift.down.inj; apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h; apply GLift.down.inj; apply propext h
      case mpr =>
        intro h; apply iff_of_eq (_root_.congrArg GLift.down h)

theorem LamGenConv.propext? : LamGenConv lval LamTerm.propext? := by
  intros t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.propext? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv

/-- ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b -/
def LamTerm.not_and_equiv_not_or_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app _ (.app _ (.base .and) lhs) rhs) =>
    .some (.mkOr (.mkNot lhs) (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_not_and_equiv_not_or_not?
  (heq : LamTerm.not_and_equiv_not_or_not? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base .and) lhs) rhs), Eq.refl _ => by
    simp [mkNot, mkOr, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.not_and_equiv_not_or_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_and_equiv_not_or_not? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base .and) lhs) rhs), Eq.refl _ => by
    cases wft.getArg.getFn.getFn.getBase.getPcst
    match wft with
    | .ofApp _ _ (.ofApp _ (.ofApp _ _ Hlhs) Hrhs) =>
      exists (.mkNot (.mkAnd Hlhs Hrhs)), (.mkOr (.mkNot Hlhs) (.mkNot Hrhs)); intro lctxTerm
      apply GLift.down.inj; apply propext
      apply Classical.not_and_iff_or_not_not

theorem LamGenConv.not_and_equiv_not_or_not? : LamGenConv lval LamTerm.not_and_equiv_not_or_not? := by
  intro t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.not_and_equiv_not_or_not? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv

/-- ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b -/
def LamTerm.not_or_equiv_not_and_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app _ (.app _ (.base .or) lhs) rhs) =>
    .some (.mkAnd (.mkNot lhs) (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_not_or_equiv_not_and_not?
  (heq : LamTerm.not_or_equiv_not_and_not? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base .or) lhs) rhs), Eq.refl _ => by
    simp [mkNot, mkAnd, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.not_or_equiv_not_and_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_or_equiv_not_and_not? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base .or) lhs) rhs), Eq.refl _ => by
    cases wft.getArg.getFn.getFn.getBase.getPcst
    match wft with
    | .ofApp _ _ (.ofApp _ (.ofApp _ _ Hlhs) Hrhs) =>
      exists (.mkNot (.mkOr Hlhs Hrhs)), (.mkAnd (.mkNot Hlhs) (.mkNot Hrhs)); intro lctxTerm
      apply GLift.down.inj; apply propext; apply not_or

theorem LamGenConv.not_or_equiv_not_and_not? : LamGenConv lval LamTerm.not_or_equiv_not_and_not? := by
  intro t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.not_or_equiv_not_and_not? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv

/-- (a = b) ↔ (a ∨ ¬ b) ∧ (¬ a ∨ b) -/
def LamTerm.propeq? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app (.base .prop) (.app _ (.base (.eq _)) lhs) rhs =>
    .some (.mkAnd (.mkOr lhs (.mkNot rhs)) (.mkOr (.mkNot lhs) rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_propeq?
  (heq : LamTerm.propeq? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app (.base .prop) (.app _ (.base (.eq _)) lhs) rhs, Eq.refl _ => by
    simp [mkOr, mkNot, mkAnd, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right, Nat.max_eq_left]

theorem propeq_equiv_eq' {a b : GLift Prop} : (a = b) ↔
  (a.down ∨ ¬ b.down) ∧ (¬ a.down ∨ b.down) := by
  cases a; case up a => cases b; simp [eqGLift_equiv]; rw [equiv_eq (a:=a)]; apply propeq_equiv

theorem LamEquiv.propeq?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.propeq? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app (.base .prop) (.app _ (.base (.eq _)) lhs) rhs, Eq.refl _ => by
    cases wft.getFn.getFn.getBase
    match wft with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) Hrhs =>
      exists (.mkEq Hlhs Hrhs)
      exists (.mkAnd (.mkOr Hlhs (.mkNot Hrhs)) (.mkOr (.mkNot Hlhs) Hrhs))
      intro lctxTerm; apply GLift.down.inj; apply propext; apply propeq_equiv_eq'

theorem LamGenConv.propeq? : LamGenConv lval LamTerm.propeq? := by
  intro t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.propeq? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv

/-- (a → b) ↔ (¬ a ∨ b) -/
def LamTerm.imp_equiv_not_or? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.app _ (.base .imp) lhs) rhs => .some (.mkOr (.mkNot lhs) rhs)
  | _ => .none

theorem LamTerm.maxEVarSucc_imp_equiv_not_or?
  (heq : LamTerm.imp_equiv_not_or? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.app _ (.base .imp) lhs) rhs, Eq.refl _ => by
    simp [mkNot, mkOr, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.imp_equiv_not_or?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.imp_equiv_not_or? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.app _ (.base .imp) lhs) rhs, Eq.refl _ => by
    cases wft.getFn.getFn.getBase.getPcst
    match wft with
    | .ofApp _ (.ofApp _ _ Hlhs) Hrhs =>
      exists (.mkImp Hlhs Hrhs), (.mkOr (.mkNot Hlhs) Hrhs); intro lctxTerm
      apply GLift.down.inj; apply propext
      apply @Decidable.imp_iff_not_or _ _ (Classical.propDecidable _)

theorem LamGenConv.imp_equiv_not_or? : LamGenConv lval LamTerm.imp_equiv_not_or? := by
  intro t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.imp_equiv_not_or? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv

/-- (¬ (a → b)) ↔ (a ∧ ¬ b) -/
def LamTerm.not_imp_equiv_and_not? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app _ (.app _ (.base .imp) lhs) rhs) =>
    .some (.mkAnd lhs (.mkNot rhs))
  | _ => .none

theorem LamTerm.maxEVarSucc_not_imp_equiv_and_not?
  (heq : LamTerm.not_imp_equiv_and_not? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base .imp) lhs) rhs), Eq.refl _ => by
    simp [mkNot, mkAnd, maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamEquiv.not_imp_equiv_and_not?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.not_imp_equiv_and_not? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app _ (.app _ (.base .imp) lhs) rhs), Eq.refl _ => by
    cases wft.getArg.getFn.getFn.getBase.getPcst
    match wft with
    | .ofApp _ _ (.ofApp _ (.ofApp _ _ Hlhs) Hrhs) =>
      exists .mkNot (.mkImp Hlhs Hrhs), (.mkAnd Hlhs (.mkNot Hrhs)); intro lctxTerm
      apply GLift.down.inj; apply propext
      apply Classical.not_imp_iff_and_not

theorem LamGenConv.not_imp_equiv_and_not? : LamGenConv lval LamTerm.not_imp_equiv_and_not? := by
  intro t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.not_imp_equiv_and_not? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv

/-- (a = b) ↔ (a ∨ b) ∧ (¬ a ∨ ¬ b) -/
def LamTerm.propne? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app (.base .prop) (.app _ (.base (.eq _)) lhs) rhs) =>
    .some (.mkAnd (.mkOr lhs rhs) (.mkOr (.mkNot lhs) (.mkNot rhs)))
  | _ => .none

theorem LamTerm.maxEVarSucc_propne?
  (heq : LamTerm.propne? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base .not) (.app (.base .prop) (.app _ (.base (.eq _)) lhs) rhs), Eq.refl _ => by
    simp [mkNot, mkAnd, mkOr, maxEVarSucc, Nat.max, Nat.max_zero_left, Nat.max_zero_right, Nat.max_eq_left]

theorem propne_equiv_eq' {a b : GLift Prop} : (a ≠ b) ↔
  (a.down ∨ b.down) ∧ (¬ a.down ∨ ¬ b.down) := by
  cases a; case up a => cases b; simp [eqGLift_equiv]; rw [equiv_eq (a:=a)]; apply propne_equiv

theorem LamEquiv.propne?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.propne? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' :=
  match t, heq with
  | .app _ (.base .not) (.app (.base .prop) (.app _ (.base (.eq _)) lhs) rhs), Eq.refl _ => by
    cases wft.getArg.getFn.getFn.getBase
    match wft with
    | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) Hrhs) =>
      exists (.mkNot (.mkEq Hlhs Hrhs))
      exists (.mkAnd (.mkOr Hlhs Hrhs) (.mkOr (.mkNot Hlhs) (.mkNot Hrhs)))
      intro lctxTerm; apply GLift.down.inj; apply propext; apply propne_equiv_eq'

theorem LamGenConv.propne? : LamGenConv lval LamTerm.propne? := by
  intro t₁ t₂ heq lctx rty wf
  have hequiv := LamEquiv.propne? wf heq
  have ⟨wf', _⟩ := hequiv; cases (LamWF.unique wf wf').left; exact hequiv
