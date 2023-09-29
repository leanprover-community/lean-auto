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
  apply GLift.down.inj; dsimp; apply eq_false; exact fun h => (h .intro)

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

theorem LamTerm.maxEVarSucc_equalize : (LamTerm.equalize t).maxEVarSucc = t.maxEVarSucc := by
  dsimp [maxEVarSucc]; simp [Nat.max, Nat.max_zero_left, Nat.max_zero_right]

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

def LamTerm.ne_true_equiv_eq_false? (t : LamTerm) : Option LamTerm :=
  match t with
  | .app _ (.base .not) (.app s (.app _ (.base (.eq _)) lhs) (.base .trueE)) =>
    .some (.app s (.app s (.base (.eq s)) lhs) (.base .falseE))
  | _ => .none

theorem LamTerm.maxEVarSucc_ne_true_equiv_eq_false?
  (heq : LamTerm.ne_true_equiv_eq_false? t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc := by
  cases t <;> try cases heq
  case app s fn arg =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      cases arg <;> try cases heq
      case app _ fn arg =>
        cases fn <;> try cases heq
        case app _ fn' arg' =>
          cases fn' <;> try cases heq
          case base b =>
            cases b <;> try cases heq
            cases arg <;> try cases heq
            case base b =>
              cases b <;> try cases heq
              simp [maxEVarSucc, Nat.max]
              simp [Nat.max_zero_left, Nat.max_zero_right]

theorem LamEquiv.ne_true_equiv_eq_false?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
  (heq : LamTerm.ne_true_equiv_eq_false? t = .some t') :
  LamEquiv lval lctx (.base .prop) t t' := by
  cases t <;> try cases heq
  case app s fn arg =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      cases wft.getFn.getBase
      cases arg <;> try cases heq
      case app _ fn arg =>
        cases fn <;> try cases heq
        case app _ fn' arg' =>
          cases fn' <;> try cases heq
          case base b =>
            cases b <;> try cases heq
            cases arg <;> try cases heq
            case base b =>
              cases b <;> try cases heq
              match wft with
              | .ofApp _ (.ofBase .ofNot) (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) Hlhs) (.ofBase .ofTrueE)) =>
                apply LamEquiv.trans (prop_ne_equiv_eq_not Hlhs (.ofBase .ofTrueE))
                apply LamEquiv.congrArg (.ofApp _ (.ofBase (.ofEq _)) Hlhs)
                apply LamEquiv.not_true_equiv_false

theorem LamThmEquiv.ne_true_equiv_eq_false?
  (wft : LamThmWF lval lctx s t)
  (heq : LamTerm.ne_true_equiv_eq_false? t = .some t') :
  LamThmEquiv lval lctx (.base .prop) t t' :=
  fun lctx' => LamEquiv.ne_true_equiv_eq_false? (wft lctx') heq