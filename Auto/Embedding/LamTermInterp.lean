import Auto.Embedding.LamBase
open Lean

namespace Auto.Embedding.Lam

-- Interpreting while typechecking a `λ` term. If the term fails to
--   typecheck at some point, return `⟨.base .prop, GLift.up False⟩`
--   as a default value.
def LamTerm.interp.{u} (lval : LamValuation.{u}) (lctxTy : Nat → LamSort) :
  (t : LamTerm) → (s : LamSort) ×
    ((lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) → s.interp lval.tyVal)
| .atom n => ⟨lval.lamVarTy n, fun _ => lval.varVal n⟩
| .etom n => ⟨lval.lamEVarTy n, fun _ => lval.eVarVal n⟩
| .base b =>
  ⟨b.lamCheck lval.toLamTyVal,
    fun _ => LamBaseTerm.interp lval b⟩
| .bvar n => ⟨lctxTy n, fun lctxTerm => lctxTerm n⟩
| .lam s body =>
  match LamTerm.interp lval (pushLCtx s lctxTy) body with
  | ⟨bodyTy, bodyInterp⟩ =>
    ⟨.func s bodyTy, fun lctxTerm (x : s.interp lval.tyVal) =>
      bodyInterp (pushLCtxDep (rty:=lctxTy) x lctxTerm)⟩
| .app s fn arg =>
  match LamTerm.interp lval lctxTy fn with
  | ⟨fnTy, fnInterp⟩ =>
    match LamTerm.interp lval lctxTy arg with
    | ⟨argTy, argInterp⟩ =>
      match fnTy with
      | .atom _ => ⟨.base .prop, fun _ => GLift.up False⟩
      | .base _ => ⟨.base .prop, fun _ => GLift.up False⟩
      | .func argTy' resTy =>
        match heq : LamSort.beq argTy' argTy, heqa : LamSort.beq argTy' s with
        | true, true =>
          have heq' := LamSort.eq_of_beq_eq_true heq;
          ⟨resTy, fun lctxTerm => (fnInterp lctxTerm) (heq' ▸ argInterp lctxTerm)⟩
        | true,  false => ⟨.base .prop, fun _ => GLift.up False⟩
        | false, true  => ⟨.base .prop, fun _ => GLift.up False⟩
        | false, false => ⟨.base .prop, fun _ => GLift.up False⟩

def LamTerm.interpAsProp.{u}
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) (t : LamTerm) : GLift.{1, u} Prop :=
  match t.interp lval lctxTy with
  | ⟨.base .prop, tInterp⟩ => tInterp lctxTerm
  | _ => GLift.up False

theorem LamTerm.interp_equiv
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort) (lwf : LamWF lval.toLamTyVal ⟨lctxTy, t, rty⟩) :
  ⟨rty, fun lctxTerm => LamWF.interp lval lctxTy lctxTerm lwf⟩ = LamTerm.interp lval lctxTy t := by
  induction t generalizing lctxTy rty <;> try (cases lwf; rfl)
  case base b =>
    let .ofBase bH := lwf; apply eq_sigma_of_heq
    case h₁ => rw [LamBaseTerm.lamCheck_of_LamWF bH]
    case h₂ =>
      apply HEq.funext; intros _; apply LamBaseTerm.interp_equiv
  case lam s t IH =>
    let .ofLam bodyTy H := lwf; apply eq_sigma_of_heq
    case h₁ => rw [← IH _ H]
    case h₂ =>
      dsimp [LamWF.interp, interp];
      apply HEq.funext; intros lctxTerm
      apply HEq.funext; intros x
      rw [← IH _ H]
  case app s fn arg IHFn IHArg =>
    let .ofApp _ HFn HArg := lwf
    dsimp [LamWF.interp, interp]
    have IHFn' := heq_of_eq_sigma (IHFn _ HFn)
    have IHArg' := heq_of_eq_sigma (IHArg _ HArg)
    revert IHFn' IHArg'
    match LamTerm.interp lval lctxTy fn with
    | ⟨fnTy, fnInterp⟩ =>
      match LamTerm.interp lval lctxTy arg with
      | ⟨argTy, argInterp⟩ =>
        dsimp; intros IHFn' IHArg'
        let ⟨fnTyEq, fnInterpEq⟩ := IHFn'
        let ⟨argTyEq, argInterpEq⟩ := IHArg'
        cases fnTyEq; cases argTyEq; cases fnInterpEq; cases argInterpEq
        dsimp; rw [LamSort.beq_refl]

theorem LamThmValid.getDefault (H : LamThmValid lval [] t) :
  GLift.down (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm lval.tyVal) t) := by
  have ⟨wf, H⟩ := H dfLCtxTy
  have hTermEquiv := LamTerm.interp_equiv _ dfLCtxTy wf
  dsimp [LamTerm.interpAsProp]; rw [← hTermEquiv]; apply H

theorem LamThmValid.getFalse (H : LamThmValid lval [] (.base .falseE)) : False :=
  LamThmValid.getDefault H

-- Only accepts propositions `p` without loose bound variables
theorem LamThmValid.ofInterpAsProp
  (lval : LamValuation) (p : LamTerm)
  (h₁ : LamTerm.lamCheck? lval.toLamTyVal dfLCtxTy p = .some (.base .prop))
  (h₂ : (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down)
  (h₃ : p.maxLooseBVarSucc = 0) : LamThmValid lval [] p := by
  intros lctx';
  have h₁' := Eq.trans (LamTerm.lamCheck?_irrelevence (lctx₁:=lctx') (by
    intro n hlt; rw [h₃] at hlt; cases hlt)) h₁
  have wf₁ := LamWF.ofLamCheck? h₁'; exists wf₁; intros lctxTerm
  have wf₂ := LamWF.ofLamCheck? h₁
  have hieq := LamTerm.interp_equiv _ _ wf₂
  dsimp [LamTerm.interpAsProp] at h₂; rw [← hieq] at h₂; dsimp at h₂
  apply Eq.mp _ h₂
  apply congrArg; apply eq_of_heq;
  apply LamWF.interp_lctxIrrelevance (lctxTy₁:=dfLCtxTy) (lctxTerm₁:=dfLCtxTerm _) _ _
  intros n h; rw [h₃] at h; cases h

structure InterpState where
  -- Let `n := lctxTyRev.size`
  lctxTyRev   : Array LamSort -- Reversed
  -- Required : `lctxTermRev.size = n`
  lctxTermRev : Array FVarId  -- Reversed
  -- Required : `lctxDrop[i] ≝ lctxTermRev[:(i+1)].data ≝ lctxTerm[(n-i-1):]`
  lctxDrop    : Array FVarId
  -- Required : `eqFact[i][j] : lctxTerm[i:].drop j = lctxTerm[i+j:]`
  eqFact      : HashMap (Nat × Nat) FVarId

def LamTerm.interpEq.{u}
  (lval : LamValuation.{u}) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (t : LamTerm) (s : LamSort) {α : Type u} (val : α) : Prop :=
  s.interp lval.tyVal = α ∧
    match t.interp lval (fun n => (lctx.getD n ⟨.base .prop, GLift.up False⟩).fst) with
    | ⟨s', interp'⟩ => s' = s ∧ HEq (interp' (fun n => (lctx.getD n ⟨.base .prop, GLift.up False⟩).snd)) val

theorem LamTerm.interpEq_atom
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : (lval.lamVarTy n).interp lval.tyVal) (h : lval.varVal n = val) :
  LamTerm.interpEq lval lctx (.atom n) (lval.lamVarTy n) val := by
  apply And.intro rfl; dsimp [interp]; apply And.intro rfl; rw [h]

theorem LamTerm.interpEq_etom
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : (lval.lamEVarTy n).interp lval.tyVal) (h : lval.eVarVal n = val) :
  LamTerm.interpEq lval lctx (.etom n) (lval.lamEVarTy n) val := by
  apply And.intro rfl; dsimp [interp]; apply And.intro rfl; rw [h]

theorem LamTerm.interpEq_base
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : (LamBaseTerm.lamCheck lval.toLamTyVal b).interp lval.tyVal) (h : b.interp lval = val) :
  LamTerm.interpEq lval lctx (.base b) (b.lamCheck lval.toLamTyVal) val := by
  apply And.intro rfl; dsimp [interp]; apply And.intro rfl; rw [h]

theorem LamTerm.interpEq_bvar
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (s : LamSort) (val : s.interp lval.tyVal) (h : lctx.get? n = .some ⟨s, val⟩) :
  LamTerm.interpEq lval lctx (.bvar n) s val := by
  apply And.intro rfl; dsimp [interp]; apply And.intro <;>
    (rw [List.getD_eq_get?, h]; rfl)

end Auto.Embedding.Lam