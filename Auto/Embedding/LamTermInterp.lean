import Auto.Embedding.LamSystem
import Auto.Lib.MonadUtils
import Auto.Lib.MetaState
open Lean

namespace Auto.Embedding.Lam

/--
  Interpreting while typechecking a `λ` term. If the term fails to
    typecheck at some point, return `⟨.base .prop, GLift.up False⟩`
    as a default value.
-/
noncomputable def LamTerm.interp.{u} (lval : LamValuation.{u}) (lctxTy : Nat → LamSort) :
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
        match LamSort.beq argTy' s with
        | true =>
          match heq : LamSort.beq argTy' argTy with
          | true =>
            have heq' := LamSort.eq_of_beq_eq_true heq;
            ⟨resTy, fun lctxTerm => (fnInterp lctxTerm) (heq' ▸ argInterp lctxTerm)⟩
          | false => ⟨.base .prop, fun _ => GLift.up False⟩
        | false  => ⟨.base .prop, fun _ => GLift.up False⟩

theorem LamTerm.interp_substLCtxTerm
  (lval : LamValuation.{u}) {lctxTy lctxTy' : Nat → LamSort}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm' : ∀ n, (lctxTy' n).interp lval.tyVal}
  (HLCtxTyEq : lctxTy = lctxTy') (HLCtxTermEq : HEq lctxTerm lctxTerm') :
  HEq ((interp lval lctxTy t).snd lctxTerm) ((interp lval lctxTy' t).snd lctxTerm') := by
  cases HLCtxTyEq; cases HLCtxTermEq; apply HEq.refl

noncomputable def LamTerm.interpAsProp.{u}
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
      simp [LamWF.interp];
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
        dsimp; rw [LamSort.beq_refl]; rfl

theorem LamThmValid.getDefault (H : LamThmValid lval [] t) :
  GLift.down (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm lval.tyVal) t) := by
  have ⟨wf, H⟩ := H dfLCtxTy
  have hTermEquiv := LamTerm.interp_equiv _ dfLCtxTy wf
  dsimp [LamTerm.interpAsProp]; rw [← hTermEquiv]; apply H

theorem LamThmValid.getFalse (H : LamThmValid lval [] (.base .falseE)) : False :=
  LamThmValid.getDefault H

/-- Only accepts propositions `p` without loose bound variables -/
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

def LamTerm.lamCheck?Eq
  (lval : LamValuation.{u}) (lctx : List LamSort) (t : LamTerm) (s : LamSort) :=
  t.lamCheck? lval.toLamTyVal (pushLCtxs lctx dfLCtxTy) = s

def LamTerm.lamCheck?Eq'
  (lval : LamValuation.{u}) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (t : LamTerm) (s : LamSort) :=
  t.lamCheck? lval.toLamTyVal (fun n => (pushLCtxs lctx (fun _ => ⟨.base .prop, GLift.up False⟩) n).fst) = .some s

theorem LamTerm.lamCheck?Eq'_ofLamCheck?Eq
  (H : LamTerm.lamCheck?Eq lval (lctx.map Sigma.fst) t s) :
  LamTerm.lamCheck?Eq' lval lctx t s := by
  dsimp [LamTerm.lamCheck?Eq'];
  conv => enter [1, 2, n]; rw [pushLCtxs_comm (f:=Sigma.fst)]
  exact H

def LamTerm.interpEq.{u}
  (lval : LamValuation.{u}) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (t : LamTerm) {α : Type u} (val : α) : Prop :=
    match t.interp lval (fun n => (pushLCtxs lctx (fun _ => ⟨.base .prop, GLift.up False⟩) n).fst) with
    | ⟨_, interp'⟩ => HEq (interp' (fun n => (pushLCtxs lctx (fun _ => ⟨.base .prop, GLift.up False⟩) n).snd)) val

theorem LamTerm.interpAsProp_of_interpEq {ty : Prop} (proof : ty)
  (h₁ : LamTerm.lamCheck?Eq' lval .nil p (.base .prop))
  (h₂ : LamTerm.interpEq lval .nil p (GLift.up ty)) :
  (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down := by
  dsimp [LamTerm.interpAsProp]
  have h₁' : p.lamCheck? lval.toLamTyVal dfLCtxTy = .some (.base .prop) := h₁
  have wft := LamWF.ofLamCheck? h₁'
  have hInterp := LamTerm.interp_equiv _ _ wft
  rw [← hInterp]; dsimp; dsimp [interpEq] at h₂
  rw [pushLCtxs_nil, ← hInterp] at h₂; dsimp at h₂
  rw [eq_of_heq h₂]; exact proof

theorem LamTerm.lamCheck?Eq'_atom :
  LamTerm.lamCheck?Eq' lval lctx (.atom n) (lval.lamVarTy n) := rfl

theorem LamTerm.lamCheck?Eq'_etom :
  LamTerm.lamCheck?Eq' lval lctx (.etom n) (lval.lamEVarTy n) := rfl

theorem LamTerm.lamCheck?Eq'_base :
  LamTerm.lamCheck?Eq' lval lctx (.base b) (LamBaseTerm.lamCheck lval.toLamTyVal b) := rfl

theorem LamTerm.lamCheck?Eq'_bvar {lval lctx n s val}
  (h : lctx[n]? = .some ⟨s, val⟩) :
  LamTerm.lamCheck?Eq' lval lctx (.bvar n) s := by
  dsimp [lamCheck?Eq', lamCheck?]; have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
  rw [pushLCtxs_lt hlt, List.getD_eq_getElem?_getD, h]; rfl

theorem LamTerm.lamCheck?Eq'_lam {lval argTy val lctx body s}
  (h : LamTerm.lamCheck?Eq' lval (⟨argTy, val⟩ :: lctx) body s) :
  LamTerm.lamCheck?Eq' lval lctx (.lam argTy body) (.func argTy s) := by
  dsimp [lamCheck?Eq', lamCheck?]; dsimp [lamCheck?Eq'] at h
  rw [pushLCtxs_cons] at h
  conv at h =>
    enter [1, 2, n]; rw [pushLCtx_comm (f:=Sigma.fst)]
  dsimp at h; rw [h]

theorem LamTerm.lamCheck?Eq'_app {lval lctx fn argTy resTy arg}
  (hFn : LamTerm.lamCheck?Eq' lval lctx fn (.func argTy resTy))
  (hArg : LamTerm.lamCheck?Eq' lval lctx arg argTy) :
  LamTerm.lamCheck?Eq' lval lctx (.app argTy fn arg) resTy := by
  dsimp [lamCheck?Eq', lamCheck?]; rw [hFn, hArg]; dsimp; rw [LamSort.beq_refl]

theorem LamTerm.interpEq_atom
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : (lval.lamVarTy n).interp lval.tyVal) (h : lval.varVal n = val) :
  LamTerm.interpEq lval lctx (.atom n) val := heq_of_eq h

theorem LamTerm.interpEq_etom
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : (lval.lamEVarTy n).interp lval.tyVal) (h : lval.eVarVal n = val) :
  LamTerm.interpEq lval lctx (.etom n) val := heq_of_eq h

theorem LamTerm.interpEq_base
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : (LamBaseTerm.lamCheck lval.toLamTyVal b).interp lval.tyVal) (h : b.interp lval = val) :
  LamTerm.interpEq lval lctx (.base b) val := heq_of_eq h

theorem LamTerm.interpEq_bvar
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (s : LamSort) (val : s.interp lval.tyVal) (h : lctx[n]? = .some ⟨s, val⟩) :
  LamTerm.interpEq lval lctx (.bvar n) val := by
  dsimp [interpEq, interp]; have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
  rw [pushLCtxs_lt hlt, List.getD_eq_getElem?_getD, h]; rfl

theorem LamTerm.interpEq_lam
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  (val : argTy.interp lval.tyVal → β)
  (hBody : ∀ x, LamTerm.interpEq lval (⟨argTy, x⟩ :: lctx) t (val x)) :
  LamTerm.interpEq lval lctx (.lam argTy t) val := by
  dsimp [interpEq, interp]; apply HEq.funext; intro x
  dsimp [interpEq] at hBody; apply HEq.trans _ (hBody x); rw [pushLCtxs_cons]
  apply LamTerm.interp_substLCtxTerm
  case HLCtxTyEq =>
    funext n; rw [pushLCtx_comm (f:=Sigma.fst)]
  case HLCtxTermEq =>
    apply HEq.funext; intro n; cases n <;> try rfl

theorem LamTerm.interpEq_app
  (lval : LamValuation) (lctx : List ((s : LamSort) × s.interp lval.tyVal))
  {argTy resTy : LamSort}
  (fnChk : LamTerm.lamCheck?Eq' lval lctx fn (.func argTy resTy))
  (argChk : LamTerm.lamCheck?Eq' lval lctx arg argTy)
  (fnVal : argTy.interp lval.tyVal → resTy.interp lval.tyVal) (argVal : argTy.interp lval.tyVal)
  (hFn : LamTerm.interpEq lval lctx fn fnVal)
  (hArg : LamTerm.interpEq lval lctx arg argVal) :
  LamTerm.interpEq lval lctx (.app argTy fn arg) (fnVal argVal) := by
  revert hFn hArg; dsimp [interpEq, interp]
  let lctxTy := fun n => (pushLCtxs lctx (fun _ => ⟨.base .prop, GLift.up False⟩) n).fst
  have fnChk' := (heq_of_eq_sigma (LamTerm.interp_equiv _ _ (LamWF.ofLamCheck? fnChk))).left
  have argChk' := (heq_of_eq_sigma (LamTerm.interp_equiv _ _ (LamWF.ofLamCheck? argChk))).left
  revert fnChk' argChk'
  match interp lval lctxTy fn with
  | ⟨fnTy', fnInterp'⟩ =>
    match interp lval lctxTy arg with
    | ⟨argTy', argInterp'⟩ =>
      dsimp; intro fnChk' argChk' hFn hArg
      cases fnChk'; cases argChk'; dsimp
      rw [LamSort.beq_refl]; dsimp
      cases hFn; cases hArg; rfl

namespace Interp

structure State where
  sortFVars    : Array FVarId               := #[]
  sortMap      : Std.HashMap LamSort FVarId     := {}
  -- Let `n := lctxTyRev.size`
  -- Reversed
  lctxTyRev    : Array LamSort              := #[]
  -- Required : `lctxTermRev.size = n`
  -- Reversed
  lctxTermRev  : Array FVarId               := #[]
  -- Required : `lctxTyDrop[i] ≝ lctxTyRev[:(i+1)].data ≝ lctxTerm[(n-i-1):]`
  lctxTyDrop   : Array FVarId               := #[]
  -- Required : `tyEqFact[i][j] : lctxTy[i:].drop j = lctxTy[i+j:]`
  typeEqFact   : Std.HashMap (Nat × Nat) FVarId := {}
  -- Required : `lctxTermDrop[i] ≝ lctxTermRev[:(i+1)].data ≝ lctxTerm[(n-i-1):]`
  lctxTermDrop : Array FVarId               := #[]
  -- Required : `termEqFact[i][j] : lctxTerm[i:].drop j = lctxTerm[i+j:]`
  termEqFact   : Std.HashMap (Nat × Nat) FVarId := {}
  -- Required : `lctxCon[i] : lctxTerm[i].map Sigma.snd = lctxTy[i]`
  lctxCon      : Array FVarId               := #[]

abbrev InterpM := StateRefT State MetaState.MetaStateM

#genMonadState InterpM

def getLCtxTy! (idx : Nat) : InterpM LamSort := do
  let lctxTyRev ← getLctxTyRev
  if idx ≥ lctxTyRev.size then
    throwError "{decl_name%} :: Index out of bound"
  match lctxTyRev[idx]? with
  | .some s => return s
  | .none => throwError "{decl_name%} :: Unexpected error"

/--
  Turning a sort into `fvar` in a hash-consing manner
  For example, for `.func (.atom 0) (.atom 0)`, we'll have
  1. .atom 0 → fvar₀ := .atom 0
  2. .func (.atom 0) (.atom 0) → fvar₁ := .func fvar₀ fvar₀
-/
def sort2FVarId (s : LamSort) : InterpM FVarId := do
  let sortMap ← getSortMap
  let userName := (`interpsf).appendIndexAfter (← getSortMap).size
  match sortMap.get? s with
  | .some id => return id
  | .none =>
    match s with
    | .func argTy resTy =>
      let argId ← sort2FVarId argTy
      let resId ← sort2FVarId resTy
      let fvarId ← MetaState.withLetDecl userName (.const ``LamSort [])
        (Lean.mkApp2 (.const ``LamSort.func []) (.fvar argId) (.fvar resId)) .default
      setSortFVars ((← getSortFVars).push fvarId)
      return fvarId
    | s =>
      let fvarId ← MetaState.withLetDecl userName (.const ``LamSort []) (Lean.toExpr s) .default
      setSortFVars ((← getSortFVars).push fvarId)
      return fvarId

/-- Turning all sorts occurring in a `LamTerm` into `fvar`, in a hash-consing manner -/
def collectSortFor (ltv : LamTyVal) : LamTerm → InterpM LamSort
| .atom n => do
  let _ ← sort2FVarId (ltv.lamVarTy n)
  return ltv.lamVarTy n
| .etom _ => throwError "{decl_name%} :: etoms should not occur here"
| .base b => do
  let s := b.lamCheck ltv
  let _ ← sort2FVarId s
  return s
| .bvar n => do
  let s ← getLCtxTy! n
  let _ ← sort2FVarId s
  return s
| .lam s body => do
  let _ ← sort2FVarId s
  let bodyTy ← withLCtxTy s (collectSortFor ltv body)
  let _ ← sort2FVarId (.func s bodyTy)
  return (.func s bodyTy)
| .app s fn arg => do
  let fnTy ← collectSortFor ltv fn
  let argTy ← collectSortFor ltv arg
  match fnTy with
  | .func argTy' resTy =>
    if argTy' == argTy && argTy' == s then
      return resTy
    else
      throwError "{decl_name%} :: Application type mismatch"
  | _ => throwError "{decl_name%} :: Malformed application"
where withLCtxTy {α : Type} (s : LamSort) (k : InterpM α) : InterpM α := do
  let lctxTyRev ← getLctxTyRev
  setLctxTyRev (lctxTyRev.push s)
  let ret ← k
  setLctxTyRev lctxTyRev
  return ret

end Interp

end Auto.Embedding.Lam
