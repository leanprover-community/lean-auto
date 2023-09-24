import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

abbrev LamEquiv (lval : LamValuation) (lctx : Nat → LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∃ (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, rty⟩),
  ∃ (wf₂ : LamWF lval.toLamTyVal ⟨lctx, t₂, rty⟩),
    ∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal),
      LamWF.interp lval lctx lctxTerm wf₁ =
        LamWF.interp lval lctx lctxTerm wf₂

-- Semantic Equivalence
-- Note that we do not expect to reorder binders or remove
--   unused binders, because doing so makes the term not equivalent
--   to the original one
def LamThmEquiv (lval : LamValuation) (lctx : List LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamEquiv lval (pushLCtxs lctx lctx') rty t₁ t₂

theorem LamThmWF.ofLamThmEquiv_l (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₁ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨wf, _⟩ := teq lctx'; ⟨wf⟩))

theorem LamThmWF.ofLamThmEquiv_r (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₂ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨_, ⟨wf, _⟩⟩ := teq lctx'; ⟨wf⟩))

theorem LamValid.ofLamEquiv
  (leq : LamEquiv lval lctx s t₁ t₂) : LamValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  let ⟨wf₁, ⟨wf₂, h₁₂⟩⟩ := leq; ⟨LamWF.mkEq wf₁ wf₂, h₁₂⟩

theorem LamThmValid.ofLamThmEquiv
  {lval : LamValuation} (lctx : List LamSort)
  (eT : LamThmEquiv lval lctx s t₁ t₂) :
  LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) := fun lctx' => LamValid.ofLamEquiv (eT lctx')

theorem LamEquiv.ofLamValid
  (heq : LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamEquiv lval lctx s t₁ t₂ :=
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq
  ⟨wft₁, ⟨wft₂, heq'⟩⟩ 

theorem LamEquiv.ofLamValidSymm
  (heq : LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamEquiv lval lctx s t₂ t₁ :=
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq
  ⟨wft₂, wft₁, fun _ => Eq.symm (heq' _)⟩

theorem LamThmEquiv.ofLamThmValid
  {lval : LamValuation} (lctx : List LamSort)
  (heq : LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamThmEquiv lval lctx s t₁ t₂ :=
  fun lctx' => LamEquiv.ofLamValid (heq lctx')

theorem LamEquiv.eqLamValid :
  LamEquiv lval lctx s t₁ t₂ = (LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :=
  propext (Iff.intro LamValid.ofLamEquiv LamEquiv.ofLamValid)

theorem LamThmEquiv.eqLamThmValid
  {lval : LamValuation} (lctx : List LamSort) :
  LamThmEquiv lval lctx s t₁ t₂ = LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  propext (Iff.intro (LamThmValid.ofLamThmEquiv _) (LamThmEquiv.ofLamThmValid _))

theorem LamValid.mpLamEquiv (hp : LamValid lval lctx p₁)
  (hequiv : LamEquiv lval lctx s p₁ p₂) : LamValid lval lctx p₂ := by
  let ⟨wfp₁, hp₁⟩ := hp
  let ⟨wfp₁', ⟨wfp₂, heqp⟩⟩ := hequiv
  rcases LamWF.unique wfp₁ wfp₁' with ⟨⟨⟩, ⟨⟩⟩
  exact ⟨wfp₂, fun lctxTerm' => heqp _ ▸ hp₁ lctxTerm'⟩

theorem LamThmValid.mpLamThmEquiv
  {lval : LamValuation} (lctx : List LamSort)
  (hequiv : LamThmEquiv lval lctx (.base .prop) p₁ p₂)
  (hp : LamThmValid lval lctx p₁) : LamThmValid lval lctx p₂ := by
  intros lctx';
  let ⟨wfp₁, ⟨wfp₂, heqp⟩⟩ := hequiv lctx'
  exists wfp₂; intro lctxTerm'; rw [← heqp]
  let ⟨wfp₁', hp₁⟩ := hp lctx'
  have wfeq : wfp₁ = wfp₁' := eq_of_heq (LamWF.unique wfp₁ wfp₁').right
  cases wfeq; apply hp₁

theorem LamEquiv.refl {lval : LamValuation} (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t t := ⟨wf, ⟨wf, fun _ => rfl⟩⟩

theorem LamThmEquiv.refl {lval : LamValuation} (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t := fun lctx' => LamEquiv.refl (wf lctx')

theorem LamEquiv.eq {lval : LamValuation} (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩)
  (heq : t₁ = t₂) : LamEquiv lval lctx s t₁ t₂ := heq ▸ LamEquiv.refl wf

theorem LamThmEquiv.eq {lval : LamValuation} (wf : LamThmWF lval lctx s t₁)
  (heq : t₁ = t₂) : LamThmEquiv lval lctx s t₁ t₂ := fun lctx => LamEquiv.eq (wf lctx) heq

theorem LamEquiv.symm {lval : LamValuation} (e : LamEquiv lval lctx s a b) : LamEquiv lval lctx s b a :=
  let ⟨wfa, ⟨wfb, eq⟩⟩ := e; ⟨wfb, ⟨wfa, fun lctxTerm => Eq.symm (eq lctxTerm)⟩⟩

theorem LamThmEquiv.symm {lval : LamValuation} (e : LamThmEquiv lval lctx rty a b) :
  LamThmEquiv lval lctx rty b a := fun lctx => LamEquiv.symm (e lctx)

theorem LamEquiv.trans {lval : LamValuation}
  (eab : LamEquiv lval lctx s a b) (ebc : LamEquiv lval lctx s b c) : LamEquiv lval lctx s a c := by
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := eab; let ⟨wfb', ⟨wfc, eqbc⟩⟩ := ebc
  rcases LamWF.unique wfb wfb' with ⟨_, ⟨⟩⟩
  exact ⟨wfa, ⟨wfc, fun lctxTerm => by rw [eqab, ←eqbc]⟩⟩

theorem LamEquiv.trans' {lval : LamValuation}
  (eab : LamEquiv lval lctx s a b) (ebc : LamEquiv lval lctx s' b c) : LamEquiv lval lctx s a c := by
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := eab; let ⟨wfb', ⟨wfc, eqbc⟩⟩ := ebc
  rcases LamWF.unique wfb wfb' with ⟨⟨⟩, ⟨⟩⟩
  exact ⟨wfa, ⟨wfc, fun lctxTerm => by rw [eqab, ←eqbc]⟩⟩

theorem LamThmEquiv.trans
  (e₁ : LamThmEquiv lval lctx rty a b) (e₂ : LamThmEquiv lval lctx rty b c) :
  LamThmEquiv lval lctx rty a c :=
  fun lctx' => LamEquiv.trans (e₁ lctx') (e₂ lctx')

theorem LamEquiv.ofLam {lval : LamValuation} (e : LamEquiv lval (pushLCtx w lctx) s a b) :
  LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := e; ⟨.ofLam _ wfa, .ofLam _ wfb, fun _ => funext (fun _ => eqab _)⟩

theorem LamThmEquiv.ofLam (e : LamThmEquiv lval (w :: lctx) s a b) :
  LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) := fun lctx' =>
    LamEquiv.ofLam (pushLCtxs_cons _ _ ▸ e lctx')

theorem LamEquiv.fromLam
  (e : LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamEquiv lval (pushLCtx w lctx) s a b :=
  let ⟨.ofLam _ wfa, .ofLam _ wfb, eqlab⟩ := e
  ⟨wfa, wfb, fun lctxTerm =>
    let h := congrFun (eqlab (fun n => lctxTerm (.succ n))) (lctxTerm 0)
    by
      dsimp [LamWF.interp] at h
      apply Eq.trans ?left (Eq.trans h ?right) <;>
        apply eq_of_heq
      case left =>
        apply LamWF.interp_heq <;> try rfl
        apply HEq.symm; apply pushDep_popDep_eq lctxTerm
      case right =>
        apply LamWF.interp_heq <;> try rfl
        apply pushDep_popDep_eq⟩

theorem LamThmEquiv.fromLam {lval : LamValuation}
  (e : LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamThmEquiv lval (w :: lctx) s a b := fun lctx' => by
  rw [pushLCtxs_cons]; apply LamEquiv.fromLam (e lctx')

theorem LamEquiv.eqLam :
  LamEquiv lval (pushLCtx w lctx) s a b = LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro LamEquiv.ofLam LamEquiv.fromLam)

theorem LamThmEquiv.eqLam {lval : LamValuation} :
  LamThmEquiv lval (w :: lctx) s a b = LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro LamThmEquiv.ofLam LamThmEquiv.fromLam)

theorem LamEquiv.congr_mkLamFN :
  LamEquiv lval (pushLCtxs l lctx) s t₁ t₂ ↔ LamEquiv lval lctx (s.mkFuncsRev l) (.mkLamFN t₁ l) (.mkLamFN t₂ l) := by
  induction l generalizing t₁ t₂ s
  case nil => exact Iff.intro id id
  case cons ls l IH =>
    dsimp [LamTerm.mkLamFN, LamWF.mkLamFN]; apply Iff.trans _ IH
    apply Iff.intro
    case mp =>
      intro H; apply LamEquiv.ofLam; apply Eq.mp _ H
      rw [pushLCtxs_cons]
    case mpr =>
      intro H; rw [pushLCtxs_cons]
      apply LamEquiv.fromLam; apply H

theorem LamEquiv.congr
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) :=
  let ⟨wfFn₁, wfFn₂, HFn⟩ := eFn
  let ⟨wfArg₁, wfArg₂, HArg⟩ := eArg
  ⟨.ofApp _ wfFn₁ wfArg₁, .ofApp _ wfFn₂ wfArg₂, fun _ => _root_.congr (HFn _) (HArg _)⟩

theorem LamThmEquiv.congr {lval : LamValuation}
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := fun lctx' =>
    LamEquiv.congr (eFn lctx') (eArg lctx')

theorem LamEquiv.congrFun
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamEquiv.congr eFn (LamEquiv.refl wfArg)

theorem LamThmEquiv.congrFun {lval : LamValuation}
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamThmWF lval lctx argTy arg) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamThmEquiv.congr eFn (LamThmEquiv.refl wfArg)

theorem LamEquiv.congrArg
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn, .func argTy resTy⟩)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamEquiv.congr (LamEquiv.refl wfFn) eArg

theorem LamThmEquiv.congrArg {lval : LamValuation}
  (wfFn : LamThmWF lval lctx (.func argTy resTy) fn)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamThmEquiv.congr (LamThmEquiv.refl wfFn) eArg

def LamWF.generalizeTy (wf : LamWF ltv ⟨lctx, t, s⟩) :
  (s : LamSort) × LamWF ltv ⟨lctx, t, s⟩ := ⟨s, wf⟩

theorem LamEquiv.congrs {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hFn : LamEquiv lval lctx fnTy fn₁ fn₂)
  (hArgs : HList ((fun (s, arg₁, arg₂) => LamEquiv lval lctx s arg₁ arg₂)) args) :
  LamEquiv lval lctx resTy
    (LamTerm.mkAppN fn₁ (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn₂ (args.map (fun (s, _, t₂) => (s, t₂)))) := by
  induction args generalizing fn₁ fn₂ fnTy
  case nil =>
    have ⟨wfFn, _⟩ := hFn
    rcases LamWF.unique wfFn wfApp with ⟨⟨⟩, ⟨⟩⟩; apply hFn
  case cons head tail IH =>
    match head with
    | ⟨s, t₁, t₂⟩ =>
      have ⟨wfFn, _⟩ := hFn
      have ⟨fnTy', wfAp⟩ := LamWF.generalizeTy
        (wfApp.fnWFOfMkAppN (args:=tail.map (fun (s, t₁, snd) => (s, t₁))))
      rcases LamWF.unique wfFn wfAp.getFn with ⟨⟨⟩, ⟨⟩⟩
      apply IH wfApp (fnTy:=fnTy'); dsimp [LamTerm.mkAppN] at wfApp
      case hFn =>
        apply LamEquiv.congr hFn
        match hArgs with
        | .cons hHead _ => apply hHead
      case hArgs =>
        match hArgs with
        | .cons _ hTail => apply hTail

theorem LamEquiv.congrArgs {lval : LamValuation} {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hArgs : HList ((fun (s, arg₁, arg₂) => LamEquiv lval lctx s arg₁ arg₂)) args) :
  LamEquiv lval lctx resTy
    (LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn (args.map (fun (s, _, t₂) => (s, t₂))))
   := LamEquiv.congrs wfApp (LamEquiv.refl wfApp.fnWFOfMkAppN) hArgs

theorem LamEquiv.congrFunN {lval : LamValuation} {args : List (LamSort × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ args, resTy⟩)
  (hFn : LamEquiv lval lctx fnTy fn₁ fn₂) :
  LamEquiv lval lctx resTy (LamTerm.mkAppN fn₁ args) (LamTerm.mkAppN fn₂ args) := by
  let masterArr := args.map (fun (s, arg) => (s, arg, arg))
  have eq₁ : args = masterArr.map (fun (s, arg₁, _) => (s, arg₁)) := by
    rw [List.map_map]; rw [List.map_equiv _ id, List.map_id];
    intro x; cases x; rfl
  have eq₂ : args = masterArr.map (fun (s, _, arg₂) => (s, arg₂)) := by
    rw [List.map_map]; rw [List.map_equiv _ id, List.map_id];
    intro x; cases x; rfl
  have eqt₂ : LamTerm.mkAppN fn₂ args = LamTerm.mkAppN fn₂ (masterArr.map (fun (s, _, arg₂) => (s, arg₂))) := by
    rw [← eq₂]
  rw [eqt₂]; revert wfApp; rw [eq₁]; intro wfApp; apply LamEquiv.congrs wfApp hFn
  apply HList.toMapTy; dsimp [Function.comp]
  apply HList.map (β:=fun (s, t) => LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
    (fun (s, t) => LamEquiv.refl (s:=s) (t:=t))
  have wfArgs := wfApp.argsWFOfMkAppN; rw [← eq₁] at wfArgs; exact wfArgs

theorem LamEquiv.forall_congr {lval : LamValuation}
  (eFn : LamEquiv lval (pushLCtx argTy lctx) (.base .prop) fn₁ fn₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEF argTy fn₁) (.mkForallEF argTy fn₂) := by
  have ⟨wfFn₁, wfFn₂, eqFn⟩ := eFn
  exists LamWF.mkForallEF wfFn₁, LamWF.mkForallEF wfFn₂; intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, forallLiftFn]
  apply _root_.congrArg; apply _root_.forall_congr; intro x
  apply _root_.congrArg; apply eqFn

theorem LamEquiv.congr_mkForallEFN
  (H : LamEquiv lval (pushLCtxs l lctx) (.base .prop) t₁ t₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEFN t₁ l) (.mkForallEFN t₂ l) := by
  induction l generalizing t₁ t₂
  case nil => exact H
  case cons ls l IH =>
    dsimp [LamTerm.mkForallEFN, LamWF.mkForallEFN]; apply IH
    apply LamEquiv.forall_congr; apply Eq.mp _ H
    rw [pushLCtxs_cons]

def LamTerm.app_bvarLift_bvar0 (s : LamSort) (t : LamTerm) : LamTerm :=
  .app s t.bvarLift (.bvar 0)

def LamWF.app_bvarLift_bvar0 (wft : LamWF ltv ⟨lctx, t, .func argTy resTy⟩) :
  LamWF ltv ⟨pushLCtx argTy lctx, t.app_bvarLift_bvar0 argTy, resTy⟩ :=
  LamWF.ofApp _ wft.ofBVarLift .pushLCtx_ofBVar

theorem LamWF.interp_app_bvarLift_bvar0
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .func argTy resTy⟩) :
  LamWF.interp lval (pushLCtx argTy lctx) (pushLCtxDep x lctxTerm) wft.app_bvarLift_bvar0 =
    LamWF.interp (rty:=.func _ _) lval lctx lctxTerm wft x := by
  dsimp [LamWF.interp]; rw [← LamWF.interp_ofBVarLift]

def LamTerm.etaExpand1 (s : LamSort) (t : LamTerm) : LamTerm :=
  .lam s (.app s t.bvarLift (.bvar 0))

def LamWF.etaExpand1 (wft : LamWF ltv ⟨lctx, t, .func argTy resTy⟩) :
  LamWF ltv ⟨lctx, t.etaExpand1 argTy, .func argTy resTy⟩ :=
  LamWF.ofLam _ (.ofApp _ wft.ofBVarLift .pushLCtx_ofBVar)

theorem LamEquiv.etaExpand1
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .func argTy resTy⟩) :
  LamEquiv lval lctx (.func argTy resTy) t (t.etaExpand1 argTy) :=
  ⟨wft, LamWF.etaExpand1 wft, fun _ => funext (fun _ => Eq.symm (LamWF.interp_app_bvarLift_bvar0 _))⟩

-- This is meant to eta-expand a term `t` which has type `argTys₀ → ⋯ → argTysᵢ₋₁ → resTy`
def LamTerm.etaExpandAux (argTys : List LamSort) (t : LamTerm) : LamTerm :=
  LamTerm.bvarAppsRev (t.bvarLifts argTys.length) argTys

theorem LamTerm.maxEVarSucc_etaExpandAux :
  (LamTerm.etaExpandAux argTys t).maxEVarSucc = t.maxEVarSucc := by
  dsimp [etaExpandAux]; rw [maxEVarSucc_bvarAppsRev, maxEVarSucc_bvarLifts]

theorem LamTerm.etaExpandAux_nil : etaExpandAux .nil t = t := by
  dsimp [etaExpandAux, bvarAppsRev]; rw [bvarLifts_zero]

theorem LamTerm.etaExpandAux_cons :
  etaExpandAux (.cons argTy argTys) t =
  etaExpandAux argTys (.app argTy t.bvarLift (.bvar 0)) := by
  dsimp [etaExpandAux, bvarAppsRev]
  dsimp [bvarLifts]; rw [bvarLiftsIdx_app, bvarLiftsIdx_succ_l]
  rw [bvarLiftsIdx_bvar, mapAt_zero, Nat.zero_add]

theorem LamTerm.etaExpandAux_append :
  etaExpandAux (argTys₁ ++ argTys₂) t = etaExpandAux argTys₂ (etaExpandAux argTys₁ t) := by
  induction argTys₁ generalizing t
  case nil => rw [etaExpandAux_nil]; rfl
  case cons argTy argTys₁ IH =>
    rw [List.cons_append, etaExpandAux_cons, etaExpandAux_cons, IH]

theorem LamTerm.etaExpandAux_append_singleton :
  etaExpandAux (argTys₁ ++ [argTy]) t = .app argTy (etaExpandAux argTys₁ t).bvarLift (.bvar 0) := by
  rw [etaExpandAux_append]; rfl

def LamWF.etaExpandAux
  (wft : LamWF ltv ⟨lctx, t, .mkFuncs resTy argTys⟩) :
  LamWF ltv ⟨pushLCtxs argTys.reverse lctx, t.etaExpandAux argTys, resTy⟩ :=
  LamWF.bvarAppsRev (by rw [← List.length_reverse]; exact LamWF.ofBVarLifts rfl _ wft)

def LamTerm.etaExpandWith (l : List LamSort) (t : LamTerm) :=
  LamTerm.mkLamFN (t.etaExpandAux l) l.reverse

theorem LamTerm.maxEVarSucc_etaExpandWith {t : LamTerm} :
  (t.etaExpandWith l).maxEVarSucc = t.maxEVarSucc := by
  dsimp [etaExpandWith]; rw [maxEVarSucc_mkLamFN, maxEVarSucc_etaExpandAux]

def LamWF.etaExpandWith (wft : LamWF ltv ⟨lctx, t, .mkFuncs s l⟩) :
  LamWF ltv ⟨lctx, t.etaExpandWith l, .mkFuncs s l⟩ := by
  rw [LamSort.mkFuncs_eq]; apply LamWF.mkLamFN;
  apply LamWF.etaExpandAux; exact wft

theorem LamEquiv.etaExpandWithAux
  {lval : LamValuation.{u}} {l : List LamSort}
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .mkFuncs s l.reverse⟩) :
  LamEquiv lval lctx (.mkFuncs s l.reverse) t (t.etaExpandWith l.reverse) := by
  dsimp [LamTerm.etaExpandWith]
  induction l generalizing lctx s t
  case nil =>
    exists wft, LamWF.etaExpandWith wft; intro lctxTerm
    apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
    dsimp [LamSort.getArgTys]; rw [LamTerm.etaExpandAux_nil]; rfl
  case cons ls l IH =>
    revert wft; rw [List.reverse_cons, LamSort.mkFuncs_append_singleton]; intro wft
    rw [List.reverse_append, List.reverse_cons, List.reverse_nil]
    rw [List.nil_append, List.singleton_append, LamTerm.etaExpandAux_append_singleton]
    apply LamEquiv.trans' (IH wft); dsimp [LamTerm.mkLamFN]
    apply LamEquiv.congr_mkLamFN.mp (LamEquiv.etaExpand1 (resTy:=s) _)
    apply LamWF.etaExpandAux wft

theorem LamEquiv.etaExpandWith
  {lval : LamValuation.{u}} {l : List LamSort}
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .mkFuncs s l⟩) :
  LamEquiv lval lctx (.mkFuncs s l) t (t.etaExpandWith l) := by
  have lrr : l = l.reverse.reverse := by rw [List.reverse_reverse]
  revert wft; rw [lrr]; apply LamEquiv.etaExpandWithAux

def LamTerm.etaExpand (s : LamSort) (t : LamTerm) := etaExpandWith s.getArgTys t

theorem LamTerm.maxEVarSucc_etaExpand {t : LamTerm} :
  (t.etaExpand s).maxEVarSucc = t.maxEVarSucc := maxEVarSucc_etaExpandWith

def LamWF.etaExpand (wft : LamWF ltv ⟨lctx, t, s⟩) :
  LamWF ltv ⟨lctx, t.etaExpand s, s⟩ := by
  rw [← LamSort.getArgTys_getResTy_eq (s:=s)] at wft
  have wft' := LamWF.etaExpandWith wft
  rw [LamSort.getArgTys_getResTy_eq] at wft'; exact wft'

theorem LamEquiv.etaExpand
  {lval : LamValuation.{u}} (wft : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t (t.etaExpand s) := by
  have wft' : LamWF lval.toLamTyVal ⟨lctx, t, .mkFuncs s.getResTy s.getArgTys⟩ := by
    rw [LamSort.getArgTys_getResTy_eq]; exact wft
  apply Eq.mp _ (LamEquiv.etaExpandWith wft'); rw [LamSort.getArgTys_getResTy_eq]; rfl

def LamWF.funext
  (wf : LamWF ltv ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, s⟩) :
  LamWF ltv ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), .base .prop⟩ :=
  let wflAp := LamWF.ofApp _ wf.getFn.getArg.ofBVarLift .pushLCtx_ofBVar
  let wfrAp := LamWF.ofApp _ wf.getArg.ofBVarLift .pushLCtx_ofBVar
  LamWF.mkEq wflAp wfrAp

def LamWF.ofFunext
  (wf : LamWF ltv ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), s⟩) :
  LamWF ltv ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, .base .prop⟩ :=
  let wfl := wf.getFn.getArg.getFn.fromBVarLift
  let wfr := wf.getArg.getFn.fromBVarLift
  LamWF.mkEq wfl wfr

theorem LamWF.interp_funext
  {wf₁ : LamWF lval.toLamTyVal ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, .base .prop⟩}
  {wf₂ : LamWF lval.toLamTyVal ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm wf₁) = (∀ (x : argTy.interp lval.tyVal),
    GLift.down (LamWF.interp lval (pushLCtx argTy lctx) (pushLCtxDep x lctxTerm) wf₂)) :=
  match wf₁ with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) HLhs) HRhs =>
    match wf₂ with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ HLhs' (.ofBVar _))) (.ofApp _ HRhs' (.ofBVar _)) => by
      dsimp [interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      rcases LamWF.unique HLhs' HLhs.ofBVarLift with ⟨⟨⟩, ⟨⟩⟩
      rcases LamWF.unique HRhs' HRhs.ofBVarLift with ⟨⟨⟩, ⟨⟩⟩
      apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h x; rw [← LamWF.interp_ofBVarLift, ← LamWF.interp_ofBVarLift, h]
      case mpr =>
        intro h; apply _root_.funext; intro x; have h' := h x
        rw [← LamWF.interp_ofBVarLift, ← LamWF.interp_ofBVarLift] at h'; exact h'

theorem LamEquiv.eqFunext {lval : LamValuation}
  (wfEq : LamWF lval.toLamTyVal ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, s⟩) :
  LamEquiv lval lctx s
    (.mkEq (.func argTy resTy) fn₁ fn₂)
    (.mkForallEF argTy (.mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)))) := by
  match wfEq with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wfFn₁) wfFn₂ =>
    let wfAp₁ := LamWF.ofApp _
      (LamWF.ofBVarLift (s:=argTy) _ wfFn₁) LamWF.pushLCtx_ofBVar
    let wfAp₂ := LamWF.ofApp _
      (LamWF.ofBVarLift (s:=argTy) _ wfFn₂) LamWF.pushLCtx_ofBVar
    exists LamWF.mkEq wfFn₁ wfFn₂, LamWF.mkForallEF (LamWF.mkEq wfAp₁ wfAp₂); intro lctxTerm
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn, forallLiftFn]
    apply _root_.congrArg; apply propext (Iff.intro ?mp ?mpr)
    case mp =>
      intro hinterp h; rw [← LamWF.interp_ofBVarLift, ← LamWF.interp_ofBVarLift, hinterp]
    case mpr =>
      intro hinterp; apply funext; intro x; apply Eq.trans ?left (Eq.trans (hinterp x) ?right)
      case left => rw [← LamWF.interp_ofBVarLift]
      case right => rw [← LamWF.interp_ofBVarLift]

theorem LamEquiv.funext {lval : LamValuation}
  (eAp : LamEquiv lval (pushLCtx argTy lctx) resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0))) :
  LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂ := by
  have ⟨wfFnAp₁, wfFnAp₂, hFnAp⟩ := eAp
  apply LamEquiv.ofLamValid (s:=.func argTy resTy) _
  have hEqValid := LamValid.ofLamEquiv eAp
  apply LamValid.mpLamEquiv (s:=.base .prop) (LamValid.revert1F hEqValid)
  apply LamEquiv.symm; apply LamEquiv.eqFunext
  apply LamWF.mkEq wfFnAp₁.getFn.fromBVarLift wfFnAp₂.getFn.fromBVarLift

def LamTerm.extensionalizeEqFWith (argTys : List LamSort) (resTy : LamSort) (lhs rhs : LamTerm) :=
  let extFn := fun x => etaExpandAux argTys x
  LamTerm.mkForallEFN (LamTerm.mkEq resTy (extFn lhs) (extFn rhs)) argTys.reverse

theorem LamTerm.maxEVarSucc_extensionalizeEqFWith :
  (extensionalizeEqFWith argTys resTy lhs rhs).maxEVarSucc = max lhs.maxEVarSucc rhs.maxEVarSucc := by
  dsimp [extensionalizeEqFWith]; rw [maxEVarSucc_mkForallEFN, maxEVarSucc_mkEq]
  rw [maxEVarSucc_etaExpandAux, maxEVarSucc_etaExpandAux]

def LamWF.extensionalizeEqFWith
  (wfl : LamWF ltv ⟨lctx, lhs, .mkFuncs s l⟩) (wfr : LamWF ltv ⟨lctx, rhs, .mkFuncs s l⟩) :
  LamWF ltv ⟨lctx, LamTerm.extensionalizeEqFWith l s lhs rhs, .base .prop⟩ :=
  LamWF.mkForallEFN (.mkEq (.etaExpandAux wfl) (.etaExpandAux wfr))

theorem LamEquiv.ofExtensionalizeEqFWithAux
  {lval : LamValuation.{u}} {l : List LamSort}
  (wfl : LamWF lval.toLamTyVal ⟨lctx, lhs, .mkFuncs s l.reverse⟩)
  (wfr : LamWF lval.toLamTyVal ⟨lctx, rhs, .mkFuncs s l.reverse⟩) :
  LamEquiv lval lctx (.base .prop) (.mkEq (.mkFuncs s l.reverse) lhs rhs) (.extensionalizeEqFWith l.reverse s lhs rhs) := by
  dsimp [LamTerm.extensionalizeEqFWith]
  induction l generalizing lctx s lhs rhs
  case nil =>
    exists LamWF.mkEq wfl wfr, LamWF.extensionalizeEqFWith wfl wfr; intro lctxTerm
    apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
    dsimp [LamSort.mkFuncs, LamTerm.extensionalizeEqFWith]
    rw [LamTerm.etaExpandAux_nil, LamTerm.etaExpandAux_nil]; rfl
  case cons ls l IH =>
    revert wfl wfr; rw [List.reverse_cons, LamSort.mkFuncs_append_singleton]; intro wfl wfr
    rw [List.reverse_append, List.reverse_cons, List.reverse_nil]
    rw [List.nil_append, List.singleton_append]
    rw [LamTerm.etaExpandAux_append_singleton, LamTerm.etaExpandAux_append_singleton]
    apply LamEquiv.trans (IH wfl wfr); dsimp [LamTerm.mkForallEFN]
    apply LamEquiv.congr_mkForallEFN; apply LamEquiv.eqFunext
    apply LamWF.mkEq (.etaExpandAux wfl) (.etaExpandAux wfr)

theorem LamEquiv.ofExtensionalizeEqFWith
  {lval : LamValuation.{u}} {l : List LamSort}
  (wfl : LamWF lval.toLamTyVal ⟨lctx, lhs, .mkFuncs s l⟩)
  (wfr : LamWF lval.toLamTyVal ⟨lctx, rhs, .mkFuncs s l⟩) :
  LamEquiv lval lctx (.base .prop) (.mkEq (.mkFuncs s l) lhs rhs) (.extensionalizeEqFWith l s lhs rhs) := by
  have lrr : l = l.reverse.reverse := by rw [List.reverse_reverse]
  revert wfl wfr; rw [lrr]; apply LamEquiv.ofExtensionalizeEqFWithAux

def LamTerm.extensionalizeEqF (s : LamSort) (lhs rhs : LamTerm) :=
  extensionalizeEqFWith s.getArgTys s.getResTy lhs rhs

theorem LamTerm.maxEVarSucc_extensionalizeEqF :
  (extensionalizeEqF s lhs rhs).maxEVarSucc = max lhs.maxEVarSucc rhs.maxEVarSucc :=
  maxEVarSucc_extensionalizeEqFWith

def LamWF.extensionalizeEqF
  (wfl : LamWF ltv ⟨lctx, lhs, s⟩)
  (wfr : LamWF ltv ⟨lctx, rhs, s⟩) :
  LamWF ltv ⟨lctx, .extensionalizeEqF s lhs rhs, .base .prop⟩ := by
  rw [← LamSort.getArgTys_getResTy_eq (s:=s)] at wfl wfr
  exact LamWF.extensionalizeEqFWith wfl wfr

theorem LamEquiv.ofExtensionalizeEqF
  {lval : LamValuation.{u}} (wf : LamWF lval.toLamTyVal ⟨lctx, .mkEq s lhs rhs, s'⟩) :
  LamEquiv lval lctx (.base .prop) (.mkEq s lhs rhs) (LamTerm.extensionalizeEqF s lhs rhs) :=
  match wf with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wfl) wfr => by
    clear wf; revert wfl wfr
    rw [← LamSort.getArgTys_getResTy_eq (s:=s)]
    intro wfl wfr; apply Eq.mp _ (LamEquiv.ofExtensionalizeEqFWith wfl wfr)
    rw [LamSort.getArgTys_getResTy_eq]; rfl

def LamTerm.extensionalizeEq (t : LamTerm) : LamTerm :=
  match t with
  | .base (.eq s) => .lam s (.lam s (.extensionalizeEqF s (.bvar 1) (.bvar 0)))
  | .app _ (.base (.eq s)) lhs => .lam s (.extensionalizeEqF s lhs.bvarLift (.bvar 0))
  | .app _ (.app _ (.base (.eq s)) lhs) rhs => .extensionalizeEqF s lhs rhs
  | _ => t

theorem LamTerm.maxEVarSucc_extensionalizeEq :
  (extensionalizeEq t).maxEVarSucc = t.maxEVarSucc := by
  cases t <;> try rfl
  case base b =>
    cases b <;> try rfl
    case eq s =>
      dsimp [maxEVarSucc]; rw [maxEVarSucc_extensionalizeEqF]; rfl
  case app s fn arg =>
    cases fn <;> try rfl
    case base b =>
      cases b <;> try rfl
      case eq s =>
        dsimp [maxEVarSucc]; rw [maxEVarSucc_extensionalizeEqF]
        rw [maxEVarSucc_bvarLift]; apply Nat.max_comm
    case app _ fn' arg' =>
      cases fn' <;> try rfl
      case base b =>
        cases b <;> try rfl
        case eq s =>
          dsimp [extensionalizeEq, maxEVarSucc]
          rw [maxEVarSucc_extensionalizeEqF]
          rw [Nat.max, Nat.max, Nat.max_zero_left]

def LamWF.extensionalizeEq (wf : LamWF ltv ⟨lctx, t, s⟩) :
  LamWF ltv ⟨lctx, t.extensionalizeEq, s⟩ := by
  cases t <;> try exact wf
  case base b =>
    cases b <;> try exact wf
    case eq s' =>
      dsimp [LamTerm.extensionalizeEq]; cases wf.getBase
      apply LamWF.ofLam; apply LamWF.ofLam
      apply LamWF.extensionalizeEqF; apply LamWF.ofBVar 1; apply LamWF.ofBVar 0
  case app s' fn arg =>
    cases fn <;> try exact wf
    case base b =>
      cases b <;> try exact wf
      case eq _ =>
        dsimp [LamTerm.extensionalizeEq]; cases wf.getFn.getBase
        apply LamWF.ofLam; apply LamWF.extensionalizeEqF
        apply LamWF.ofBVarLift; apply wf.getArg; apply LamWF.ofBVar 0
    case app _ fn' arg' =>
      cases fn' <;> try exact wf
      case base b =>
        cases b <;> try exact wf
        case eq _ =>
          cases wf.getFn.getFn.getBase
          apply LamWF.extensionalizeEqF wf.getFn.getArg wf.getArg

theorem LamEquiv.ofExtensionalizeEq
  {lval : LamValuation.{u}} (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t t.extensionalizeEq := by
  cases t <;> try apply LamEquiv.refl wf
  case base b =>
    cases b <;> try apply LamEquiv.refl wf
    case eq s' =>
      cases wf.getBase
      apply LamEquiv.trans (LamEquiv.etaExpandWith (l:=[s', s']) wf)
      apply LamEquiv.ofLam; apply LamEquiv.ofLam
      apply LamEquiv.ofExtensionalizeEqF (LamWF.mkEq (.ofBVar 1) (.ofBVar 0))
  case app s' fn arg =>
    cases fn <;> try apply LamEquiv.refl wf
    case base b =>
      cases b <;> try apply LamEquiv.refl wf
      case eq _ =>
        cases wf.getFn.getBase
        apply LamEquiv.trans (LamEquiv.etaExpandWith (l:=[s']) wf)
        apply LamEquiv.ofLam;
        apply LamEquiv.ofExtensionalizeEqF (.ofApp _ wf.ofBVarLift (.ofBVar 0))
    case app _ fn' arg' =>
      cases fn' <;> try apply LamEquiv.refl wf
      case base b =>
        cases b <;> try apply LamEquiv.refl wf
        case eq _ =>
          cases wf.getFn.getFn.getBase; apply LamEquiv.ofExtensionalizeEqF wf

theorem LamThmEquiv.ofExtensionalizeEq (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t.extensionalizeEq :=
  fun lctx' => LamEquiv.ofExtensionalizeEq (wf lctx')

def LamTerm.extensionalizeAux (isAppFn : Bool) (t : LamTerm) : LamTerm :=
  let cont (r : LamTerm) : LamTerm :=
    match isAppFn with
    | true => r
    | false => r.extensionalizeEq
  match t with
  | .atom n => .atom n
  | .etom n => .etom n
  | .base _ => cont t
  | .bvar n => .bvar n
  | .lam s body => .lam s (body.extensionalizeAux false)
  | .app s fn arg => cont (.app s (fn.extensionalizeAux true) (arg.extensionalizeAux false))

theorem LamTerm.maxEVarSucc_extensionalizeAux :
  (extensionalizeAux isAppFn t).maxEVarSucc = t.maxEVarSucc := by
  induction t generalizing isAppFn <;> (try rfl) <;> dsimp [extensionalizeAux]
  case base b =>
    match isAppFn with
    | true => rfl
    | false => dsimp; rw [maxEVarSucc_extensionalizeEq]
  case lam s body IH =>
    dsimp [maxEVarSucc]; rw [IH]
  case app s fn arg IHFn IHArg =>
    match isAppFn with
    | true => 
      dsimp [maxEVarSucc]; rw [IHFn, IHArg]
    | false =>
      dsimp; rw [maxEVarSucc_extensionalizeEq]
      dsimp [maxEVarSucc]; rw [IHFn, IHArg]

abbrev LamTerm.extensionalize := LamTerm.extensionalizeAux false

def LamWF.extensionalizeAux :
  (wft : LamWF ltv ⟨lctx, t, s⟩) → LamWF ltv ⟨lctx, t.extensionalizeAux isAppFn, s⟩
| .ofAtom n => .ofAtom n
| .ofEtom n => .ofEtom n
| .ofBase b => by
  dsimp [LamTerm.extensionalizeAux]
  match isAppFn with
  | true => exact .ofBase b
  | false => exact .extensionalizeEq (.ofBase b)
| .ofBVar n => .ofBVar n
| .ofLam _ wfBody => .ofLam _ wfBody.extensionalizeAux
| .ofApp _ wfFn wfArg => by
  dsimp [LamTerm.extensionalizeAux]
  have wfAp := LamWF.ofApp _
    (wfFn.extensionalizeAux (isAppFn:=true))
    (wfArg.extensionalizeAux (isAppFn:=false))
  match isAppFn with
  | true => exact wfAp
  | false => exact wfAp.extensionalizeEq

theorem LamEquiv.ofExtensionalize
  {lval : LamValuation.{u}} (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t (t.extensionalizeAux isAppFn) := by
  induction t generalizing s lctx isAppFn <;> try apply LamEquiv.refl wf
  case base b => cases wf; case ofBase H =>
    dsimp [LamTerm.extensionalizeAux]
    match isAppFn with
    | true => apply LamEquiv.refl (.ofBase H)
    | false => apply LamEquiv.ofExtensionalizeEq (.ofBase H)
  case lam s body IH => cases wf; case ofLam _ wfBody =>
    dsimp [LamTerm.extensionalizeAux]; apply LamEquiv.ofLam; apply IH wfBody
  case app s' fn arg IHFn IHArg => cases wf; case ofApp HArg HFn =>
    dsimp [LamTerm.extensionalizeAux];
    match isAppFn with
    | true =>
      dsimp; apply LamEquiv.congr; apply IHFn HFn; apply IHArg HArg
    | false =>
      dsimp; apply LamEquiv.trans _ (LamEquiv.ofExtensionalizeEq
        (.ofApp _ HFn.extensionalizeAux HArg.extensionalizeAux))
      apply LamEquiv.congr; apply IHFn HFn; apply IHArg HArg

theorem LamThmEquiv.ofExtensionalize
  (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t (t.extensionalizeAux isAppFn) :=
  fun lctx' => LamEquiv.ofExtensionalize (wf lctx')

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we reduce the top-level redex
-- Suppose `lctx ⊢ body : ty`. It's easy to see that the `lctx` which `arg`
--   resides in is `fun n => lctx (n + idx + 1)` and the type of `arg` is `lctx idx`
def LamTerm.instantiateAt (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n        => .atom n
| .etom n        => .etom n
| .base b        => .base b
| .bvar n        => pushLCtxAt (arg.bvarLifts idx) idx LamTerm.bvar n
| .lam s body    => .lam s (LamTerm.instantiateAt (.succ idx) arg body)
| .app s fn arg' => .app s (LamTerm.instantiateAt idx arg fn) (LamTerm.instantiateAt idx arg arg')

theorem LamTerm.maxEVarSucc_instantiateAt :
  (LamTerm.instantiateAt idx arg body).maxEVarSucc ≤ Nat.max arg.maxEVarSucc body.maxEVarSucc := by
  induction body generalizing idx <;> try apply Nat.le_max_right
  case bvar n =>
    dsimp [instantiateAt, pushLCtxAt, restoreAt]
    match Nat.ble idx n with
    | true =>
      dsimp [pushLCtx]
      match n - idx with
      | 0 =>
        apply Nat.le_trans _ (Nat.le_max_left _ _)
        dsimp [bvarLifts, bvarLiftsIdx]
        rw [LamTerm.maxEVarSucc_mapBVarAt]; apply Nat.le_refl
      | _ + 1 => apply Nat.le_max_right
    | false => apply Nat.le_max_right
  case lam s body IH =>
    dsimp [instantiateAt, maxEVarSucc]; apply IH
  case app s fn arg' IHFn IHArg' =>
    dsimp [instantiateAt, maxEVarSucc]
    rw [Nat.max_le]; apply And.intro
    case left =>
      apply Nat.le_trans IHFn
      rw [Nat.max_le]; apply And.intro
      case left => apply Nat.le_max_left
      case right =>
        apply Nat.le_trans _ (Nat.le_max_right _ _)
        apply Nat.le_max_left
    case right =>
      apply Nat.le_trans IHArg'
      rw [Nat.max_le]; apply And.intro
      case left => apply Nat.le_max_left
      case right =>
        apply Nat.le_trans _ (Nat.le_max_right _ _)
        apply Nat.le_max_right

def LamWF.instantiateAt
  (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, arg.bvarLifts idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAt argTy idx lctx, body, bodyTy⟩) →
  LamWF ltv ⟨lctx, LamTerm.instantiateAt idx arg body, bodyTy⟩
| lctx, _,     .ofAtom n => .ofAtom _
| lctx, _,     .ofEtom n => .ofEtom _
| lctx, _,     .ofBase (b:=b) H => .ofBase H
| lctx, wfArg, .ofBVar n => by
  dsimp [LamTerm.instantiateAt, pushLCtxAt, restoreAt, pushLCtx]
  match Nat.ble idx n with
  | true =>
    dsimp;
    match (n - idx) with
    | 0 => exact wfArg
    | _ + 1 => exact .ofBVar _
  | false => exact .ofBVar n
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLiftIdx (s:=argTy') (lctx:=lctx) 0 _ wfArg
  let IHArg := LamWF.instantiateAt ltv (Nat.succ idx) _
    (by
      dsimp [LamTerm.bvarLifts] at wfArg'
      rw [pushLCtxAt_zero, ← LamTerm.bvarLiftsIdx_succ_r] at wfArg'
      exact wfArg')
    (by
      rw [pushLCtx_pushLCtxAt] at H
      exact H)
  .ofLam _ IHArg
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.instantiateAt ltv idx _ wfArg HFn
  let IHArg := LamWF.instantiateAt ltv idx _ wfArg HArg
  .ofApp argTy' IHFn IHArg

theorem LamWF.interp_instantiateAt.{u}
  (lval : LamValuation.{u}) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort} :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts idx arg, argTy⟩) →
  (wfBody : LamWF lval.toLamTyVal ⟨pushLCtxAt argTy idx lctxTy, body, bodyTy⟩) →
  let wfInstantiateAt' := LamWF.instantiateAt lval.toLamTyVal idx lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtxAt argTy idx lctxTy)
    (pushLCtxAtDep (LamWF.interp lval lctxTy lctxTerm wfArg) idx lctxTerm) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfInstantiateAt')
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofEtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBase b => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n => by
  dsimp [LamWF.interp, LamWF.instantiateAt, LamTerm.instantiateAt]
  dsimp [pushLCtxAt, pushLCtxAtDep, restoreAt, restoreAtDep, pushLCtx]
  match Nat.ble idx n with
  | true =>
    dsimp;
    match (n - idx) with
    | 0 => rfl
    | _ + 1 => rfl
  | false => rfl
| lctxTy, lctxTerm, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  _root_.funext (fun x => by
    have wfArg' := LamWF.ofBVarLift (s:=argTy') (lctx:=lctxTy) _ wfArg
    rw [← LamTerm.bvarLifts_succ_r] at wfArg'
    rw [pushLCtx_pushLCtxAt] at H
    have IH := LamWF.interp_instantiateAt lval (.succ idx)
      (pushLCtx argTy' lctxTy) (pushLCtxDep x lctxTerm) wfArg' H
    apply Eq.trans ?eqLarge (Eq.trans IH ?eqSmall)
    case eqLarge =>
      dsimp [interp]; apply interp_substLCtxTerm
      case HLCtxTyEq => apply pushLCtx_pushLCtxAt
      case HLCtxTermEq =>
        apply HEq.trans (pushLCtxDep_pushLCtxAtDep _ _ _ _)
        apply pushLCtxAtDep_substx <;> try rfl
        rw [LamWF.interp_ofBVarLift lval _ lctxTerm x _ wfArg]
        apply interp_heq <;> try rfl
        rw [LamTerm.bvarLifts_succ_r]
    case eqSmall =>
      dsimp [interp]; apply interp_substLCtxTerm <;> rfl)
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.interp_instantiateAt lval idx lctxTy lctxTerm wfArg HFn
  let IHArg := LamWF.interp_instantiateAt lval idx lctxTy lctxTerm wfArg HArg
  by dsimp [LamWF.interp]; dsimp at IHFn; dsimp at IHArg; simp [IHFn, IHArg]

def LamTerm.instantiate1 := LamTerm.instantiateAt 0

theorem LamTerm.maxEVarSucc_instantiate1 :
  (LamTerm.instantiate1 arg body).maxEVarSucc ≤ Nat.max arg.maxEVarSucc body.maxEVarSucc :=
  LamTerm.maxEVarSucc_instantiateAt

def LamWF.instantiate1
  (ltv : LamTyVal) {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, arg, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtx argTy lctx, body, bodyTy⟩) →
  LamWF ltv ⟨lctx, LamTerm.instantiate1 arg body, bodyTy⟩ :=
  Eq.mp (by
    dsimp [LamTerm.bvarLifts]
    rw [pushLCtxAt_zero, LamTerm.bvarLiftsIdx_zero]
    rfl) (@LamWF.instantiateAt ltv 0 arg argTy body bodyTy)

def LamThmWF.instantiate1
  (wfArg : LamThmWF lval lctx argTy arg) (wfBody : LamThmWF lval (argTy :: lctx) bodyTy body) :
  LamThmWF lval lctx bodyTy (LamTerm.instantiate1 arg body) := by
  intro lctx'; have hArg := wfArg lctx'; have hBody := wfBody lctx'
  rw [pushLCtxs_cons] at hBody; apply LamWF.instantiate1 _ _ hArg hBody

theorem LamWF.interp_instantiate1.{u}
  (lval : LamValuation.{u}) {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, arg, argTy⟩)
  (wfBody : LamWF lval.toLamTyVal ⟨pushLCtx argTy lctxTy, body, bodyTy⟩) :
  let wfInstantiate1' := LamWF.instantiate1 lval.toLamTyVal lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtx argTy lctxTy)
    (pushLCtxDep (LamWF.interp lval lctxTy lctxTerm wfArg) lctxTerm) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfInstantiate1') := by
  apply Eq.trans ?eqLarge (Eq.trans (@LamWF.interp_instantiateAt lval 0
    arg argTy body bodyTy lctxTy lctxTerm (Eq.mp ?eqArg wfArg) (Eq.mp ?eqBody wfBody)) ?eqSmall)
  case eqArg => dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx_zero]
  case eqBody => rw [pushLCtxAt_zero]
  case eqLarge =>
    apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
    case h.HLCtxTyEq => rw [pushLCtxAt_zero]
    case h.HLCtxTermEq =>
      apply HEq.trans (HEq.symm (pushLCtxAtDep_zero _ _)) _
      apply pushLCtxAtDep_heq <;> try rfl
      apply LamWF.interp_heq <;> try rfl
      dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx_zero]
  case eqSmall =>
    apply eq_of_heq; apply LamWF.interp_heq <;> rfl

theorem LamThmValid.instantiate1
  (hw : LamThmWF lval lctx argTy arg) (hv : LamThmValid lval (argTy :: lctx) body) :
  LamThmValid lval lctx (LamTerm.instantiate1 arg body) := by
  intro lctx'; have hArg := hw lctx'; have hBody := hv lctx'
  rw [pushLCtxs_cons] at hBody; have ⟨wfBody, vBody⟩ := hBody
  exists (LamWF.instantiate1 _ _ hArg wfBody); intro lctxTerm;
  rw [← LamWF.interp_instantiate1]; apply vBody

def LamBaseTerm.resolveImport (ltv : LamTyVal) : LamBaseTerm → LamBaseTerm
| .eqI n      => .eq (ltv.lamILTy n)
| .forallEI n => .forallE (ltv.lamILTy n)
| .existEI n  => .existE (ltv.lamILTy n)
| t           => t

def LamBaseTerm.LamWF.resolveImport {ltv : LamTyVal} {b : LamBaseTerm} {ty : LamSort}
  (wfB : LamBaseTerm.LamWF ltv b ty) : LamBaseTerm.LamWF ltv (b.resolveImport ltv) ty := by
  cases wfB <;> constructor

theorem LamBaseTerm.LamWF.interp_resolveImport
  (lval : LamValuation.{u}) {b : LamBaseTerm} {ty : LamSort}
  (wfB : LamBaseTerm.LamWF lval.toLamTyVal b ty) :
  let wfRB := LamBaseTerm.LamWF.resolveImport wfB
  LamBaseTerm.LamWF.interp lval wfB = LamBaseTerm.LamWF.interp lval wfRB := by
  cases wfB <;> first | rfl | dsimp [resolveImport, LamBaseTerm.resolveImport, interp]
  case ofEqI n =>
    generalize LamValuation.ilVal lval n = ilVal
    cases ilVal
    case mk eqL _ _ =>
      apply funext; intros a; apply funext; intros b;
      apply GLift.down.inj; apply propext;
      apply Iff.intro (eqL.down _ _) (eqL.up _ _)
  case ofForallEI n =>
    generalize LamValuation.ilVal lval n = ilVal
    cases ilVal
    case mk _ forallL _ =>
      apply funext; intros p;
      apply GLift.down.inj; apply propext;
      apply Iff.intro (forallL.down _) (forallL.up _)
  case ofExistEI n =>
    generalize LamValuation.ilVal lval n = ilVal
    cases ilVal
    case mk _ _ existL =>
      apply funext; intros p;
      apply GLift.down.inj; apply propext;
      apply Iff.intro (existL.down _) (existL.up _)

def LamTerm.resolveImport (ltv : LamTyVal) : LamTerm → LamTerm
| .atom n       => .atom n
| .etom n       => .etom n
| .base b       => .base (b.resolveImport ltv)
| .bvar n       => .bvar n
| .lam s t      => .lam s (t.resolveImport ltv)
| .app s fn arg => .app s (fn.resolveImport ltv) (arg.resolveImport ltv)

theorem LamTerm.maxEVarSucc_resolveImport {t : LamTerm} :
  (t.resolveImport ltv).maxEVarSucc = t.maxEVarSucc :=
  match t with
  | .atom n => rfl
  | .etom n => rfl
  | .base b => rfl
  | .bvar n => rfl
  | .lam _ t => LamTerm.maxEVarSucc_resolveImport (t:=t)
  | .app s fn arg => by
    dsimp [resolveImport, maxEVarSucc]
    rw [maxEVarSucc_resolveImport (t:=fn), maxEVarSucc_resolveImport (t:=arg)]

def LamWF.resolveImport
  {ltv : LamTyVal} {t : LamTerm} {ty : LamSort}
  {lctx : Nat → LamSort} (wfT : LamWF ltv ⟨lctx, t, ty⟩) :
  LamWF ltv ⟨lctx, LamTerm.resolveImport ltv t, ty⟩ :=
  match wfT with
  | .ofAtom n => .ofAtom n
  | .ofEtom n => .ofEtom n
  | .ofBase b => .ofBase (LamBaseTerm.LamWF.resolveImport b)
  | .ofBVar n => .ofBVar n
  | .ofLam s hwf => .ofLam s hwf.resolveImport
  | .ofApp s fn arg => .ofApp s fn.resolveImport arg.resolveImport

def LamThmWF.resolveImport
  {lval : LamValuation} {lctx : List LamSort} {rty : LamSort} {t : LamTerm}
  (wf : LamThmWF lval lctx rty t) : LamThmWF lval lctx rty (t.resolveImport lval.toLamTyVal) :=
  fun lctx => LamWF.resolveImport (wf lctx)

theorem LamWF.interp_resolveImport
  {lval : LamValuation.{u}} {t : LamTerm} {ty : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfT : LamWF lval.toLamTyVal ⟨lctxTy, t, ty⟩) :
  let wfRB := LamWF.resolveImport wfT
  LamWF.interp lval lctxTy lctxTerm wfT = LamWF.interp lval lctxTy lctxTerm wfRB :=
  match wfT with
  | .ofAtom _ => rfl
  | .ofEtom _ => rfl
  | .ofBase b => LamBaseTerm.LamWF.interp_resolveImport lval b
  | .ofBVar n => rfl
  | .ofLam s hwf => by
    apply _root_.funext; intros x; dsimp [interp]
    rw [LamWF.interp_resolveImport _ _ hwf]
  | .ofApp s wfFn wfArg => by
    dsimp [interp];
    rw [LamWF.interp_resolveImport _ _ wfFn]
    rw [LamWF.interp_resolveImport _ _ wfArg]

theorem LamThmValid.resolveImport (H : LamThmValid lval lctx t) :
  LamThmValid lval lctx (t.resolveImport lval.toLamTyVal) := by
  intro lctx; let ⟨wf, h⟩ := H lctx;
  exists (LamWF.resolveImport wf); intro lctxTerm
  rw [← LamWF.interp_resolveImport]; apply h

def LamTerm.topBetaAux (s : LamSort) (arg : LamTerm) : (fn : LamTerm) → LamTerm
| .lam _ body => LamTerm.instantiate1 arg body
| t           => .app s t arg

def LamWF.topBetaAux (ltv : LamTyVal)
  {arg : LamTerm} {argTy : LamSort} {fn : LamTerm} {resTy : LamSort}
  (lctx : Nat → LamSort) (wfArg : LamWF ltv ⟨lctx, arg, argTy⟩) 
  (wfFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩) :
  LamWF ltv ⟨lctx, LamTerm.topBetaAux argTy arg fn, resTy⟩ :=
  match fn with
  | .atom _  => .ofApp _ wfFn wfArg
  | .etom _  => .ofApp _ wfFn wfArg
  | .base _  => .ofApp _ wfFn wfArg
  | .bvar _  => .ofApp _ wfFn wfArg
  | .lam _ body =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=argTy') (body:=body') bodyTy' wfBody =>
      LamWF.instantiate1 ltv lctx (argTy:=argTy') wfArg wfBody
  | .app _ _ _ => .ofApp _ wfFn wfArg

def LamWF.interp_topBetaAux.{u} (lval : LamValuation.{u})
  {arg : LamTerm} {argTy : LamSort} {fn : LamTerm} {resTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, arg, argTy⟩)
  (wfFn : LamWF lval.toLamTyVal ⟨lctxTy, fn, .func argTy resTy⟩) :
  let wfHB := LamWF.topBetaAux _ lctxTy wfArg wfFn
  (LamWF.interp lval lctxTy lctxTerm (.ofApp _ wfFn wfArg)
  = LamWF.interp lval lctxTy lctxTerm wfHB) :=
  match fn with
  | .atom _  => rfl
  | .etom _  => rfl
  | .base _  => rfl
  | .bvar _  => rfl
  | .lam _ _ =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=_) (body:=_) _ _ => LamWF.interp_instantiate1 _ _ _ _ _
  | .app _ _ _ => rfl

def LamTerm.topBeta : LamTerm → LamTerm
| .app s fn arg => LamTerm.topBetaAux s arg fn
| t => t

theorem LamTerm.maxEVarSucc_topBeta :
  (LamTerm.topBeta t).maxEVarSucc ≤ t.maxEVarSucc := by
  cases t <;> try apply Nat.le_refl
  case app s fn arg =>
    dsimp [topBeta]; cases fn <;> try apply Nat.le_refl
    case lam s' body =>
      dsimp [topBetaAux, maxEVarSucc]; rw [Nat.max, Nat.max_comm]
      apply LamTerm.maxEVarSucc_instantiate1

def LamWF.topBeta
  (ltv : LamTyVal) {t : LamTerm} {ty : LamSort} (lctx : Nat → LamSort)
  (wf : LamWF ltv ⟨lctx, t, ty⟩) : LamWF ltv ⟨lctx, LamTerm.topBeta t, ty⟩ :=
  match t with
  | .atom _ => wf
  | .etom _ => wf
  | .base _ => wf
  | .bvar _ => wf
  | .lam .. => wf
  | .app .. =>
    match wf with
    | .ofApp _ wfFn wfArg => LamWF.topBetaAux _ lctx wfArg wfFn

def LamThmWF.topBeta
  (wf : LamThmWF lval lctx rty t) : LamThmWF lval lctx rty t.topBeta := by
  intro lctx; apply LamWF.topBeta _ _ (wf lctx)

theorem LamWF.interp_topBeta
  {lval : LamValuation.{u}} {t : LamTerm} {ty : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfT : LamWF lval.toLamTyVal ⟨lctxTy, t, ty⟩) :
  let wfHB := LamWF.topBeta lval.toLamTyVal lctxTy wfT
  LamWF.interp lval lctxTy lctxTerm wfT = LamWF.interp lval lctxTy lctxTerm wfHB :=
  match t with
  | .atom _ => rfl
  | .etom _ => rfl
  | .base _ => rfl
  | .bvar _ => rfl
  | .lam .. => rfl
  | .app .. =>
    match wfT with
    | .ofApp _ wfFn wfArg => LamWF.interp_topBetaAux _ lctxTy lctxTerm wfArg wfFn

theorem LamThmValid.topBeta (H : LamThmValid lval lctx t) :
  LamThmValid lval lctx t.topBeta := by
  intros lctx; let ⟨wf, h⟩ := H lctx; exists (LamWF.topBeta _ _ wf);
  intro lctxTerm; rw [← LamWF.interp_topBeta]; apply h

theorem LamEquiv.ofTopBeta {lval : LamValuation}
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) : LamEquiv lval lctx s t t.topBeta :=
  ⟨wf, LamWF.topBeta _ _ wf, fun _ => LamWF.interp_topBeta _ _ _⟩

theorem LamThmEquiv.ofTopBeta (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t.topBeta :=
  fun lctx' => LamEquiv.ofTopBeta (wf lctx')

def LamTerm.beta (t : LamTerm) : List (LamSort × LamTerm) → LamTerm
| .nil => t
| arg :: args =>
  match t with
  | .lam _ t' => (LamTerm.instantiate1 arg.snd t').beta args
  | t => t.mkAppN (arg :: args)

theorem LamTerm.maxEVarSucc_beta
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  (LamTerm.beta t args).maxEVarSucc ≤ n := by
  induction hs generalizing t
  case nil => exact ht
  case cons argty argtys harg hargs IH =>
    cases t <;> try apply LamTerm.maxEVarSucc_mkAppN (.cons harg hargs) ht
    case lam s body =>
      dsimp [beta]; apply IH
      apply Nat.le_trans LamTerm.maxEVarSucc_instantiate1
      rw [Nat.max_le]; apply And.intro harg ht

def LamWF.ofBeta
  (fn : LamTerm) (args : List (LamSort × LamTerm))
  (wf : LamWF ltv ⟨lctx, fn.mkAppN args, resTy⟩) :
  LamWF ltv ⟨lctx, fn.beta args, resTy⟩ :=
  match args with
  | .nil => wf
  | arg :: args =>
    match fn with
    | .atom _ => wf
    | .etom _ => wf
    | .base _ => wf
    | .bvar _ => wf
    | .lam s' t' => by
      have wfAp := LamWF.fnWFOfMkAppN (args:=args) wf
      have wflst := (wf.fnWFOfMkAppN (args:=args)).getFn; cases wflst
      case ofLam wft => exact LamWF.ofBeta _ args (LamWF.mkAppN
        (LamWF.instantiate1 _ _ wfAp.getArg wft) (wf.argsWFOfMkAppN (args:=args)))
    | .app _ _ _ => wf

theorem LamEquiv.ofBeta
  (fn : LamTerm) (args : List (LamSort × LamTerm))
  (wf : LamWF lval.toLamTyVal ⟨lctx, fn.mkAppN args, resTy⟩) :
  LamEquiv lval lctx resTy (fn.mkAppN args) (fn.beta args) :=
  match args with
  | .nil => ⟨wf, wf, fun _ => rfl⟩
  | arg :: args =>
    match fn with
    | .atom _ => ⟨wf, wf, fun _ => rfl⟩
    | .etom _ => ⟨wf, wf, fun _ => rfl⟩
    | .base _ => ⟨wf, wf, fun _ => rfl⟩
    | .bvar _ => ⟨wf, wf, fun _ => rfl⟩
    | .lam s' t' => by
      dsimp [LamTerm.mkAppN, LamTerm.beta]
      dsimp [LamTerm.mkAppN] at wf
      let wfAp := LamWF.fnWFOfMkAppN (args:=args) wf
      have hTop := LamEquiv.ofTopBeta wfAp;
      dsimp only [LamTerm.topBeta, LamTerm.topBetaAux] at hTop
      have hCongr := LamEquiv.congrFunN wf (args:=args) hTop
      apply LamEquiv.trans hCongr
      apply LamEquiv.ofBeta _ args
      apply LamWF.mkAppN _ wf.argsWFOfMkAppN
      have wflst := wf.fnWFOfMkAppN.getFn; cases wflst
      case ofLam wft => apply LamWF.instantiate1 _ _ wfAp.getArg wft
    | .app _ _ _ => ⟨wf, wf, fun _ => rfl⟩

def LamTerm.headBetaAux : List (LamSort × LamTerm) → LamTerm → LamTerm
| args, .app s fn arg => headBetaAux ((s, arg) :: args) fn
| args, t             => beta t args

theorem LamTerm.maxEVarSucc_headBetaAux
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  (LamTerm.headBetaAux args t).maxEVarSucc ≤ n := by
  induction t generalizing args <;> try apply LamTerm.maxEVarSucc_beta hs ht
  case app s fn arg IHFn IHArg =>
    dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
    exact IHFn (.cons ht.right hs) ht.left

def LamWF.ofHeadBetaAux
  (wf : LamWF ltv ⟨lctx, LamTerm.mkAppN t args, rty⟩) :
  LamWF ltv ⟨lctx, t.headBetaAux args, rty⟩ :=
  match t with
  | .atom _ => LamWF.ofBeta _ _ wf
  | .etom _ => LamWF.ofBeta _ _ wf
  | .base _ => LamWF.ofBeta _ _ wf
  | .bvar _ => LamWF.ofBeta _ _ wf
  | .lam _ _ => LamWF.ofBeta _ _ wf
  | .app _ fn _ => ofHeadBetaAux (t:=fn) wf

theorem LamEquiv.ofHeadBetaAux
  (wf : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN t args, rty⟩) :
  LamEquiv lval lctx rty (LamTerm.mkAppN t args) (t.headBetaAux args) := by
  induction t generalizing args <;>
    try (cases args <;> apply LamEquiv.refl wf)
  case lam s body _ => apply LamEquiv.ofBeta _ _ wf
  case app s fn arg IHFn _ =>
    dsimp [LamTerm.headBetaAux]; apply IHFn (args:=(s, arg) :: args) wf

def LamTerm.headBeta := LamTerm.headBetaAux []

theorem LamTerm.maxEVarSucc_headBeta :
  (LamTerm.headBeta t).maxEVarSucc ≤ t.maxEVarSucc :=
  LamTerm.maxEVarSucc_headBetaAux .nil (Nat.le_refl _)

def LamWF.ofHeadBeta (wf : LamWF ltv ⟨lctx, t, s⟩) : LamWF ltv ⟨lctx, t.headBeta, s⟩ := by
  cases t <;> try exact wf
  apply LamWF.ofHeadBetaAux wf

theorem LamEquiv.ofHeadBeta
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t t.headBeta := by cases t <;> apply LamEquiv.ofHeadBetaAux (args:=[]) wf

theorem LamThmEquiv.ofHeadBeta (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t.headBeta :=
  fun lctx' => LamEquiv.ofHeadBeta (wf lctx')

def LamTerm.headBetaBounded (n : Nat) (t : LamTerm) :=
  match n with
  | 0 => t
  | .succ n' =>
    match t.isHeadBetaTarget with
    | true => headBetaBounded n' t.headBeta
    | false => t

theorem LamTerm.maxEVarSucc_headBetaBounded :
  (LamTerm.headBetaBounded n t).maxEVarSucc ≤ t.maxEVarSucc := by
  induction n generalizing t
  case zero => apply Nat.le_refl
  case succ n IH =>
    dsimp [headBetaBounded]
    cases (isHeadBetaTarget t) <;> try apply Nat.le_refl
    dsimp; apply Nat.le_trans IH; apply maxEVarSucc_headBeta

def LamWF.ofHeadBetaBounded
  (wf : LamWF ltv ⟨lctx, t, s⟩) : LamWF ltv ⟨lctx, t.headBetaBounded n, s⟩ :=
  match n with
  | 0 => wf
  | .succ n => by
    dsimp [LamTerm.headBetaBounded]
    match t.isHeadBetaTarget with
    | true => exact LamWF.ofHeadBetaBounded wf.ofHeadBeta
    | false => exact wf

theorem LamEquiv.ofHeadBetaBounded
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) : LamEquiv lval lctx s t (t.headBetaBounded n) := by
  induction n generalizing t
  case zero => apply LamEquiv.refl wf
  case succ n IH =>
    dsimp [LamTerm.headBetaBounded]
    match t.isHeadBetaTarget with
    | true =>
      dsimp
      apply LamEquiv.trans (LamEquiv.ofHeadBeta wf)
      apply IH (LamWF.ofHeadBeta wf)
    | false => apply LamEquiv.refl wf

theorem LamThmEquiv.ofHeadBetaBounded (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t (t.headBetaBounded n) :=
  fun lctx => LamEquiv.ofHeadBetaBounded (wf lctx)

def LamTerm.betaBounded (n : Nat) (t : LamTerm) :=
  match n with
  | 0 => t
  | .succ n' =>
    match t with
    | .atom _ => t
    | .etom _ => t
    | .base _ => t
    | .bvar _ => t
    | .lam s t => .lam s (t.betaBounded n')
    | .app .. =>
      let tb := t.headBetaBounded n'
      let fn := tb.getAppFn
      let args := tb.getAppArgs
      let argsb := args.map (fun ((s, arg) : LamSort × _) => (s, betaBounded n' arg))
      LamTerm.mkAppN fn argsb

theorem LamTerm.maxEVarSucc_betaBounded :
  (LamTerm.betaBounded n t).maxEVarSucc ≤ t.maxEVarSucc := by
  induction n generalizing t
  case zero => apply Nat.le_refl
  case succ n IH =>
    cases t <;> try apply Nat.le_refl
    case lam s t => apply IH
    case app s fn arg =>
      dsimp [betaBounded, maxEVarSucc]
      apply LamTerm.maxEVarSucc_mkAppN
      case hs =>
        apply HList.toMapTy; dsimp [Function.comp]
        apply HList.map _ LamTerm.maxEVarSucc_getAppArgs
        intro a; cases a; dsimp; intro h
        apply Nat.le_trans _ (Nat.le_trans h _)
        apply IH; apply maxEVarSucc_headBetaBounded
      case ht =>
        apply Nat.le_trans maxEVarSucc_getAppFn
        apply maxEVarSucc_headBetaBounded

def LamTerm.betaReduced (t : LamTerm) :=
  match t with
  | .app _ fn arg =>
    !(fn.isLam) && fn.betaReduced && arg.betaReduced
  | .lam _ body => body.betaReduced
  | _ => true

theorem LamEquiv.ofBetaBounded
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) : LamEquiv lval lctx s t (t.betaBounded n) := by
  induction n generalizing lctx t s
  case zero => apply LamEquiv.refl wf
  case succ n IH =>
    dsimp [LamTerm.betaBounded]; cases t <;> try apply LamEquiv.refl wf
    case lam s t =>
      dsimp
      match wf with
      | .ofLam _ wf => apply LamEquiv.ofLam; apply IH wf
    case app s fn arg =>
      dsimp;
      have ⟨_, ⟨wfhbb, _⟩⟩ := LamEquiv.ofHeadBetaBounded (n:=n) wf
      apply LamEquiv.trans (LamEquiv.ofHeadBetaBounded (n:=n) wf)
      apply LamEquiv.trans (LamEquiv.eq wfhbb (LamTerm.appFn_appArg_eq _))
      let masterArr := (LamTerm.getAppArgs (LamTerm.headBetaBounded n (.app s fn arg))).map (fun (s, arg) => (s, arg, arg.betaBounded n))
      have eq₁ : (LamTerm.getAppArgs (LamTerm.headBetaBounded n (.app s fn arg))) = masterArr.map (fun (s, arg₁, _) => (s, arg₁)) := by
        dsimp; rw [List.map_map]; rw [List.map_equiv _ id, List.map_id]
        intro x; cases x; rfl
      have eq₂ : List.map
        (fun x => (x.fst, LamTerm.betaBounded n x.snd))
        (LamTerm.getAppArgs (LamTerm.headBetaBounded n (.app s fn arg))) = masterArr.map (fun (s, _, arg₂) => (s, arg₂)) := by
        dsimp; rw [List.map_map]; apply List.map_equiv;
        intro x; cases x; rfl
      rw [eq₂, eq₁]; have ⟨fnTy, wfFn⟩ := wfhbb.getAppFn
      apply LamEquiv.congrs (fnTy:=fnTy)
      case wfApp => rw [← eq₁, ← LamTerm.appFn_appArg_eq]; exact wfhbb
      case hFn => apply LamEquiv.refl wfFn
      case hArgs =>
        dsimp;
        apply HList.toMapTy; dsimp [Function.comp]
        apply HList.map
          (β:=fun (s, t) => LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
          (fun (s, t) => @IH lctx t s)
        apply LamWF.getAppArgs wfhbb

theorem LamThmEquiv.ofBetaBounded (wf : LamThmWF lval lctx rty t) :
  LamThmEquiv lval lctx rty t (t.betaBounded n) := fun lctx => LamEquiv.ofBetaBounded (wf lctx)

opaque LamTerm.betaReduceHackyAux (t : LamTerm) : LamTerm × Nat := Id.run <| do
  let mut n := 1
  while true do
    let cur := t.betaBounded n
    if (t.betaBounded n).betaReduced then
      return (cur, n)
    n := n * 2
  return (t, n)

def LamTerm.betaReduceHacky (t : LamTerm) := (betaReduceHackyAux t).fst

def LamTerm.betaReduceHackyIdx (t : LamTerm) := (betaReduceHackyAux t).snd

-- #eval LamTerm.betaBounded 7 (.app (.atom 0)
--   (.lam (.atom 0) (.app (.atom 0) (.bvar 0) (.bvar 0)))
--   (.lam (.atom 0) (.app (.atom 0) (.bvar 0) (.app (.atom 0) (.bvar 0) (.bvar 0)))))

theorem LamThmEquiv.ofResolveImport
  {lval : LamValuation} (wfT : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t (t.resolveImport lval.toLamTyVal) := by
  dsimp [LamThmEquiv]; intros lctx';
  let wfT' := wfT lctx'; exists wfT'; exists (LamWF.resolveImport wfT')
  intros lctxTerm; apply LamWF.interp_resolveImport

theorem LamValid.eq_refl {lval : LamValuation}
  (wfA : LamWF lval.toLamTyVal ⟨lctx, a, s⟩) : LamValid lval lctx (.mkEq s a a) := by
  exists (.mkEq wfA wfA); intro lctxTerm; rfl

theorem LamValid.eq_eq {lval : LamValuation} (heq : a = b)
  (wfA : LamWF lval.toLamTyVal ⟨lctx, a, s⟩) : LamValid lval lctx (.mkEq s a b) := by
  cases heq; apply LamValid.eq_refl wfA

theorem LamValid.eq_symm
  (H : LamValid lval lctx (.mkEq s a b)) :
  LamValid lval lctx (.mkEq s b a) := LamValid.ofLamEquiv (LamEquiv.symm (LamEquiv.ofLamValid H))

theorem LamValid.eq_trans
  (H₁ : LamValid lval lctx (.mkEq s a b))
  (H₂ : LamValid lval lctx (.mkEq s b c)) :
  LamValid lval lctx (.mkEq s a c) :=
  have heqab := LamEquiv.ofLamValid H₁
  have heqbc := LamEquiv.ofLamValid H₂
  LamValid.ofLamEquiv (LamEquiv.trans heqab heqbc)

theorem LamValid.eq_congr
  (HFn : LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂))
  (HArg : LamValid lval lctx (.mkEq argTy arg₁ arg₂)) :
  LamValid lval lctx (.mkEq resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂)) :=
  have heqFn := LamEquiv.ofLamValid HFn
  have heqArg := LamEquiv.ofLamValid HArg
  have heqAp := LamEquiv.congr heqFn heqArg
  LamValid.ofLamEquiv heqAp

theorem LamValid.eq_congrFun
  (HFn : LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂))
  (wfArg₁ : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamValid lval lctx (.mkEq resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg)) := by
  apply LamValid.eq_congr HFn; apply LamValid.eq_refl wfArg₁

theorem LamValid.eq_congrArg
  (HArg : LamValid lval lctx (.mkEq argTy arg₁ arg₂))
  (wfFn₁ : LamWF lval.toLamTyVal ⟨lctx, fn, .func argTy resTy⟩) :
  LamValid lval lctx (.mkEq resTy (.app argTy fn arg₁) (.app argTy fn arg₂)) := by
  apply LamValid.eq_congr _ HArg; apply LamValid.eq_refl wfFn₁

theorem LamValid.eq_funext
  {fn₁ fn₂ : LamTerm}
  (HApp : LamValid lval (pushLCtx argTy lctx) (.mkEq resTy
    (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)))) :
  LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂) :=
  have heqAp := LamEquiv.ofLamValid HApp
  have heqFn := LamEquiv.funext heqAp
  LamValid.ofLamEquiv heqFn

def LamTerm.impApp? (t₁₂ t₁ : LamTerm) : Option LamTerm :=
  match t₁₂ with
  | .app _ (.app _ imp hyp) concl =>
    match hyp.beq t₁ with
    | true =>
      match imp with
      | .base b =>
        match b with
        | .imp => .some concl
        | _ => .none
      | _ => .none
    | false => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_impApp?
  (heq : LamTerm.impApp? t₁₂ t₁ = .some t') : t'.maxEVarSucc ≤ t₁₂.maxEVarSucc := by
  induction t₁₂ generalizing t₁ t' <;> try cases heq
  case app s fn arg IHFn _ =>
    cases fn <;> try cases heq
    case app s' imp hyp =>
      dsimp [impApp?] at heq
      cases h : hyp.beq t₁
      case true =>
        rw [h] at heq; cases imp <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          dsimp [maxEVarSucc]; cases (LamTerm.eq_of_beq_eq_true h)
          apply Nat.le_max_right
      case false =>
        rw [h] at heq; cases heq

theorem LamValid.impApp
  (v₁₂ : LamValid lval lctx t₁₂) (v₁ : LamValid lval lctx t₁)
  (heq : LamTerm.impApp? t₁₂ t₁ = .some t₂) : LamValid lval lctx t₂ := by
  dsimp [LamTerm.impApp?] at heq
  cases t₁₂ <;> try cases heq
  case app bp₁ hypimp concl =>
    cases hypimp <;> try cases heq
    case app bp₂ imp hyp =>
      dsimp at heq
      match h : LamTerm.beq hyp t₁ with
      | true =>
        rw [h] at heq
        cases imp <;> try cases heq
        case base b =>
          cases b <;> cases heq
          case imp =>
            have ⟨wf₁₂, h₁₂⟩ := v₁₂
            match wf₁₂ with
            | .ofApp _ (.ofApp _ (.ofBase .ofImp) HArg) wfConcl =>
              exists wfConcl; have ⟨wf₁, h₁⟩ := v₁;
              intro lctxTerm; apply h₁₂; apply Eq.mp _ (h₁ lctxTerm);
              apply congrArg; apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
              exact .symm (LamTerm.eq_of_beq_eq_true h)
      | false =>
        rw [h] at heq; cases heq

theorem LamThmValid.impApp
  (H₁₂ : LamThmValid lval lctx t₁₂) (H₁ : LamThmValid lval lctx t₁)
  (heq : LamTerm.impApp? t₁₂ t₁ = .some res) : LamThmValid lval lctx res :=
  fun lctx' => LamValid.impApp (H₁₂ lctx') (H₁ lctx') heq

def LamTerm.impApps? (t : LamTerm) (ps : List LamTerm) : Option LamTerm :=
  match ps with
  | .nil => .some t
  | .cons p ps =>
    match t.impApp? p with
    | .some t' => t'.impApps? ps
    | .none => .none

theorem LamTerm.maxEVarSucc_impApps?
  (heq : LamTerm.impApps? t ps = .some t') : t'.maxEVarSucc ≤ t.maxEVarSucc := by
  induction ps generalizing t t'
  case nil => cases heq; apply Nat.le_refl
  case cons p ps IH =>
    dsimp [impApps?] at heq
    match h : impApp? t p with
    | .some t' =>
      rw [h] at heq; dsimp at heq
      apply Nat.le_trans (IH heq) (maxEVarSucc_impApp? h)
    | .none => rw [h] at heq; cases heq

theorem LamValid.impApps
  (vt : LamValid lval lctx t) (vps : HList (LamValid lval lctx) ps)
  (heq : LamTerm.impApps? t ps = .some t') : LamValid lval lctx t' := by
  induction ps generalizing t
  case nil => cases heq; exact vt
  case cons head tail IH =>
    match vps with
    | .cons vHead vTail =>
      dsimp [LamTerm.impApps?] at heq
      match hap : LamTerm.impApp? t head with
      | .some t'' =>
        rw [hap] at heq; dsimp at heq
        apply IH _ vTail heq
        apply LamValid.impApp vt vHead hap
      | .none => rw [hap] at heq; cases heq

theorem LamThmValid.impApps
  (vt : LamThmValid lval lctx t) (vps : HList (LamThmValid lval lctx) ps)
  (heq : LamTerm.impApps? t ps = .some t') : LamThmValid lval lctx t' :=
  fun lctx' => LamValid.impApps (vt lctx') (vps.map (fun _ tv => tv lctx')) heq

def LamTerm.intro1F? (t : LamTerm) : Option (LamSort × LamTerm) :=
  match t with
  | .app _ fn lm =>
    match fn with
    | .base (.forallE s) =>
      match lm with
      | .lam _ t => .some (s, t)
      | _ => .none 
    | _ => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_intro1F?
  (heq : LamTerm.intro1F? t = .some (s, t')) : t'.maxEVarSucc = t.maxEVarSucc := by
  induction t generalizing s t' <;> try cases heq
  case app s fn arg IHFn IHArg =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s' =>
        cases arg <;> try cases heq
        case lam s'' body =>
          dsimp [maxEVarSucc]; rw [Nat.max, Nat.max_def]; simp [Nat.zero_le]

theorem LamValid.intro1F? (H : LamValid lval lctx t)
  (heq : LamTerm.intro1F? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p := by
  dsimp [LamTerm.intro1F?] at heq
  cases t <;> try cases heq
  case app _ fn lm =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        cases lm <;> try cases heq
        case lam s' t =>
          have ⟨wfl, vl⟩ := H
          match wfl with
          | .ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ Hp) =>
            apply LamValid.intro1F H

-- First-order logic style intro1
theorem LamThmValid.intro1F? (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1F? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs_cons]; apply LamValid.intro1F? (H lctx') heq

def LamTerm.intro1H? (t : LamTerm) : Option (LamSort × LamTerm) :=
  match t with
  | .app _ fn p =>
    match fn with
    | .base (.forallE s) =>
      .some (s, .app s p.bvarLift (.bvar 0))
    | _ => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_intro1H?
  (heq : LamTerm.intro1H? t = .some (s, t')) : t'.maxEVarSucc = t.maxEVarSucc := by
  induction t generalizing s t' <;> try cases heq
  case app s fn arg IHFn _ =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE _ =>
        dsimp [maxEVarSucc, bvarLift, bvarLiftIdx, bvarLiftsIdx];
        rw [LamTerm.maxEVarSucc_mapBVarAt]; apply Nat.max_comm

theorem LamValid.intro1HAux (H : LamValid lval lctx (.app s' (.base (.forallE s)) t)) :
  LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  have ⟨wfl, vl⟩ := H
  match wfl with
  | .ofApp _ (.ofBase (.ofForallE _)) Hp => by
    let Hp' := LamWF.ofBVarLiftIdx (s:=s) 0 _ Hp
    let HApp := LamWF.ofApp s Hp' (.ofBVar 0)
    rw [← pushLCtxAt_zero]; exists HApp; intro lctxTerm
    dsimp [LamWF.interp]
    have vl' := vl (fun n => lctxTerm (.succ n)) (lctxTerm 0)
    apply Eq.mp _ vl'; apply congrArg; apply congrFun;
    apply Eq.trans (LamWF.interp_ofBVarLiftIdx lval (idx:=0) lctx
      (fun n => lctxTerm (Nat.succ n)) (lctxTerm 0) _ Hp) ?req
    apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
    case HLCtxTermEq =>
      apply HEq.funext; intro n; cases n <;> rfl

theorem LamValid.intro1H? (H : LamValid lval lctx t)
  (heq : LamTerm.intro1H? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p := by
  dsimp [LamTerm.intro1H?] at heq
  cases t <;> try cases heq
  case app _ fn p =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        apply LamValid.intro1HAux H

-- Higher-order logic style intro1
theorem LamThmValid.intro1H? (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1H? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs_cons]; apply LamValid.intro1H? (H lctx') heq

def LamTerm.intro1? (t : LamTerm) : Option (LamSort × LamTerm) :=
  match t with
  | .app _ fn p =>
    match fn with
    | .base (.forallE s) =>
      match p with
      | .lam _ t => .some (s, t)
      | _ => .some (s, .app s p.bvarLift (.bvar 0))
    | _ => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_intro1? (heq : LamTerm.intro1? t = .some (s, t')) :
  t'.maxEVarSucc = t.maxEVarSucc := by
  cases t <;> try cases heq
  case app _ fn p =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        dsimp [intro1?] at heq;
        dsimp [maxEVarSucc]; rw [Nat.max, Nat.max_def]; simp [Nat.zero_le]
        cases p <;> cases heq <;> try rfl
        case app.refl =>
          dsimp [maxEVarSucc]; rw [LamTerm.maxEVarSucc_mapBVarAt]; rw [LamTerm.maxEVarSucc_mapBVarAt]
          rw [Nat.max, Nat.max_comm, Nat.max_def]; simp [Nat.zero_le]

theorem LamValid.intro1? (H : LamValid lval lctx t)
  (heq : LamTerm.intro1? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p := by
  dsimp [LamTerm.intro1?] at heq
  cases t <;> try cases heq
  case app _ fn p =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        dsimp at heq
        cases p <;> try apply LamValid.intro1H? H heq
        apply LamValid.intro1F? H heq

theorem LamThmValid.intro1? (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs_cons]; apply LamValid.intro1? (H lctx') heq

def LamTerm.mp? (t : LamTerm) (rw : LamTerm) : Option LamTerm :=
  match rw with
  | .app _ (.app _ (base (.eq _)) arg') res =>
    match t.beq arg' with
    | true => .some res
    | false => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_mp?
  (heq : LamTerm.mp? t rw = .some t') : t'.maxEVarSucc ≤ rw.maxEVarSucc := by
  cases rw <;> try cases heq
  case app s fn arg =>
    cases fn <;> try cases heq
    case app s' fn' arg' =>
      cases fn' <;> try cases heq
      case base b =>
        cases b <;> try cases heq
        dsimp [mp?] at heq
        cases h : t.beq arg'
        case true =>
          rw [h] at heq; cases heq; dsimp [maxEVarSucc]; apply Nat.le_max_right
        case false =>
          rw [h] at heq; cases heq

theorem LamEquiv.mp?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) (Hrw : LamValid lval lctx rw)
  (heq : t.mp? rw = .some t') : LamEquiv lval lctx rty t t' := by
  dsimp [LamTerm.mp?] at heq
  cases rw <;> try cases heq
  case app _ eqap res =>
    cases eqap <;> try cases heq
    case app _ eqT arg' =>
      cases eqT <;> try cases heq
      case base b =>
        cases b <;> try cases heq
        case eq s' =>
          dsimp at heq
          match h : t.beq arg' with
          | true =>
            rw [h] at heq; dsimp at heq; cases heq
            cases (LamTerm.eq_of_beq_eq_true h)
            have ⟨wfrw, _⟩ := Hrw
            have ⟨seq₁, seq₂, _⟩ := LamWF.mkEq_sortEq wfrw
            cases seq₁; cases seq₂
            have ⟨wft', _⟩ := LamEquiv.ofLamValid Hrw
            rcases LamWF.unique wft wft' with ⟨⟨⟩, _⟩
            apply LamEquiv.ofLamValid Hrw
          | false => rw [h] at heq; cases heq

theorem LamThmEquiv.mp?
  (wft : LamThmWF lval lctx rty t) (Hrw : LamThmValid lval lctx rw)
  (heq : t.mp? rw = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.mp? (wft lctx') (Hrw lctx') heq

def LamTerm.congrArg? (t : LamTerm) (rw : LamTerm) : Option LamTerm :=
  match t with
  | .app s fn arg =>
    match rw with
    | .app _ (.app _ (.base (.eq _)) arg') res =>
      match arg.beq arg' with
      | true => .some (.app s fn res)
      | false => .none
    | _ => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_congrArg?
  (ht : t.maxEVarSucc ≤ n) (hrw : rw.maxEVarSucc ≤ n)
  (heq : LamTerm.congrArg? t rw = .some t') : t'.maxEVarSucc ≤ n := by
  cases t <;> try cases heq
  case app s fn arg =>
    cases rw <;> try cases heq
    case app s' fn' res =>
      cases fn' <;> try cases heq
      case app s'' fn'' arg' =>
        cases fn'' <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          case eq s''' =>
            dsimp [congrArg?] at heq
            cases h : arg.beq arg'
            case true =>
              rw [h] at heq; cases heq; dsimp [maxEVarSucc]; rw [Nat.max_le]
              dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
              apply And.intro ht.left
              dsimp [maxEVarSucc] at hrw; rw [Nat.max_le] at hrw
              apply hrw.right
            case false =>
              rw [h] at heq; cases heq

theorem LamEquiv.congrArg?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) (Hrw : LamValid lval lctx rw)
  (heq : t.congrArg? rw = .some t') : LamEquiv lval lctx rty t t' := by
  dsimp [LamTerm.congrArg?] at heq
  cases t <;> try cases heq
  case app s fn arg =>
    dsimp at heq
    cases rw <;> try cases heq
    case app _ eqap res =>
      cases eqap <;> try cases heq
      case app _ eqT arg' =>
        cases eqT <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          case eq sfn =>
            dsimp at heq
            match h : arg.beq arg' with
            | true =>
              rw [h] at heq; dsimp at heq
              cases (LamTerm.eq_of_beq_eq_true h)
              cases heq; cases wft;
              case ofApp s heqAp hres =>
                apply LamEquiv.congrArg hres
                have ⟨wfrw, _⟩ := Hrw
                have ⟨seq₁, seq₂, _⟩ := LamWF.mkEq_sortEq wfrw
                cases seq₁; cases seq₂
                have ⟨argwf, _⟩ := LamEquiv.ofLamValid Hrw
                rcases LamWF.unique argwf heqAp with ⟨⟨⟩, _⟩
                apply LamEquiv.ofLamValid Hrw
            | false =>
              rw [h] at heq; cases heq

theorem LamThmEquiv.congrArg?
  (wft : LamThmWF lval lctx rty t) (Hrw : LamThmValid lval lctx rw)
  (heq : t.congrArg? rw = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.congrArg? (wft lctx') (Hrw lctx') heq

def LamTerm.congrFun? (t : LamTerm) (rw : LamTerm) : Option LamTerm :=
  match t with
  | .app s fn arg =>
    match rw with
    | .app _ (.app _ (.base (.eq _)) fn') res =>
      match fn.beq fn' with
      | true => .some (.app s res arg)
      | false => .none
    | _ => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_congrFun?
  (ht : t.maxEVarSucc ≤ n) (hrw : rw.maxEVarSucc ≤ n)
  (heq : LamTerm.congrFun? t rw = .some t') : t'.maxEVarSucc ≤ n := by
  cases t <;> try cases heq
  case app s fn arg =>
    cases rw <;> try cases heq
    case app s' fn' res =>
      cases fn' <;> try cases heq
      case app s'' fn'' arg' =>
        cases fn'' <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          case eq s''' =>
            dsimp [congrFun?] at heq
            cases h : fn.beq arg'
            case true =>
              rw [h] at heq; cases heq; dsimp [maxEVarSucc]; rw [Nat.max_le]
              dsimp [maxEVarSucc] at hrw; rw [Nat.max_le] at hrw
              apply And.intro hrw.right
              dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
              apply ht.right
            case false =>
              rw [h] at heq; cases heq

theorem LamEquiv.congrFun?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) (Hrw : LamValid lval lctx rw)
  (heq : t.congrFun? rw = .some t') : LamEquiv lval lctx rty t t' := by
  dsimp [LamTerm.congrFun?] at heq
  cases t <;> try cases heq
  case app s fn arg =>
    dsimp at heq
    cases rw <;> try cases heq
    case app _ eqap res =>
      cases eqap <;> try cases heq
      case app _ eqT fn' =>
        cases eqT <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          case eq sfn =>
            dsimp at heq
            match h : fn.beq fn' with
            | true =>
              rw [h] at heq; dsimp at heq
              cases (LamTerm.eq_of_beq_eq_true h)
              cases heq; cases wft
              case ofApp heqAp hres =>
                apply LamEquiv.congrFun _ heqAp
                have ⟨wfrw, _⟩ := Hrw
                have ⟨seq₁, seq₂, _⟩ := LamWF.mkEq_sortEq wfrw
                cases seq₁; cases seq₂
                have ⟨argwf, _⟩ := LamEquiv.ofLamValid Hrw
                rcases LamWF.unique argwf hres with ⟨⟨⟩, _⟩;
                apply LamEquiv.ofLamValid Hrw
            | false =>
              rw [h] at heq; cases heq

theorem LamThmEquiv.congrFun?
  (wft : LamThmWF lval lctx rty t) (Hrw : LamThmValid lval lctx rw)
  (heq : t.congrFun? rw = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.congrFun? (wft lctx') (Hrw lctx') heq

def LamTerm.congr? (t : LamTerm) (rwFn : LamTerm) (rwArg : LamTerm) : Option LamTerm :=
  (t.congrFun? rwFn).bind (LamTerm.congrArg? · rwArg)

theorem LamEquiv.congr?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩)
  (HrwFn : LamValid lval lctx rwFn) (HrwArg : LamValid lval lctx rwArg)
  (heq : t.congr? rwFn rwArg = .some t') : LamEquiv lval lctx rty t t' := by
  dsimp [LamTerm.congr?] at heq
  match hFn : LamTerm.congrFun? t rwFn with
  | .some t'' =>
    rw [hFn] at heq; dsimp [Option.bind] at heq
    apply LamEquiv.trans (LamEquiv.congrFun? wft HrwFn hFn)
    have ⟨_, wfCongr, _⟩ := LamEquiv.congrFun? wft HrwFn hFn
    apply LamEquiv.congrArg? wfCongr HrwArg heq
  | .none => rw [hFn] at heq; cases heq

theorem LamTerm.maxEVarSucc_congr?
  (ht : t.maxEVarSucc ≤ n) (hrwFn : rwFn.maxEVarSucc ≤ n) (hrwArg : rwArg.maxEVarSucc ≤ n)
  (heq : LamTerm.congr? t rwFn rwArg = .some t') : t'.maxEVarSucc ≤ n := by
  dsimp [congr?] at heq;
  cases h : congrFun? t rwFn
  case some t' =>
    rw [h] at heq; dsimp at heq
    apply maxEVarSucc_congrArg? _ hrwArg heq
    apply maxEVarSucc_congrFun? ht hrwFn h
  case none => rw [h] at heq; cases heq

theorem LamThmEquiv.congr?
  (wft : LamThmWF lval lctx rty t)
  (HrwFn : LamThmValid lval lctx rwFn) (HrwArg : LamThmValid lval lctx rwArg)
  (heq : t.congr? rwFn rwArg = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.congr? (wft lctx') (HrwFn lctx') (HrwArg lctx') heq

def LamTerm.congrArgs? (t : LamTerm) (rwArgs : List LamTerm) : Option LamTerm :=
  match rwArgs with
  | .nil => .some t
  | .cons rwArg rwArgs =>
    match t with
    | .app s fn arg =>
      (fn.congrArgs? rwArgs).bind (fun fn' => LamTerm.congrArg? (.app s fn' arg) rwArg)
    | _ => .none

theorem LamTerm.maxEVarSucc_congrArgs?
  (ht : t.maxEVarSucc ≤ n) (hrwArgs : HList (fun rw => rw.maxEVarSucc ≤ n) rwArgs)
  (heq : LamTerm.congrArgs? t rwArgs = .some t') : t'.maxEVarSucc ≤ n := by
  induction rwArgs generalizing t t'
  case nil => unfold congrArgs? at heq; cases heq; exact ht
  case cons head tail IH =>
    cases hrwArgs
    case cons hHead hTail =>
      cases t <;> try cases heq
      case app s fn arg =>
        dsimp [congrArgs?] at heq
        cases h : congrArgs? fn tail
        case some fn' =>
          rw [h] at heq; dsimp [Option.bind] at heq
          apply maxEVarSucc_congrArg? _ hHead heq
          dsimp [maxEVarSucc]; rw [Nat.max_le]
          dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
          apply And.intro _ ht.right
          apply IH ht.left hTail h
        case none =>
          rw [h] at heq; cases heq

theorem LamEquiv.congrArgs?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) (HrwArgs : HList (LamValid lval lctx) rwArgs)
  (heq : t.congrArgs? rwArgs = .some t') : LamEquiv lval lctx rty t t' := by
  induction rwArgs generalizing t t' rty
  case nil =>
    unfold LamTerm.congrArgs? at heq; cases heq; apply LamEquiv.refl wft
  case cons head tail IH =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [LamTerm.congrArgs?] at heq
      match h₁ : LamTerm.congrArgs? fn tail with
      | .some t₁ =>
        rw [h₁] at heq; dsimp at heq
        cases HrwArgs
        case cons HrwHead HrwTail =>
          have .ofApp _ wfFn wfArg := wft
          have fneq := IH wfFn HrwTail h₁
          apply LamEquiv.trans (LamEquiv.congrFun fneq wfArg)
          have ⟨_, wfap, _⟩ := LamEquiv.congrFun fneq wfArg
          exact LamEquiv.congrArg? wfap HrwHead heq
      | .none => rw [h₁] at heq; cases heq

theorem LamThmEquiv.congrArgs?
  (wft : LamThmWF lval lctx rty t) (HrwArgs : HList (LamThmValid lval lctx) rwArgs)
  (heq : t.congrArgs? rwArgs = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.congrArgs? (wft lctx') (HrwArgs.map (fun _ twf => twf lctx')) heq

def LamTerm.congrFunN? (t : LamTerm) (rwFn : LamTerm) (idx : Nat) : Option LamTerm :=
  match t with
  | .app s fn arg =>
    match idx with
    | 0 => t.congrFun? rwFn
    | idx' + 1 => (fun x => .app s x arg) <$> fn.congrFunN? rwFn idx'
  | _ => .none

theorem LamTerm.maxEVarSucc_congrFunN?
  (ht : t.maxEVarSucc ≤ n) (hrwFn : rwFn.maxEVarSucc ≤ n)
  (heq : LamTerm.congrFunN? t rwFn idx = .some t') : t'.maxEVarSucc ≤ n := by
  induction idx generalizing t t'
  case zero =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [congrFunN?] at heq; apply maxEVarSucc_congrFun? ht hrwFn heq
  case succ idx IH =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [congrFunN?] at heq
      cases h : congrFunN? fn rwFn idx
      case some fn' =>
        rw [h] at heq; cases heq
        dsimp [maxEVarSucc]; rw [Nat.max_le]
        dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
        apply And.intro _ ht.right
        apply IH ht.left h
      case none =>
        rw [h] at heq; cases heq

theorem LamEquiv.congrFunN?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) (HrwFn : LamValid lval lctx rwFn)
  (heq : t.congrFunN? rwFn n = .some t') : LamEquiv lval lctx rty t t' := by
  induction n generalizing t t' rty
  case zero =>
    cases t <;> try cases heq
    case app s fn arg =>
      apply LamEquiv.congrFun? wft HrwFn heq
  case succ n IH =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [LamTerm.congrFunN?] at heq
      match h₁ : LamTerm.congrFunN? fn rwFn n with
      | .some t₁ =>
        rw [h₁] at heq; dsimp at heq
        cases Option.some.inj heq
        cases wft; case ofApp HArg HFn =>
          apply LamEquiv.congrFun _ HArg; apply IH HFn h₁
      | .none => rw [h₁] at heq; cases heq

theorem LamThmEquiv.congrFunN?
  (wft : LamThmWF lval lctx rty t) (HrwFn : LamThmValid lval lctx rwFn)
  (heq : t.congrFunN? rwFn n = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.congrFunN? (wft lctx') (HrwFn lctx') heq

def LamTerm.congrs? (t : LamTerm) (rwFn : LamTerm) (rwArgs : List LamTerm) : Option LamTerm :=
  match rwArgs with
  | .nil => t.mp? rwFn
  | .cons rwArg rwArgs =>
    match t with
    | .app s fn arg =>
      (fn.congrs? rwFn rwArgs).bind (fun fn' => LamTerm.congrArg? (.app s fn' arg) rwArg)
    | _ => .none

theorem LamTerm.maxEVarSucc_congrs?
  (ht : t.maxEVarSucc ≤ n) (hrwFn : rwFn.maxEVarSucc ≤ n) (hrwArgs : HList (fun rw => rw.maxEVarSucc ≤ n) rwArgs)
  (heq : LamTerm.congrs? t rwFn rwArgs = .some t') : t'.maxEVarSucc ≤ n := by
  induction rwArgs generalizing t t'
  case nil => unfold congrs? at heq; apply Nat.le_trans (maxEVarSucc_mp? heq) hrwFn
  case cons head tail IH =>
    cases hrwArgs
    case cons hHead hTail =>
      cases t <;> try cases heq
      case app s fn arg =>
        dsimp [congrs?] at heq
        cases h : congrs? fn rwFn tail
        case some fn' =>
          rw [h] at heq; dsimp [Option.bind] at heq
          apply maxEVarSucc_congrArg? _ hHead heq
          dsimp [maxEVarSucc]; rw [Nat.max_le]
          dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
          apply And.intro _ ht.right
          apply IH ht.left hTail h
        case none =>
          rw [h] at heq; cases heq

theorem LamEquiv.congrs?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩)
  (HrwFn : LamValid lval lctx rwFn) (HrwArgs : HList (LamValid lval lctx) rwArgs)
  (heq : t.congrs? rwFn rwArgs = .some t') : LamEquiv lval lctx rty t t' := by
  induction rwArgs generalizing rty t t'
  case nil =>
    unfold LamTerm.congrs? at heq; apply LamEquiv.mp? wft HrwFn heq
  case cons head tail IH =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [LamTerm.congrs?] at heq
      match h₁ : LamTerm.congrs? fn rwFn tail with
      | .some t₁ =>
        rw [h₁] at heq; dsimp at heq
        cases HrwArgs
        case cons HrwHead HrwTail =>
          have .ofApp _ wfFn wfArg := wft
          have fneq := IH wfFn HrwTail h₁
          apply LamEquiv.trans (LamEquiv.congrFun fneq wfArg)
          have ⟨_, wfap, _⟩ := LamEquiv.congrFun fneq wfArg
          apply LamEquiv.congrArg? wfap HrwHead heq
      | .none => rw [h₁] at heq; cases heq

theorem LamThmEquiv.congrs?
  (wft : LamThmWF lval lctx rty t)
  (HrwFn : LamThmValid lval lctx rwFn) (HrwArgs : HList (LamThmValid lval lctx) rwArgs)
  (heq : t.congrs? rwFn rwArgs = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => LamEquiv.congrs? (wft lctx') (HrwFn lctx') (HrwArgs.map (fun _ twf => twf lctx')) heq

theorem LamThmValid.define {lval : LamValuation.{u}}
  (wft : LamThmWF lval [] s t) (heVar : t.maxEVarSucc ≤ eidx) :
  ∃ val, LamThmValid (lval.insertEVarAt s val eidx) [] (.mkEq s (.etom eidx) t) := by
  exists LamWF.interp lval dfLCtxTy (dfLCtxTerm _) (wft dfLCtxTy)
  apply LamThmValid.ofLamThmValidD
  let ltv₁ := lval.toLamTyVal
  let ltv₂ := { lval.toLamTyVal with lamEVarTy := replaceAt s eidx lval.lamEVarTy}
  have wft' := LamWF.eVarIrrelevance (ltv₁:=ltv₁) (ltv₂:=ltv₂) rfl rfl
    (fun n H => LamTyVal.insertEVarAt_eVarIrrelevance (Nat.le_trans H heVar)) (wft dfLCtxTy)
  apply And.intro
  case left =>
    rw [LamTerm.maxLooseBVarSucc_mkEq]; dsimp [LamTerm.maxLooseBVarSucc]
    rw [Nat.max_zero_left]; have ⟨_, hlb⟩ := LamThmWFD.ofLamThmWF wft; apply hlb
  case right =>
    exists LamWF.mkEq LamWF.insertEVarAt_eIdx wft'
    intro lctxTerm; dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn]
    apply eq_of_heq; apply HEq.trans (LamWF.interp_insertEVarAt_eIdx _)
    apply LamWF.interp_eVarIrrelevance <;> try rfl
    intro n hn; apply LamValuation.insertEVarAt_eVarIrrelevance
    apply Nat.le_trans hn heVar

section Skolemization

  def LamTerm.skolemize? (t : LamTerm) (eidx : Nat) (lctx : List LamSort) : Option (LamSort × LamTerm) :=
    match t with
    | .app _ (.base (.existE s)) p => .some (s, .app s p (LamTerm.bvarApps (.etom eidx) lctx 0))
    | _ => .none

  theorem LamTerm.maxEVarSucc_skolemize? (heq : LamTerm.skolemize? t eidx lctx = .some (s, t')) :
    t'.maxEVarSucc ≤ max t.maxEVarSucc (.succ eidx) := by
    cases t <;> try cases heq
    case app s fn arg =>
      cases fn <;> try cases heq
      case base b =>
        cases b <;> try cases heq
        case existE s =>
          dsimp [maxEVarSucc]; rw [LamTerm.maxEVarSucc_bvarApps]; simp [Nat.max]
          rw [Nat.max_zero_left]; apply Nat.le_refl
  
  theorem choose_spec' {p : α → β → Prop} (h : ∀ q, ∃ x, p x q) : ∃ (y : _ → _), ∀ q, p (y q) q :=
    ⟨fun q => Classical.choose (h q), fun q => Classical.choose_spec (h q)⟩

  theorem LamThmValid.skolemize
    (vt : LamThmValid lval lctx (.mkExistE s p)) (heVar : p.maxEVarSucc ≤ eidx) :
    ∃ val, LamThmValid (lval.insertEVarAt (s.mkFuncsRev lctx) val eidx) lctx (.app s p (LamTerm.bvarApps (.etom eidx) lctx 0)) := by
    have ⟨hSucc, ⟨wft, ht⟩⟩ := LamThmValidD.ofLamThmValid vt
    cases wft; case ofApp HArg HFn => cases HFn; case ofBase Hb => cases Hb; case ofExistE =>
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, existLiftFn] at ht;
      have ⟨valPre, hvalPre⟩ := choose_spec' ht
      exists LamSort.curryRev valPre; apply LamThmValid.ofLamThmValidD; apply And.intro;
      case left =>
        dsimp [LamTerm.maxLooseBVarSucc]; rw [Nat.max_le]; apply And.intro (Nat.max_le.mp hSucc).right
        apply Nat.le_trans LamTerm.maxLooseBVarSucc_bvarApps; rw [Nat.max_le]
        apply And.intro (Nat.zero_le _) .refl
      case right =>
        let ltv₁ := lval.toLamTyVal
        let ltv₂ := { lval.toLamTyVal with lamEVarTy := replaceAt (s.mkFuncsRev lctx) eidx lval.lamEVarTy}
        have HArg' := LamWF.eVarIrrelevance (ltv₁:=ltv₁) (ltv₂:=ltv₂) rfl rfl
          (fun n H => LamTyVal.insertEVarAt_eVarIrrelevance (Nat.le_trans H heVar)) HArg
        exists (.ofApp _ HArg' (LamWF.bvarApps (ex:=[]) LamWF.insertEVarAt_eIdx))
        intro lctxTerm; dsimp [LamWF.interp]
        apply Eq.mp _ (hvalPre lctxTerm); apply congrArg; apply eq_of_heq
        apply congr_hd_heq <;> try rfl
        case h₁ =>
          apply LamWF.interp_eVarIrrelevance <;> try rfl;
          intros n H; apply LamValuation.insertEVarAt_eVarIrrelevance;
          apply Nat.le_trans H heVar
        case h₂ =>
          apply HEq.symm
          apply LamWF.interp_bvarApps (tyex:=[]) (termex:=.nil) LamWF.insertEVarAt_eIdx
          apply LamWF.interp_insertEVarAt_eIdx

  theorem LamThmValid.skolemize?
    (vt : LamThmValid lval lctx t) (heq : t.skolemize? eidx lctx = .some (s, t'))
    (heVar : t.maxEVarSucc ≤ eidx) :
    ∃ val, LamThmValid (lval.insertEVarAt (s.mkFuncsRev lctx) val eidx) lctx t' := by
    have ⟨hSucc, ⟨wft, ht⟩⟩ := LamThmValidD.ofLamThmValid vt
    cases t <;> try cases heq
    case app sp fn arg =>
      cases fn <;> try cases heq
      case base b =>
        cases b <;> try cases heq
        case existE.refl =>
        cases wft; case ofApp HArg HFn =>
          cases HFn; case ofBase Hb =>
            cases Hb; case ofExistE =>
              dsimp [LamTerm.maxEVarSucc] at heVar; rw [Nat.max_le] at heVar
              apply LamThmValid.skolemize vt heVar.right

end Skolemization

section UnsafeOps
  
  def LamTerm.replace (t : LamTerm) (f : LamTerm → Option LamTerm) (lvl : Nat) :=
    match f (t.bvarLifts lvl) with
    | .some t' => t'.bvarLifts lvl
    | .none =>
      match t with
      | .app s fn arg => .app s (replace fn f lvl) (replace arg f lvl)
      | .lam s body => .lam s (replace body f (.succ lvl))
      | _ => t
  
  -- Turn `ts[i]` into `.bvar i`
  def LamTerm.abstractsImp (t : LamTerm) (ts : Array LamTerm) :=
    let ts := ts.mapIdx (fun i x => (x, LamTerm.bvar i.val))
    let tmap := @Lean.HashMap.ofList _ _ inferInstance inferInstance ts.data
    t.replace (fun x => tmap.find? x) 0
  
  def LamTerm.abstractsRevImp (t : LamTerm) (ts : Array LamTerm) := t.abstractsImp ts.reverse
  
  def LamTerm.instantiatesAtImp (idx : Nat) (args : Array LamTerm) : (body : LamTerm) → LamTerm
  | .atom n        => .atom n
  | .etom n        => .etom n
  | .base b        => .base b
  | .bvar n        =>
    match idx.ble n with
    | true =>
      match (n - idx).blt args.size with
      | true => (args[n - idx]?.getD (.base .trueE)).bvarLifts idx
      | false => LamTerm.bvar (n - args.size)
    | false => LamTerm.bvar n
  | .lam s body    => .lam s (LamTerm.instantiatesAtImp (.succ idx) args body)
  | .app s fn arg' => .app s (LamTerm.instantiatesAtImp idx args fn) (LamTerm.instantiatesAtImp idx args arg')
  
  def LamTerm.instantiatesImp := LamTerm.instantiatesAtImp 0

end UnsafeOps

end Auto.Embedding.Lam