import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

abbrev LamEquiv {lval : LamValuation} {lctx : Nat → LamSort} {rty : LamSort}
  (t₁ t₂ : LamTerm) (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, rty⟩) :=
  ∃ (wf₂ : LamWF lval.toLamTyVal ⟨lctx, t₂, rty⟩),
    ∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal),
      LamWF.interp lval lctx lctxTerm wf₁ =
        LamWF.interp lval lctx lctxTerm wf₂

theorem LamEquiv.toForall {lval : LamValuation} (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, rty⟩)
  (leq : LamEquiv t₁ t₂ wf) : ∀ (rty' : _) (wf' : LamWF lval.toLamTyVal ⟨lctx, t₁, rty'⟩),
  LamEquiv t₁ t₂ wf' := fun rty' wf' => by
    cases (LamWF.unique wf wf')
    case intro left right =>
      cases left; cases right; exact leq

-- Semantic Equivalence
-- Note that we do not expect to reorder binders or remove
--   unused binders, because doing so makes the term not equivalent
--   to the original one
def LamThmEquiv (lval : LamValuation) (lctx : List LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∀ (lctx' : Nat → LamSort),
    ∃ (wf₁ : LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t₁, rty⟩),
    LamEquiv t₁ t₂ wf₁

theorem LamThmWF.ofLamThmEquiv_l (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₁ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨wf, _⟩ := teq lctx'; ⟨wf⟩))

theorem LamThmWF.ofLamThmEquiv_r (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₂ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨_, ⟨wf, _⟩⟩ := teq lctx'; ⟨wf⟩))

theorem LamEquiv.refl (lval : LamValuation) (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv t t wf := ⟨wf, fun _ => rfl⟩

theorem LamThmEquiv.refl (lval : LamValuation) (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t := fun lctx => ⟨wf lctx, LamEquiv.refl _ _⟩

theorem LamEquiv.eq (lval : LamValuation) (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩)
  (heq : t₁ = t₂) : LamEquiv t₁ t₂ wf := heq ▸ LamEquiv.refl lval wf

theorem LamThmEquiv.eq (lval : LamValuation) (wf : LamThmWF lval lctx s t₁)
  (heq : t₁ = t₂) : LamThmEquiv lval lctx s t₁ t₂ := fun lctx => ⟨wf lctx, LamEquiv.eq _ (wf lctx) heq⟩

theorem LamEquiv.symm (lval : LamValuation) (wfa : LamWF lval.toLamTyVal ⟨lctx, a, rty⟩)
  (e : LamEquiv a b wfa) : ∃ (wfb : LamWF lval.toLamTyVal ⟨lctx, b, rty⟩), LamEquiv b a wfb :=
  let ⟨wfb, eq⟩ := e; ⟨wfb, ⟨wfa, fun lctxTerm => Eq.symm (eq lctxTerm)⟩⟩

theorem LamThmEquiv.symm (lval : LamValuation) (e : LamThmEquiv lval lctx rty a b) :
  LamThmEquiv lval lctx rty b a := fun lctx => let ⟨wfa, h⟩ := e lctx; LamEquiv.symm _ wfa h

theorem LamEquiv.trans (lval : LamValuation)
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, rty⟩) (wfb : LamWF lval.toLamTyVal ⟨lctx, b, rty⟩)
  (eab : LamEquiv a b wfa) (ebc : LamEquiv b c wfb) :  LamEquiv a c wfa :=
  let ⟨wfb, eqab⟩ := eab; let ⟨wfc, eqbc⟩ := ebc; ⟨wfc, fun lctxTerm =>
    by rw [eqab, ←eqbc]; apply eq_of_heq; apply LamWF.interp.heq <;> rfl⟩

theorem LamThmEquiv.trans (lval : LamValuation)
  (e₁ : LamThmEquiv lval lctx rty a b) (e₂ : LamThmEquiv lval lctx rty b c) :
  LamThmEquiv lval lctx rty a c :=
  fun lctx' => let ⟨wfa, eqab⟩ := e₁ lctx'; let ⟨wfb, eqbc⟩ := e₂ lctx'; ⟨wfa, LamEquiv.trans lval wfa wfb eqab eqbc⟩

theorem LamEquiv.ofLam (lval : LamValuation)
  (wfa : LamWF lval.toLamTyVal ⟨pushLCtx w lctx, a, s⟩) (e : LamEquiv a b wfa) :
  LamEquiv (.lam w a) (.lam w b) (.ofLam s wfa) :=
  let ⟨wfb, eqab⟩ := e; ⟨.ofLam _ wfb, fun _ => funext (fun _ => eqab _)⟩

theorem LamThmEquiv.ofLam (lval : LamValuation)
  (e : LamThmEquiv lval (w :: lctx) s a b) :
  LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) := fun lctx' =>
    let ⟨wfa, eqab⟩ := pushLCtxs.cons _ _ ▸ e lctx';
    ⟨(.ofLam s wfa), LamEquiv.ofLam lval _ eqab⟩

theorem LamEquiv.fromLam (lval : LamValuation)
  (wfa : LamWF lval.toLamTyVal ⟨pushLCtx w lctx, a, s⟩)
  (e : LamEquiv (.lam w a) (.lam w b) (.ofLam s wfa)) : LamEquiv a b wfa :=
  let ⟨.ofLam _ wfb, eqlab⟩ := e
  ⟨wfb, fun lctxTerm =>
    let h := congrFun (eqlab (fun n => lctxTerm (.succ n))) (lctxTerm 0)
    by
      dsimp [LamWF.interp] at h
      apply Eq.trans ?left (Eq.trans h ?right) <;>
        apply eq_of_heq
      case left =>
        apply LamWF.interp.heq <;> try rfl
        apply HEq.symm; apply pushDep_popDep_eq lctxTerm
      case right =>
        apply LamWF.interp.heq <;> try rfl
        apply pushDep_popDep_eq⟩

theorem LamThmEquiv.fromLam (lval : LamValuation)
  (e : LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamThmEquiv lval (w :: lctx) s a b := fun lctx' => by
  rw [pushLCtxs.cons]
  let ⟨.ofLam _ wfa, leqab⟩ := e lctx';
  exists wfa; apply LamEquiv.fromLam _ _ leqab

theorem LamEquiv.eqLam (lval : LamValuation)
  (wfa : LamWF lval.toLamTyVal ⟨pushLCtx w lctx, a, s⟩) :
  LamEquiv a b wfa = LamEquiv (.lam w a) (.lam w b) (.ofLam s wfa) :=
  propext (Iff.intro (LamEquiv.ofLam _ _) (LamEquiv.fromLam _ _))

theorem LamThmEquiv.eqLam (lval : LamValuation) :
  LamThmEquiv lval (w :: lctx) s a b = LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro (LamThmEquiv.ofLam _) (LamThmEquiv.fromLam _))

theorem LamEquiv.congr (lval : LamValuation)
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn₁, (.func argTy resTy)⟩) (eFn : LamEquiv fn₁ fn₂ wfFn)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg₁, argTy⟩) (eArg : LamEquiv arg₁ arg₂ wfArg) :
  LamEquiv (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) (.ofApp _ wfFn wfArg) :=
  let ⟨wfFn₂, HFn⟩ := eFn
  let ⟨wfArg₂, HArg⟩ := eArg
  ⟨.ofApp _ wfFn₂ wfArg₂, fun _ => _root_.congr (HFn _) (HArg _)⟩

theorem LamThmEquiv.congr (lval : LamValuation)
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := fun lctx' =>
    let ⟨wfFn, HFn⟩ := eFn lctx'
    let ⟨wfArg, HArg⟩ := eArg lctx'
    ⟨.ofApp _ wfFn wfArg, LamEquiv.congr _ _ HFn _ HArg⟩

theorem LamEquiv.congrFun (lval : LamValuation)
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn₁, .func argTy resTy⟩) (eFn : LamEquiv fn₁ fn₂ wfFn)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamEquiv (.app argTy fn₁ arg) (.app argTy fn₂ arg) (.ofApp _ wfFn wfArg) :=
  LamEquiv.congr _ _ eFn _ (LamEquiv.refl _ _)

theorem LamThmEquiv.congrFun (lval : LamValuation)
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamThmWF lval lctx argTy arg) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamThmEquiv.congr lval eFn (LamThmEquiv.refl lval wfArg)

theorem LamEquiv.congrArg (lval : LamValuation)
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn, .func argTy resTy⟩)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg₁, argTy⟩) (eArg : LamEquiv arg₁ arg₂ wfArg) :
  LamEquiv (.app argTy fn arg₁) (.app argTy fn arg₂) (.ofApp _ wfFn wfArg) :=
  LamEquiv.congr _ _ (LamEquiv.refl _ _) _ eArg

theorem LamThmEquiv.congrArg (lval : LamValuation)
  (wfFn : LamThmWF lval lctx (.func argTy resTy) fn)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamThmEquiv.congr lval (LamThmEquiv.refl lval wfFn) eArg

theorem LamEquiv.congrs (lval : LamValuation) {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hFn : ∀ (fnTy : _) (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn₁, fnTy⟩),
    LamEquiv fn₁ fn₂ wfFn)
  (hArgs : HList ((fun (_, arg₁, arg₂) => ∀ (argTy : _) (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg₁, argTy⟩),
    LamEquiv arg₁ arg₂ wfArg)) args) :
  LamEquiv
    (LamTerm.mkAppN fn₁ (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn₂ (args.map (fun (s, _, t₂) => (s, t₂))))
    wfApp := by
  revert fn₁ fn₂ hArgs; induction args <;> intro fn₁ fn₂ wfApp hFn hArgs
  case nil => apply hFn
  case cons head tail IH =>
    match head with
    | ⟨s, t₁, t₂⟩ =>
      apply IH
      case hFn =>
        intros fnTy wfFn;
        match wfFn with
        | .ofApp _ wfFn' wfArg' =>
          apply LamEquiv.congr _ _ (hFn _ _)
          match hArgs with
          | .cons hHead _ => apply hHead
      case hArgs =>
        match hArgs with
        | .cons _ hTail => apply hTail

theorem LamEquiv.congrArgs (lval : LamValuation) {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hArgs : HList ((fun (_, arg₁, arg₂) => ∀ (argTy : _) (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg₁, argTy⟩),
    LamEquiv arg₁ arg₂ wfArg)) args) :
  LamEquiv
    (LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn (args.map (fun (s, _, t₂) => (s, t₂))))
    wfApp := LamEquiv.congrs lval wfApp (fun _ wfFn => LamEquiv.refl _ wfFn) hArgs

theorem LamEquiv.congrFunN (lval : LamValuation) {args : List (LamSort × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ args, resTy⟩)
  (hFn : ∀ (fnTy : _) (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn₁, fnTy⟩), LamEquiv fn₁ fn₂ wfFn) :
  LamEquiv (LamTerm.mkAppN fn₁ args) (LamTerm.mkAppN fn₂ args) wfApp := by
  let masterArr := args.map (fun (s, arg) => (s, arg, arg))
  have eq₁ : args = masterArr.map (fun (s, arg₁, _) => (s, arg₁)) := by
    rw [List.map_map]; rw [List.map_equiv _ id, List.map_id];
    intro x; cases x; rfl
  have eq₂ : args = masterArr.map (fun (s, _, arg₂) => (s, arg₂)) := by
    rw [List.map_map]; rw [List.map_equiv _ id, List.map_id];
    intro x; cases x; rfl
  have eqt₂ : LamTerm.mkAppN fn₂ args = LamTerm.mkAppN fn₂ (masterArr.map (fun (s, arg₁, arg₂) => (s, arg₂))) := by
    rw [← eq₂]
  rw [eqt₂]; revert wfApp; rw [eq₁]; intro wfApp; apply LamEquiv.congrs _ _ hFn
  apply HList.toMapTy; apply HList.ofMapList
  intro x argTy wfArg; apply LamEquiv.refl

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
  revert idx; induction body <;> intro idx <;> try apply Nat.le_max_right
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
      rw [pushLCtxAt.zero] at wfArg'
      dsimp [LamTerm.bvarLifts] at wfArg'
      rw [← LamTerm.bvarLiftsIdx.succ_r] at wfArg'
      exact wfArg')
    (by
      rw [pushLCtx_pushLCtxAt] at H
      exact H)
  .ofLam _ IHArg
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.instantiateAt ltv idx _ wfArg HFn
  let IHArg := LamWF.instantiateAt ltv idx _ wfArg HArg
  .ofApp argTy' IHFn IHArg

theorem LamWF.instantiateAt.correct.{u}
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
  funext (fun x => by
    let wfArg' := LamWF.ofBVarLiftIdx (s:=argTy') (lctx:=lctxTy) 0 _ wfArg
    rw [pushLCtxAt.zero] at wfArg'
    dsimp [LamTerm.bvarLifts] at wfArg'
    rw [← LamTerm.bvarLiftsIdx.succ_r] at wfArg'
    rw [pushLCtx_pushLCtxAt] at H
    let IH := LamWF.instantiateAt.correct lval (.succ idx) (pushLCtx argTy' lctxTy) (pushLCtxDep x lctxTerm) wfArg' H
    apply Eq.trans ?eqLarge (Eq.trans IH ?eqSmall)
    case eqLarge =>
      dsimp [interp]; apply eq_of_heq; apply interp.heq <;> try rfl
      case h.HLCtxTyEq => apply pushLCtx_pushLCtxAt
      case h.HLCtxTermEq =>
        apply HEq.trans (pushLCtxDep_pushLCtxAtDep _ _ _ _)
        apply heq_of_eq
        apply congrArg (f := fun x => pushLCtxAtDep x _ _)
        rw [LamWF.ofBVarLiftIdx.correct (idx:=0) lval _ lctxTerm x _ wfArg]
        apply eq_of_heq; apply interp.heq
        case h.h.HLCtxTyEq => rw [pushLCtxAt.zero]
        case h.h.HLCtxTermEq => apply pushLCtxAtDep.zero
        case h.h.HTeq => rw [← LamTerm.bvarLiftsIdx.succ_r]
    case eqSmall =>
      dsimp [interp]; apply eq_of_heq; apply interp.heq <;> rfl)
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.instantiateAt.correct lval idx lctxTy lctxTerm wfArg HFn
  let IHArg := LamWF.instantiateAt.correct lval idx lctxTy lctxTerm wfArg HArg
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
    rw [pushLCtxAt.zero, LamTerm.bvarLiftsIdx.zero]
    rfl) (@LamWF.instantiateAt ltv 0 arg argTy body bodyTy)

def LamThmWF.instantiate1
  (wfArg : LamThmWF lval lctx argTy arg) (wfBody : LamThmWF lval (argTy :: lctx) bodyTy body) :
  LamThmWF lval lctx bodyTy (LamTerm.instantiate1 arg body) := by
  intro lctx'; have hArg := wfArg lctx'; have hBody := wfBody lctx'
  rw [pushLCtxs.cons] at hBody; apply LamWF.instantiate1 _ _ hArg hBody

theorem LamWF.instantiate1.correct.{u}
  (lval : LamValuation.{u}) {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, arg, argTy⟩)
  (wfBody : LamWF lval.toLamTyVal ⟨pushLCtx argTy lctxTy, body, bodyTy⟩) :
  let wfInstantiate1' := LamWF.instantiate1 lval.toLamTyVal lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtx argTy lctxTy)
    (pushLCtxDep (LamWF.interp lval lctxTy lctxTerm wfArg) lctxTerm) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfInstantiate1') := by
  apply Eq.trans ?eqLarge (Eq.trans (@LamWF.instantiateAt.correct lval 0
    arg argTy body bodyTy lctxTy lctxTerm (Eq.mp ?eqArg wfArg) (Eq.mp ?eqBody wfBody)) ?eqSmall)
  case eqArg => dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx.zero]
  case eqBody => rw [pushLCtxAt.zero]
  case eqLarge =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => rw [pushLCtxAt.zero]
    case h.HLCtxTermEq =>
      apply HEq.trans (HEq.symm (pushLCtxAtDep.zero _ _)) _
      apply HEq.funext; intro x;
      apply pushLCtxAtDep.heq <;> try rfl
      apply LamWF.interp.heq <;> try rfl
      dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx.zero]
  case eqSmall =>
    apply eq_of_heq; apply LamWF.interp.heq <;> rfl

theorem LamThmValid.instantiate1
  (hw : LamThmWF lval lctx argTy arg) (hv : LamThmValid lval (argTy :: lctx) body) :
  LamThmValid lval lctx (LamTerm.instantiate1 arg body) := by
  intro lctx'; have hArg := hw lctx'; have hBody := hv lctx'
  rw [pushLCtxs.cons] at hBody; have ⟨wfBody, vBody⟩ := hBody
  exists (LamWF.instantiate1 _ _ hArg wfBody); intro lctxTerm;
  rw [← LamWF.instantiate1.correct]; apply vBody

def LamBaseTerm.resolveImport (ltv : LamTyVal) : LamBaseTerm → LamBaseTerm
| .eqI n      => .eq (ltv.lamILTy n)
| .forallEI n => .forallE (ltv.lamILTy n)
| .existEI n  => .existE (ltv.lamILTy n)
| t           => t

def LamBaseTerm.LamWF.resolveImport {ltv : LamTyVal} {b : LamBaseTerm} {ty : LamSort}
  (wfB : LamBaseTerm.LamWF ltv b ty) : LamBaseTerm.LamWF ltv (b.resolveImport ltv) ty := by
  cases wfB <;> constructor

theorem LamBaseTerm.LamWF.resolveImport.correct
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

theorem LamWF.resolveImport.correct
  {lval : LamValuation.{u}} {t : LamTerm} {ty : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfT : LamWF lval.toLamTyVal ⟨lctxTy, t, ty⟩) :
  let wfRB := LamWF.resolveImport wfT
  LamWF.interp lval lctxTy lctxTerm wfT = LamWF.interp lval lctxTy lctxTerm wfRB :=
  match wfT with
  | .ofAtom _ => rfl
  | .ofEtom _ => rfl
  | .ofBase b => LamBaseTerm.LamWF.resolveImport.correct lval b
  | .ofBVar n => rfl
  | .ofLam s hwf => by
    apply funext; intros x; dsimp [interp]
    rw [LamWF.resolveImport.correct _ _ hwf]
  | .ofApp s wfFn wfArg => by
    dsimp [interp];
    rw [LamWF.resolveImport.correct _ _ wfFn]
    rw [LamWF.resolveImport.correct _ _ wfArg]

theorem LamThmValid.resolveImport (H : LamThmValid lval lctx t) :
  LamThmValid lval lctx (t.resolveImport lval.toLamTyVal) := by
  intro lctx; let ⟨wf, h⟩ := H lctx;
  exists (LamWF.resolveImport wf); intro lctxTerm
  rw [← LamWF.resolveImport.correct]; apply h

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

def LamWF.topBetaAux.correct.{u} (lval : LamValuation.{u})
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
    | _, .ofLam (argTy:=_) (body:=_) _ _ => LamWF.instantiate1.correct _ _ _ _ _
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

theorem LamWF.topBeta.correct
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
    | .ofApp _ wfFn wfArg => LamWF.topBetaAux.correct _ lctxTy lctxTerm wfArg wfFn

theorem LamThmValid.topBeta (H : LamThmValid lval lctx t) :
  LamThmValid lval lctx t.topBeta := by
  intros lctx; let ⟨wf, h⟩ := H lctx; exists (LamWF.topBeta _ _ wf);
  intro lctxTerm; rw [← LamWF.topBeta.correct]; apply h

theorem LamEquiv.ofTopBeta {lval : LamValuation}
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) : LamEquiv t t.topBeta wf :=
  ⟨LamWF.topBeta _ _ wf, fun _ => LamWF.topBeta.correct _ _ _⟩

theorem LamThmEquiv.ofTopBeta (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t.topBeta :=
  fun lctx' => ⟨wf lctx', LamEquiv.ofTopBeta (wf lctx')⟩

def LamTerm.beta (t : LamTerm) : List (LamSort × LamTerm) → LamTerm
| .nil => t
| arg :: args =>
  match t with
  | .lam _ t' => (LamTerm.instantiate1 arg.snd t').beta args
  | t => t.mkAppN (arg :: args)

theorem LamTerm.maxEVarSucc_beta
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  (LamTerm.beta t args).maxEVarSucc ≤ n := by
  revert t; induction hs <;> intro t ht
  case nil => exact ht
  case cons argty argtys harg hargs IH =>
    cases t <;> try apply LamTerm.maxEVarSucc_mkAppN (.cons harg hargs) ht
    case lam s body =>
      dsimp [beta]; apply IH
      apply Nat.le_trans LamTerm.maxEVarSucc_instantiate1
      rw [Nat.max_le]; apply And.intro harg ht

theorem LamEquiv.ofBeta (lval : LamValuation.{u})
  (fn : LamTerm) (args : List (LamSort × LamTerm))
  (wf : LamWF lval.toLamTyVal ⟨lctx, fn.mkAppN args, resTy⟩) :
  LamEquiv _ (fn.beta args) wf :=
  match args with
  | .nil => ⟨wf, fun _ => rfl⟩
  | arg :: args =>
    match fn with
    | .atom _ => ⟨wf, fun _ => rfl⟩
    | .etom _ => ⟨wf, fun _ => rfl⟩
    | .base _ => ⟨wf, fun _ => rfl⟩
    | .bvar _ => ⟨wf, fun _ => rfl⟩
    | .lam s' t' => by
      dsimp [LamTerm.mkAppN, LamTerm.beta]
      dsimp [LamTerm.mkAppN] at wf
      let ⟨apTy, wfAp⟩ := LamWF.getAppFn (args:=args) wf
      have hTop := LamEquiv.ofTopBeta wfAp;
      dsimp only [LamTerm.topBeta, LamTerm.topBetaAux] at hTop
      have hCongr := LamEquiv.congrFunN _ (args:=args) wf hTop.toForall
      let ⟨hCongrWF, CongrEq⟩ := hCongr
      apply LamEquiv.trans _ _ hCongrWF ⟨hCongrWF, CongrEq⟩
      apply LamEquiv.ofBeta lval _ args
    | .app _ _ _ => ⟨wf, fun _ => rfl⟩

def LamTerm.headBetaAux : List (LamSort × LamTerm) → LamTerm → LamTerm
| args, .app s fn arg => headBetaAux ((s, arg) :: args) fn
| args, t             => beta t args

theorem LamTerm.maxEVarSucc_headBetaAux
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  (LamTerm.headBetaAux args t).maxEVarSucc ≤ n := by
  revert args; induction t <;> intro args hs <;> try apply LamTerm.maxEVarSucc_beta hs ht
  case app s fn arg IHFn IHArg =>
    dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
    exact IHFn ht.left (.cons ht.right hs)

theorem LamEquiv.ofHeadBetaAux (lval : LamValuation.{u})
  (wf : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN t args, rty⟩) :
  LamEquiv _ (t.headBetaAux args) wf := by
  revert args wf; induction t <;> intro args wf <;>
    try (cases args <;> apply LamEquiv.refl)
  case lam s body _ => apply LamEquiv.ofBeta
  case app s fn arg IHFn _ => dsimp [LamTerm.headBetaAux]; apply IHFn

def LamTerm.headBeta := LamTerm.headBetaAux []

theorem LamTerm.maxEVarSucc_headBeta :
  (LamTerm.headBeta t).maxEVarSucc ≤ t.maxEVarSucc :=
  LamTerm.maxEVarSucc_headBetaAux .nil (Nat.le_refl _)

theorem LamEquiv.ofHeadBeta (lval : LamValuation.{u})
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) :
  LamEquiv _ t.headBeta wf := by cases t <;> apply LamEquiv.ofHeadBetaAux (args:=[]) lval wf

theorem LamThmEquiv.ofHeadBeta (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t.headBeta :=
  fun lctx => ⟨wf lctx, LamEquiv.ofHeadBeta _ (wf lctx)⟩

def LamTerm.headBetaBounded (n : Nat) (t : LamTerm) :=
  match n with
  | 0 => t
  | .succ n' =>
    match t.isHeadBetaTarget with
    | true => headBetaBounded n' t.headBeta
    | false => t

theorem LamTerm.maxEVarSucc_headBetaBounded :
  (LamTerm.headBetaBounded n t).maxEVarSucc ≤ t.maxEVarSucc := by
  revert t; induction n <;> intro t
  case zero => apply Nat.le_refl
  case succ n IH =>
    dsimp [headBetaBounded]
    cases (isHeadBetaTarget t) <;> try apply Nat.le_refl
    dsimp; apply Nat.le_trans IH; apply maxEVarSucc_headBeta

theorem LamEquiv.ofHeadBetaBounded (lval : LamValuation.{u})
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) : LamEquiv _ (t.headBetaBounded n) wf := by
  revert t; induction n <;> intro t wf
  case zero => apply LamEquiv.refl
  case succ n IH =>
    dsimp [LamTerm.headBetaBounded]
    match t.isHeadBetaTarget with
    | true =>
      dsimp
      let ⟨wfBeta, eqBeta⟩ := LamEquiv.ofHeadBeta _ wf
      apply LamEquiv.trans _ wf wfBeta ⟨wfBeta, eqBeta⟩
      apply IH
    | false => apply LamEquiv.refl

theorem LamThmEquiv.ofHeadBetaBounded (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t (t.headBetaBounded n) :=
  fun lctx => ⟨wf lctx, LamEquiv.ofHeadBetaBounded _ (wf lctx)⟩

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
  revert t; induction n <;> intro t
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
  | .atom _ => true
  | .etom _ => true
  | .base _ => true
  | .bvar _ => true
  | .app _ fn arg =>
    !(fn.isLam) && fn.betaReduced && arg.betaReduced
  | .lam _ body => body.betaReduced

theorem LamEquiv.ofBetaBounded (lval : LamValuation.{u})
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) : LamEquiv _ (t.betaBounded n) wf := by
  revert rty t lctx; induction n <;> intro lctx t rty wf
  case zero => apply LamEquiv.refl
  case succ n IH =>
    dsimp [LamTerm.betaBounded]
    match t with
    | .atom _ => apply LamEquiv.refl
    | .etom _ => apply LamEquiv.refl
    | .base _ => apply LamEquiv.refl
    | .bvar _ => apply LamEquiv.refl
    | .lam s t =>
      dsimp
      match wf with
      | .ofLam _ wf => apply LamEquiv.ofLam; apply IH wf
    | .app s fn arg =>
      dsimp;
      let ⟨wfhbb, _⟩ := LamEquiv.ofHeadBetaBounded (n:=n) lval wf
      apply LamEquiv.trans _ _ wfhbb (LamEquiv.ofHeadBetaBounded _ wf)
      let ⟨wftap, eqtap⟩ := LamEquiv.eq _ wfhbb (LamTerm.appFn_appArg_eq _)
      apply LamEquiv.trans _ _ wftap ⟨wftap, eqtap⟩
      let masterArr := (LamTerm.getAppArgs (LamTerm.headBetaBounded n (.app s fn arg))).map (fun (s, arg) => (s, arg, arg.betaBounded n))
      have eq₁ : (LamTerm.getAppArgs (LamTerm.headBetaBounded n (.app s fn arg))) = masterArr.map (fun (s, arg₁, _) => (s, arg₁)) := by
        dsimp; rw [List.map_map]; rw [List.map_equiv _ id, List.map_id]
        intro x; cases x; rfl
      have eq₂ : List.map
        (fun x => (x.fst, LamTerm.betaBounded n x.snd))
        (LamTerm.getAppArgs (LamTerm.headBetaBounded n (.app s fn arg))) = masterArr.map (fun (s, _, arg₂) => (s, arg₂)) := by
        dsimp; rw [List.map_map]; apply List.map_equiv;
        intro x; cases x; rfl
      rw [eq₂]; revert wftap; rw [eq₁]; intro wftap _;
      apply LamEquiv.congrs
      case hFn => intro fnTy wfFn; apply LamEquiv.refl
      case hArgs =>
        dsimp;
        apply HList.toMapTy; dsimp [Function.comp]
        apply HList.ofMapList; intro x;
        match x with
        | (s, t) =>
          intro argTy wfArg; dsimp; apply IH

theorem LamThmEquiv.ofBetaBounded (wf : LamThmWF lval lctx rty t) :
  LamThmEquiv lval lctx rty t (t.betaBounded n) := fun lctx => ⟨wf lctx, LamEquiv.ofBetaBounded _ _⟩

partial def LamTerm.betaReduceHackyAux (t : LamTerm) : LamTerm × Nat := Id.run <| do
  let mut cur := t
  let mut n := 1
  while true do
    cur := t.betaBounded n
    if cur.betaReduced then
      return (cur, n)
    n := n * 2
  return (cur, n)

def LamTerm.betaReduceHacky (t : LamTerm) := (betaReduceHackyAux t).fst

def LamTerm.betaReduceHackyIdx (t : LamTerm) := (betaReduceHackyAux t).snd

-- #eval LamTerm.betaBounded 7 (.app (.atom 0)
--   (.lam (.atom 0) (.app (.atom 0) (.bvar 0) (.bvar 0)))
--   (.lam (.atom 0) (.app (.atom 0) (.bvar 0) (.app (.atom 0) (.bvar 0) (.bvar 0)))))

theorem LamThmEquiv.ofResolveImport
  (lval : LamValuation) (wfT : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t (t.resolveImport lval.toLamTyVal) := by
  dsimp [LamThmEquiv]; intros lctx';
  let wfT' := wfT lctx'; exists wfT'; exists (LamWF.resolveImport wfT')
  intros lctxTerm; apply LamWF.resolveImport.correct

theorem LamValid.ofLamEquiv
  (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩)
  (leq : LamEquiv t₁ t₂ wf₁) : LamValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  let ⟨wf₂, h₁₂⟩ := leq; ⟨LamWF.mkEq wf₁ wf₂, h₁₂⟩

theorem LamThmValid.ofLamThmEquiv
  (lval : LamValuation) (lctx : List LamSort)
  (eT : LamThmEquiv lval lctx s t₁ t₂) :
  LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) := fun lctx' =>
  let ⟨wf₁, leq⟩ := eT lctx'; LamValid.ofLamEquiv wf₁ leq

theorem LamEquiv.ofLamValid
  (heq : LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  ∃ (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩), LamEquiv t₁ t₂ wf :=
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq
  ⟨wft₁, ⟨wft₂, heq'⟩⟩ 

theorem LamThmEquiv.ofLamThmValid
  (lval : LamValuation) (lctx : List LamSort)
  (heq : LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamThmEquiv lval lctx s t₁ t₂ :=
  fun lctx' => LamEquiv.ofLamValid (heq lctx')

theorem LamEquiv.eqLamValid :
  (∃ (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩), LamEquiv t₁ t₂ wf) = (LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :=
  propext (Iff.intro (fun ⟨wf, h⟩ => LamValid.ofLamEquiv wf h) LamEquiv.ofLamValid)

theorem LamThmEquiv.eqLamThmValid
  (lval : LamValuation) (lctx : List LamSort) :
  LamThmEquiv lval lctx s t₁ t₂ = LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  propext (Iff.intro (LamThmValid.ofLamThmEquiv _ _) (LamThmEquiv.ofLamThmValid _ _))

theorem LamValid.mpLamEquiv (hp : LamValid lval lctx p₁)
  (hequiv : ∀ (wfp₁ : LamWF lval.toLamTyVal ⟨lctx, p₁, (.base .prop)⟩),
    LamEquiv p₁ p₂ wfp₁) : LamValid lval lctx p₂ :=
  let ⟨wfp₁, hp₁⟩ := hp
  let ⟨wfp₂, heqp⟩ := hequiv wfp₁
  ⟨wfp₂, fun lctxTerm' => heqp _ ▸ hp₁ lctxTerm'⟩

theorem LamThmValid.mpLamThmEquiv
  (lval : LamValuation) (lctx : List LamSort)
  (hequiv : LamThmEquiv lval lctx (.base .prop) p₁ p₂)
  (hp : LamThmValid lval lctx p₁) : LamThmValid lval lctx p₂ := by
  intros lctx';
  let ⟨wfp₁, ⟨wfp₂, heqp⟩⟩ := hequiv lctx'
  exists wfp₂; intro lctxTerm'; rw [← heqp]
  let ⟨wfp₁', hp₁⟩ := hp lctx'
  have wfeq : wfp₁ = wfp₁' := eq_of_heq (LamWF.unique wfp₁ wfp₁').right
  cases wfeq; apply hp₁

theorem LamEq.symm (lval : LamValuation) (lctx : List LamSort)
  (H : LamThmValid lval lctx (.mkEq s a b)) :
  LamThmValid lval lctx (.mkEq s b a) := by
  apply LamThmValid.ofLamThmEquiv
  apply LamThmEquiv.symm;
  apply LamThmEquiv.ofLamThmValid _ _ H

theorem LamEq.trans (lval : LamValuation) (lctx : List LamSort)
  (H₁ : LamThmValid lval lctx (.mkEq s a b))
  (H₂ : LamThmValid lval lctx (.mkEq s b c)) :
  LamThmValid lval lctx (.mkEq s a c) := by
  apply LamThmValid.ofLamThmEquiv
  apply LamThmEquiv.trans (b:=b)
  case e₁ => apply LamThmEquiv.ofLamThmValid _ _ H₁
  case e₂ => apply LamThmEquiv.ofLamThmValid _ _ H₂

def LamTerm.impApp? (t₁₂ t₁ : LamTerm) : Option LamTerm :=
  match t₁₂ with
  | .app _ fn concl =>
    match fn with
    | .app _ imp hyp =>
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
  | _ => .none

theorem LamTerm.maxEVarSucc_impApp?
  (heq : LamTerm.impApp? t₁₂ t₁ = .some t') : t'.maxEVarSucc ≤ t₁₂.maxEVarSucc := by
  revert t₁ t'; induction t₁₂ <;> intro t₁ t' heq <;> try cases heq
  case app s fn arg IHFn _ =>
    cases fn <;> try cases heq
    case app s' imp hyp =>
      dsimp [impApp?] at heq
      cases h : hyp.beq t₁
      case true =>
        rw [h] at heq; cases imp <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          dsimp [maxEVarSucc]; cases (LamTerm.beq_eq _ _ h)
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
              apply congrArg; apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
              exact .symm (LamTerm.beq_eq _ _ h)
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
  revert t t'; induction ps <;> intro t t' heq
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
  revert t; induction ps <;> intros t vt heq
  case nil => cases heq; exact vt
  case cons head tail IH =>
    match vps with
    | .cons vHead vTail =>
      dsimp [LamTerm.impApps?] at heq
      match hap : LamTerm.impApp? t head with
      | .some t'' =>
        rw [hap] at heq; dsimp at heq
        apply IH vTail _ heq
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
  revert s t'; induction t <;> intros s t' heq <;> try cases heq
  case app s fn arg IHFn IHArg =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s' =>
        cases arg <;> try cases heq
        case lam s'' body =>
          dsimp [maxEVarSucc]; rw [Nat.max, Nat.max_def]; simp [Nat.zero_le]

theorem LamValid.intro1F (H : LamValid lval lctx t)
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
            exists Hp; intro lctxTerm
            have vl' := vl (fun n => lctxTerm (.succ n)) (lctxTerm 0)
            dsimp [LamWF.interp, LamBaseTerm.LamWF.interp] at vl';
            apply Eq.mp _ vl'; apply congrArg;
            apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
            apply HEq.funext; intro n; cases n <;> rfl

-- First-order logic style intro1
theorem LamThmValid.intro1F (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1F? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs.cons]; apply LamValid.intro1F (H lctx') heq

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
  revert s t'; induction t <;> intros s t' heq <;> try cases heq
  case app s fn arg IHFn _ =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s' =>
        dsimp [maxEVarSucc, bvarLift, bvarLiftIdx, bvarLiftsIdx];
        rw [LamTerm.maxEVarSucc_mapBVarAt]; apply Nat.max_comm


theorem LamValid.intro1HAux (H : LamValid lval lctx (.app s' (.base (.forallE s)) t)) :
  LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  have ⟨wfl, vl⟩ := H
  match wfl with
  | .ofApp _ (.ofBase (.ofForallE _)) Hp => by
    let Hp' := LamWF.ofBVarLiftIdx (s:=s) 0 _ Hp
    let HApp := LamWF.ofApp s Hp' (.ofBVar 0)
    rw [← pushLCtxAt.zero]; exists HApp; intro lctxTerm
    dsimp [LamWF.interp]
    have vl' := vl (fun n => lctxTerm (.succ n)) (lctxTerm 0)
    apply Eq.mp _ vl'; apply congrArg; apply congrFun;
    apply Eq.trans (LamWF.ofBVarLiftIdx.correct lval (idx:=0) lctx
      (fun n => lctxTerm (Nat.succ n)) (lctxTerm 0) _ Hp) ?req
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case HLCtxTermEq =>
      apply HEq.funext; intro n; cases n <;> rfl

theorem LamValid.intro1H (H : LamValid lval lctx t)
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
theorem LamThmValid.intro1H (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1H? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs.cons]; apply LamValid.intro1H (H lctx') heq

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

theorem LamValid.intro1 (H : LamValid lval lctx t)
  (heq : LamTerm.intro1? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p := by
  dsimp [LamTerm.intro1?] at heq
  cases t <;> try cases heq
  case app _ fn p =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        dsimp at heq
        cases p <;> try apply LamValid.intro1H H heq
        apply LamValid.intro1F H heq

theorem LamThmValid.intro1 (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs.cons]; apply LamValid.intro1 (H lctx') heq

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
  (heq : t.mp? rw = .some t') : LamEquiv t t' wft := by
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
            cases (LamTerm.beq_eq _ _ h)
            have ⟨wfrw, _⟩ := Hrw
            have ⟨seq₁, seq₂, _⟩ := LamWF.mkEq_sortEq wfrw
            cases seq₁; cases seq₂
            have ⟨argwf, argh⟩ := LamEquiv.ofLamValid Hrw
            apply LamEquiv.toForall _ argh
          | false => rw [h] at heq; cases heq

theorem LamThmEquiv.mp?
  (wft : LamThmWF lval lctx rty t) (Hrw : LamThmValid lval lctx rw)
  (heq : t.mp? rw = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => ⟨wft lctx', LamEquiv.mp? (wft lctx') (Hrw lctx') heq⟩

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
  (heq : t.congrArg? rw = .some t') : LamEquiv t t' wft := by
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
              cases (LamTerm.beq_eq _ _ h)
              cases heq; cases wft;
              case ofApp s heqAp hres =>
                apply LamEquiv.congrArg
                have ⟨wfrw, _⟩ := Hrw
                have ⟨seq₁, seq₂, _⟩ := LamWF.mkEq_sortEq wfrw
                cases seq₁; cases seq₂
                have ⟨argwf, argh⟩ := LamEquiv.ofLamValid Hrw
                apply LamEquiv.toForall _ argh
            | false =>
              rw [h] at heq; cases heq

theorem LamThmEquiv.congrArg?
  (wft : LamThmWF lval lctx rty t) (Hrw : LamThmValid lval lctx rw)
  (heq : t.congrArg? rw = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => ⟨wft lctx', LamEquiv.congrArg? _ (Hrw lctx') heq⟩

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
  (heq : t.congrFun? rw = .some t') : LamEquiv t t' wft := by
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
              cases (LamTerm.beq_eq _ _ h)
              cases heq; cases wft
              case ofApp heqAp hres =>
                apply LamEquiv.congrFun
                have ⟨wfrw, _⟩ := Hrw
                have ⟨seq₁, seq₂, _⟩ := LamWF.mkEq_sortEq wfrw
                cases seq₁; cases seq₂
                have ⟨argwf, argh⟩ := LamEquiv.ofLamValid Hrw
                apply LamEquiv.toForall _ argh
            | false =>
              rw [h] at heq; cases heq

theorem LamThmEquiv.congrFun?
  (wft : LamThmWF lval lctx rty t) (Hrw : LamThmValid lval lctx rw)
  (heq : t.congrFun? rw = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => ⟨wft lctx', LamEquiv.congrFun? _ (Hrw lctx') heq⟩

def LamTerm.congr? (t : LamTerm) (rwFn : LamTerm) (rwArg : LamTerm) : Option LamTerm :=
  (t.congrFun? rwFn).bind (LamTerm.congrArg? · rwArg)

theorem LamEquiv.congr?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩)
  (HrwFn : LamValid lval lctx rwFn) (HrwArg : LamValid lval lctx rwArg)
  (heq : t.congr? rwFn rwArg = .some t') : LamEquiv t t' wft := by
  dsimp [LamTerm.congr?] at heq
  match hFn : LamTerm.congrFun? t rwFn with
  | .some t'' =>
    rw [hFn] at heq; dsimp [Option.bind] at heq
    have ⟨wfFn, eqFn⟩ := LamEquiv.congrFun? wft HrwFn hFn
    apply LamEquiv.trans _ _ wfFn ⟨wfFn, eqFn⟩
    apply LamEquiv.congrArg? _ HrwArg heq
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
  fun lctx' => ⟨wft lctx', LamEquiv.congr? _ (HrwFn lctx') (HrwArg lctx') heq⟩

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
  revert t t'; induction rwArgs <;> intro t t' ht heq
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
          apply IH hTail ht.left h
        case none =>
          rw [h] at heq; cases heq

theorem LamEquiv.congrArgs?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) (HrwArgs : HList (LamValid lval lctx) rwArgs)
  (heq : t.congrArgs? rwArgs = .some t') : LamEquiv t t' wft := by
  revert rty t t'; induction rwArgs <;> intros t rty t' wft heq
  case nil =>
    unfold LamTerm.congrArgs? at heq; cases heq; apply LamEquiv.refl
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
          have fneq := IH HrwTail wfFn h₁
          have ⟨wfap, eqap⟩ := LamEquiv.congrFun _ wfFn fneq wfArg
          apply LamEquiv.trans _ _ wfap ⟨wfap, eqap⟩
          apply LamEquiv.toForall
          apply LamEquiv.congrArg? wfap HrwHead heq
      | .none => rw [h₁] at heq; cases heq

theorem LamThmEquiv.congrArgs?
  (wft : LamThmWF lval lctx rty t) (HrwArgs : HList (LamThmValid lval lctx) rwArgs)
  (heq : t.congrArgs? rwArgs = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => ⟨wft lctx', LamEquiv.congrArgs? _ (HrwArgs.map (fun _ twf => twf lctx')) heq⟩

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
  revert t t'; induction idx <;> intro t t' ht heq
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
  (heq : t.congrFunN? rwFn n = .some t') : LamEquiv t t' wft := by
  revert rty t t'; induction n <;> intros t rty t' wft heq
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
        cases wft; apply LamEquiv.congrFun
        apply IH _ h₁
      | .none => rw [h₁] at heq; cases heq

theorem LamThmEquiv.congrFunN?
  (wft : LamThmWF lval lctx rty t) (HrwFn : LamThmValid lval lctx rwFn)
  (heq : t.congrFunN? rwFn n = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => ⟨wft lctx', LamEquiv.congrFunN? _ (HrwFn lctx') heq⟩

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
  revert t t'; induction rwArgs <;> intro t t' ht heq
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
          apply IH hTail ht.left h
        case none =>
          rw [h] at heq; cases heq

theorem LamEquiv.congrs?
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩)
  (HrwFn : LamValid lval lctx rwFn) (HrwArgs : HList (LamValid lval lctx) rwArgs)
  (heq : t.congrs? rwFn rwArgs = .some t') : LamEquiv t t' wft := by
  revert rty t t'; induction rwArgs <;> intros t rty t' wft heq
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
          have fneq := IH HrwTail wfFn h₁
          have ⟨wfap, eqap⟩ := LamEquiv.congrFun _ wfFn fneq wfArg
          apply LamEquiv.trans _ _ wfap ⟨wfap, eqap⟩
          apply LamEquiv.toForall
          apply LamEquiv.congrArg? wfap HrwHead heq
      | .none => rw [h₁] at heq; cases heq

theorem LamThmEquiv.congrs?
  (wft : LamThmWF lval lctx rty t)
  (HrwFn : LamThmValid lval lctx rwFn) (HrwArgs : HList (LamThmValid lval lctx) rwArgs)
  (heq : t.congrs? rwFn rwArgs = .some t') : LamThmEquiv lval lctx rty t t' :=
  fun lctx' => ⟨wft lctx', LamEquiv.congrs? _ (HrwFn lctx') (HrwArgs.map (fun _ twf => twf lctx')) heq⟩

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
      exists LamSort.curry valPre; apply LamThmValid.ofLamThmValidD; apply And.intro;
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

end Auto.Embedding.Lam