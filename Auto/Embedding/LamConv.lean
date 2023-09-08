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

theorem LamEquiv.congrFn (lval : LamValuation)
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn₁, .func argTy resTy⟩) (eFn : LamEquiv fn₁ fn₂ wfFn)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamEquiv (.app argTy fn₁ arg) (.app argTy fn₂ arg) (.ofApp _ wfFn wfArg) :=
  LamEquiv.congr _ _ eFn _ (LamEquiv.refl _ _)

theorem LamThmEquiv.congrFn (lval : LamValuation)
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

theorem LamEquiv.congrN (lval : LamValuation) {args : List (LamSort × LamTerm × LamTerm)}
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

theorem LamEquiv.congrFnN (lval : LamValuation) {args : List (LamSort × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ args, resTy⟩)
  (hFn : ∀ (fnTy : _) (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn₁, fnTy⟩), LamEquiv fn₁ fn₂ wfFn) :
  LamEquiv (LamTerm.mkAppN fn₁ args) (LamTerm.mkAppN fn₂ args) wfApp := by
  revert fn₁ fn₂; induction args <;> intro fn₁ fn₂ wfApp hFn
  case nil => apply hFn
  case cons head tail IH =>
    match head with
    | ⟨s, t⟩ =>
      apply IH; intro fnTy wfFn
      match wfFn with
      | .ofApp _ wfFn' wfArg' =>
        apply LamEquiv.congrFn _ _ (hFn _ _)

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we reduce the top-level redex
-- Suppose `lctx ⊢ body : ty`. It's easy to see that the `lctx` which `arg`
--   resides in is `fun n => lctx (n + idx + 1)` and the type of `arg` is `lctx idx`
def LamTerm.instantiateAt (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n        => .atom n
| .base b        => .base b
| .bvar n        => pushLCtxAt (arg.bvarLifts idx) idx LamTerm.bvar n
| .lam s body    => .lam s (LamTerm.instantiateAt (.succ idx) arg body)
| .app s fn arg' => .app s (LamTerm.instantiateAt idx arg fn) (LamTerm.instantiateAt idx arg arg')

def LamWF.instantiateAt
  (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, arg.bvarLifts idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAt argTy idx lctx, body, bodyTy⟩) →
  LamWF ltv ⟨lctx, LamTerm.instantiateAt idx arg body, bodyTy⟩
| lctx, _,     .ofAtom n => .ofAtom _
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
| .base b       => .base (b.resolveImport ltv)
| .bvar n       => .bvar n
| .lam s t      => .lam s (t.resolveImport ltv)
| .app s fn arg => .app s (fn.resolveImport ltv) (arg.resolveImport ltv)

def LamWF.resolveImport
  {ltv : LamTyVal} {t : LamTerm} {ty : LamSort}
  {lctx : Nat → LamSort} (wfT : LamWF ltv ⟨lctx, t, ty⟩) :
  LamWF ltv ⟨lctx, LamTerm.resolveImport ltv t, ty⟩ :=
  match wfT with
  | .ofAtom n => .ofAtom n
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
  | .base _  => rfl
  | .bvar _  => rfl
  | .lam _ _ =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=_) (body:=_) _ _ => LamWF.instantiate1.correct _ _ _ _ _
  | .app _ _ _ => rfl

def LamTerm.topBeta : LamTerm → LamTerm
| .app s fn arg => LamTerm.topBetaAux s arg fn
| t => t

def LamWF.topBeta
  (ltv : LamTyVal) {t : LamTerm} {ty : LamSort} (lctx : Nat → LamSort)
  (wf : LamWF ltv ⟨lctx, t, ty⟩) : LamWF ltv ⟨lctx, LamTerm.topBeta t, ty⟩ :=
  match t with
  | .atom _ => wf
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

theorem LamEquiv.ofBeta (lval : LamValuation.{u})
  (fn : LamTerm) (args : List (LamSort × LamTerm))
  (wf : LamWF lval.toLamTyVal ⟨lctx, fn.mkAppN args, resTy⟩) :
  LamEquiv _ (fn.beta args) wf :=
  match args with
  | .nil => ⟨wf, fun _ => rfl⟩
  | arg :: args =>
    match fn with
    | .atom _ => ⟨wf, fun _ => rfl⟩
    | .base _ => ⟨wf, fun _ => rfl⟩
    | .bvar _ => ⟨wf, fun _ => rfl⟩
    | .lam s' t' => by
      dsimp [LamTerm.mkAppN, LamTerm.beta]
      dsimp [LamTerm.mkAppN] at wf
      let ⟨apTy, wfAp⟩ := LamWF.getAppFn (args:=args) wf
      have hTop := LamEquiv.ofTopBeta wfAp;
      dsimp only [LamTerm.topBeta, LamTerm.topBetaAux] at hTop
      have hCongr := LamEquiv.congrFnN _ (args:=args) wf hTop.toForall
      let ⟨hCongrWF, CongrEq⟩ := hCongr
      apply LamEquiv.trans _ _ hCongrWF ⟨hCongrWF, CongrEq⟩
      apply LamEquiv.ofBeta lval _ args
    | .app _ _ _ => ⟨wf, fun _ => rfl⟩

def LamTerm.headBetaAux : List (LamSort × LamTerm) → LamTerm → LamTerm
| args, .app s fn arg => headBetaAux ((s, arg) :: args) fn
| args, t             => beta t args

theorem LamEquiv.ofHeadBetaAux (lval : LamValuation.{u})
  (wf : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN t args, rty⟩) :
  LamEquiv _ (t.headBetaAux args) wf := by
  revert args wf; induction t <;> intro args wf <;>
    try (cases args <;> apply LamEquiv.refl)
  case lam s body _ => apply LamEquiv.ofBeta
  case app s fn arg IHFn _ => dsimp [LamTerm.headBetaAux]; apply IHFn

def LamTerm.headBeta := LamTerm.headBetaAux []

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
    match t.isHeadbetaTarget with
    | true => headBetaBounded n' t.headBeta
    | false => t

theorem LamEquiv.ofHeadBetaBounded (lval : LamValuation.{u})
  (wf : LamWF lval.toLamTyVal ⟨lctx, t, rty⟩) : LamEquiv _ (t.headBetaBounded n) wf := by
  revert t; induction n <;> intro t wf
  case zero => apply LamEquiv.refl
  case succ n IH =>
    dsimp [LamTerm.headBetaBounded]
    match t.isHeadbetaTarget with
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
    | .base _ => t
    | .bvar _ => t
    | .lam s t => .lam s (t.betaBounded n')
    | .app .. =>
      let tb := t.headBetaBounded n'
      let fn := tb.getAppFn
      let args := tb.getAppArgs
      let argsb := args.map (fun ((s, arg) : LamSort × _) => (s, betaBounded n' arg))
      LamTerm.mkAppN fn argsb

def LamTerm.betaReduced (t : LamTerm) :=
  match t with
  | .atom _ => true
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
      apply LamEquiv.congrN
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

-- LamTerm.instantiate1 t' arg.snd
-- .app arg.fst (LamTerm.lam s' t') arg.snd
theorem LamThmEquiv.ofResolveImport
  (lval : LamValuation) (wfT : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t (t.resolveImport lval.toLamTyVal) := by
  dsimp [LamThmEquiv]; intros lctx';
  let wfT' := wfT lctx'; exists wfT'; exists (LamWF.resolveImport wfT')
  intros lctxTerm; apply LamWF.resolveImport.correct

theorem LamThmValid.ofLamThmEquiv
  (lval : LamValuation) (lctx : List LamSort)
  (eT : LamThmEquiv lval lctx s t₁ t₂) :
  LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) := by
  dsimp [LamThmValid]; intros lctx'
  let ⟨wfT₁, ⟨wfT₂, heq⟩⟩ := eT lctx';
  exact Exists.intro (LamWF.mkEq wfT₁ wfT₂) heq

theorem LamThmEquiv.ofLamThmValid
  (lval : LamValuation) (lctx : List LamSort)
  (heq : LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamThmEquiv lval lctx s t₁ t₂ := by
  dsimp [LamThmEquiv]; intros lctx'
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq lctx'
  exact Exists.intro wft₁ (.intro wft₂ heq')

theorem LamThmEquiv.eqLamThmValid
  (lval : LamValuation) (lctx : List LamSort) :
  LamThmEquiv lval lctx s t₁ t₂ = LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  propext (Iff.intro (LamThmValid.ofLamThmEquiv _ _) (LamThmEquiv.ofLamThmValid _ _))

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

theorem LamEq.subst (lval : LamValuation) (lctx : List LamSort)
  (hEq : LamThmValid lval lctx (.mkEq s a b))
  (hPa : LamThmValid lval lctx (.app s p a)) :
  LamThmValid lval lctx (.app s p b) := by
  apply LamThmValid.mpLamThmEquiv _ _ _ hPa
  apply LamThmEquiv.congrArg
  case wfFn =>
    intros lctx'
    let .ofApp _ Hp _ := LamThmWF.ofLamThmValid hPa lctx'
    exact Hp
  case eArg =>
    apply LamThmEquiv.ofLamThmValid _ _ hEq

theorem LamEq.congr (lval : LamValuation) (lctx : List LamSort)
  (hEq : LamThmValid lval lctx (.mkEq s' a b))
  (wfT : LamThmWF lval lctx s (.app s' f a))
  : LamThmValid lval lctx (.mkEq s (.app s' f a) (.app s' f b)) := by
  apply LamThmValid.ofLamThmEquiv
  apply LamThmEquiv.congrArg
  case wfFn =>
    intros lctx'
    let .ofApp _ Hf _ := wfT lctx'
    exact Hf
  case eArg => exact LamThmEquiv.ofLamThmValid _ _ hEq

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

end Auto.Embedding.Lam