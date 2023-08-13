import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we beta-reduce the whole term
-- `bj` is the judgement related to the body, i.e. `lctx ⊢ body : ty`. It's
--   easy to see that the `lctx` which `arg` resides in is `fun n => lctx (n + idx + 1)`
--   and the type of `arg` is `lctx idx`
def LamTerm.subst (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n      => .atom n
| .base b      => .base b
| .bvar n      => pushLCtxAt (arg.bvarLifts idx) idx LamTerm.bvar n
| .lam s body  => .lam s (LamTerm.subst (.succ idx) arg body)
| .app fn arg' => .app (LamTerm.subst idx arg fn) (LamTerm.subst idx arg arg')

private def LamWF.subst
  (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, arg.bvarLifts idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAt argTy idx lctx, body, bodyTy⟩) →
  LamWF ltv ⟨lctx, LamTerm.subst idx arg body, bodyTy⟩
| lctx, _,     .ofAtom n => .ofAtom _
| lctx, _,     .ofBase (b:=b) H => .ofBase H
| lctx, wfArg, .ofBVar n => by
  dsimp [LamTerm.subst, pushLCtxAt, restoreAt, pushLCtx]
  match Nat.ble idx n with
  | true =>
    dsimp;
    match (n - idx) with
    | 0 => exact wfArg
    | _ + 1 => exact .ofBVar _
  | false => exact .ofBVar n
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLiftIdx (s:=argTy') (lctx:=lctx) 0 _ wfArg
  let IHArg := LamWF.subst ltv (Nat.succ idx) _
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
  let IHFn := LamWF.subst ltv idx _ wfArg HFn
  let IHArg := LamWF.subst ltv idx _ wfArg HArg
  .ofApp argTy' IHFn IHArg

private def LamWF.subst.correct.{u}
  (lval : LamValuation.{u}) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort} :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts idx arg, argTy⟩) →
  (wfBody : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAt argTy idx lctxTy, body, bodyTy⟩) →
  let wfSubst' := LamWF.subst lval.ilVal.toLamTyVal idx lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtxAt argTy idx lctxTy)
    (pushLCtxAtDep (LamWF.interp lval lctxTy lctxTerm wfArg) idx lctxTerm) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfSubst')
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBase b => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n => by
  dsimp [LamWF.interp, LamWF.subst, LamTerm.subst]
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
    let IH := LamWF.subst.correct lval (.succ idx) (pushLCtx argTy' lctxTy) (pushLCtxDep x lctxTerm) wfArg' H
    apply Eq.trans _ (Eq.trans IH _)
    case _ =>
      dsimp [interp]; apply eq_of_heq; apply interp.heq <;> try rfl
      case h.HLCtxTyEq => apply pushLCtx_pushLCtxAt
      case h.HLCtxTermEq =>
        apply HEq.trans (pushLCtxDep_pushLCtxAtDep _ _ _ _)
        apply heq_of_eq
        apply congr_arg (f := fun x => pushLCtxAtDep x _ _)
        rw [LamWF.ofBVarLiftIdx.correct (idx:=0) lval _ lctxTerm x _ wfArg]
        apply eq_of_heq; apply interp.heq
        case h.h.HLCtxTyEq => rw [pushLCtxAt.zero]
        case h.h.HLCtxTermEq => apply pushLCtxAtDep.zero
        case h.h.HTeq => rw [← LamTerm.bvarLiftsIdx.succ_r]
    case _ =>
      dsimp [interp]; apply eq_of_heq; apply interp.heq <;> rfl)
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.subst.correct lval idx lctxTy lctxTerm wfArg HFn
  let IHArg := LamWF.subst.correct lval idx lctxTy lctxTerm wfArg HArg
  by dsimp [LamWF.interp]; dsimp at IHFn; dsimp at IHArg; simp [IHFn, IHArg]


-- Note: `LamTerm.subst`, `LamWF.subst` and `LamWF.subst_correct` is the main API
--   of syntactic operations on `λ` terms

def LamTerm.headBetaAux (arg : LamTerm) : (fn : LamTerm) → LamTerm
| .lam _ body => LamTerm.subst 0 arg body
| t           => .app t arg

def LamWF.headBetaAux (ltv : LamTyVal)
  {arg : LamTerm} {argTy : LamSort} {fn : LamTerm} {resTy : LamSort}
  (lctx : Nat → LamSort) (wfArg : LamWF ltv ⟨lctx, arg, argTy⟩) 
  (wfFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩) :
  LamWF ltv ⟨lctx, LamTerm.headBetaAux arg fn, resTy⟩ :=
  match fn with
  | .atom _  => .ofApp _ wfFn wfArg
  | .base _  => .ofApp _ wfFn wfArg
  | .bvar _  => .ofApp _ wfFn wfArg
  | .lam _ body =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=argTy') (body:=body') bodyTy' wfBody =>
      LamWF.subst ltv 0 lctx (argTy:=argTy')
        (by dsimp [LamTerm.bvarLifts];
            rw [LamTerm.bvarLiftsIdx.zero 0 arg];
            exact wfArg)
        (by rw [pushLCtxAt.zero]; exact wfBody)
  | .app _ _ => .ofApp _ wfFn wfArg

def LamWF.headBetaAux.correct.{u} (lval : LamValuation.{u})
  {arg : LamTerm} {argTy : LamSort} {fn : LamTerm} {resTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, arg, argTy⟩)
  (wfFn : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, fn, .func argTy resTy⟩) :
  let wfHB := LamWF.headBetaAux lval.ilVal.toLamTyVal lctxTy wfArg wfFn
  (LamWF.interp lval lctxTy lctxTerm (.ofApp _ wfFn wfArg)
  = LamWF.interp lval lctxTy lctxTerm wfHB) :=
  match fn with
  | .atom _  => rfl
  | .base _  => rfl
  | .bvar _  => rfl
  | .lam s body =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=_) (body:=_) _ wfBody => by
      dsimp [headBetaAux, LamWF.interp]
      let b := LamWF.interp lval
        (pushLCtxAt s 0 lctxTy)
        (pushLCtxAtDep (LamWF.interp lval lctxTy lctxTerm wfArg) 0 lctxTerm)
        (by rw [pushLCtxAt.zero]; exact wfBody)
      apply Eq.trans (b:=b)
      case h₁ =>
        apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
        rw [pushLCtxAt.zero]; apply HEq.symm; apply pushLCtxAtDep.zero
      case h₂ =>
        dsimp
        rw [← LamWF.subst.correct]
        apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
        apply heq_of_eq; apply congr_arg (f := fun x => pushLCtxAtDep x 0 lctxTerm);
        apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
        dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx.zero 0 arg]
  | .app _ _ => rfl

def LamTerm.headBeta : LamTerm → LamTerm
| .app fn arg => LamTerm.headBetaAux arg fn
| t => t

def LamWF.headBeta
  (ltv : LamTyVal) {t : LamTerm} {ts : LamSort} (lctx : Nat → LamSort)
  (wf : LamWF ltv ⟨lctx, t, ts⟩) : LamWF ltv ⟨lctx, LamTerm.headBeta t, ts⟩ :=
  match t with
  | .atom _ => wf
  | .base _ => wf
  | .bvar _ => wf
  | .lam .. => wf
  | .app .. =>
    match wf with
    | .ofApp _ wfFn wfArg => LamWF.headBetaAux ltv lctx wfArg wfFn

def LamWF.headBeta.correct
  (lval : LamValuation.{u}) {t : LamTerm} {ty : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  (wfT : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, ty⟩) :
  let wfHB := LamWF.headBeta lval.ilVal.toLamTyVal lctxTy wfT
  LamWF.interp lval lctxTy lctxTerm wfT = LamWF.interp lval lctxTy lctxTerm wfHB :=
  match t with
  | .atom _ => rfl
  | .base _ => rfl
  | .bvar _ => rfl
  | .lam .. => rfl
  | .app .. =>
    match wfT with
    | .ofApp _ wfFn wfArg => LamWF.headBetaAux.correct lval lctxTy lctxTerm wfArg wfFn

end Auto.Embedding.Lam