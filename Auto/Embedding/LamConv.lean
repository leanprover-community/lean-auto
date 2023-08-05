import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (Nat.succ ?n)`
def LamTerm.bvarLiftIdx (idx : Nat) : LamTerm → LamTerm
| .atom n     => .atom n
| .base b     => .base b
| .bvar n     => .bvar (popLCtxAt id idx n)
| .lam s t    => .lam s (t.bvarLiftIdx (Nat.succ idx))
| .app fn arg => .app (fn.bvarLiftIdx idx) (arg.bvarLiftIdx idx)

def LamTerm.bvarLift : LamTerm → LamTerm := LamTerm.bvarLiftIdx 0

def LamTerm.bvarLifts (t : LamTerm) : (lvl : Nat) → LamTerm
| 0 => t
| lvl' + 1 => (t.bvarLifts lvl').bvarLift

def LamTerm.bvarLifts_cast₁ {lvl : Nat} {rterm : LamTerm} (f : LamTerm → Sort u)
  (H : f (LamTerm.bvarLifts (LamTerm.bvarLift rterm) lvl)) :
  f (LamTerm.bvarLifts rterm (Nat.succ lvl)) :=
  match lvl with
  | 0 => H
  | lvl' + 1 => LamTerm.bvarLifts_cast₁ (rterm:=rterm) (f := fun t => f (t.bvarLift)) H

def LamTerm.bvarLifts_cast₂ {lvl : Nat} {rterm : LamTerm} (f : LamTerm → Sort u)
  (H : f (LamTerm.bvarLifts rterm (Nat.succ lvl))) :
  f (LamTerm.bvarLifts (LamTerm.bvarLift rterm) lvl) :=
  match lvl with
  | 0 => H
  | lvl' + 1 => LamTerm.bvarLifts_cast₂ (rterm:=rterm) (f := fun t => f (t.bvarLift)) H

def LamWF.ofBVarLiftIdx {lamVarTy lctx} (idx : Nat) (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨popLCtxAt lctx idx, rterm, rTy⟩) →
  LamWF lamVarTy ⟨lctx, rterm.bvarLiftIdx idx, rTy⟩
| .ofAtom n => .ofAtom n
| .ofBase b => .ofBase b
| .ofBVar n =>
  let H := @LamWF.ofBVar lamVarTy lctx (popLCtxAt id idx n)
  let castHg := fun i => LamWF lamVarTy ⟨lctx, LamTerm.bvar (popLCtxAt id idx n), i⟩
  popLCtxAt.comm_cast₁ id lctx castHg idx n H
| .ofLam (argTy:=argTy) (body:=body) bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (body:=body.bvarLiftIdx (Nat.succ idx))
    (LamWF.ofBVarLiftIdx (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.ofBVarLiftIdx idx _ HFn
  let IHArg := LamWF.ofBVarLiftIdx idx _ HArg
  .ofApp argTy' IHFn IHArg

def LamWF.ofBVarLift {lamVarTy lctx} (rterm : LamTerm) 
  (HWF : LamWF lamVarTy ⟨popLCtx lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm.bvarLift, rTy⟩ :=
  LamWF.ofBVarLiftIdx 0 rterm HWF

def LamWF.ofBVarLifts {lamVarTy lctx} (rterm : LamTerm) (lvl : Nat)
  (HWF : LamWF lamVarTy ⟨popLCtxs lctx lvl, rterm, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm.bvarLifts lvl, rTy⟩ :=
  match lvl with
  | 0 => HWF
  | lvl' + 1 =>
    let HWF' := LamWF.ofBVarLift rterm HWF
    let IH := LamWF.ofBVarLifts (LamTerm.bvarLift rterm) lvl' HWF'
    let castIH := fun t => LamWF lamVarTy ⟨lctx, t, rTy⟩
    LamTerm.bvarLifts_cast₁ castIH IH

def LamWF.fromBVarLiftIdx {lamVarTy} (idx : Nat) : {rTy : LamSort} →
  (rterm : LamTerm) → (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLiftIdx idx, rTy⟩) →
  LamWF lamVarTy ⟨popLCtxAt lctx idx, rterm, rTy⟩
| _, .atom n, .ofAtom _ => .ofAtom n
| _, .base _, .ofBase H => .ofBase H
| _, .bvar n, .ofBVar _ =>
  let H := @LamWF.ofBVar lamVarTy (popLCtxAt lctx idx) n
  let castHg := fun i => LamWF lamVarTy ⟨popLCtxAt lctx idx, LamTerm.bvar n, i⟩
  popLCtxAt.comm_cast₂ id lctx castHg idx n H
| _, .lam argTy body, .ofLam bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (LamWF.fromBVarLiftIdx (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| _, .app fn arg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.fromBVarLiftIdx idx _ HFn
  let IHArg := LamWF.fromBVarLiftIdx idx _ HArg
  .ofApp argTy' IHFn IHArg

def LamWF.fromBVarLift {lamVarTy} {rty : LamSort}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLift, rty⟩) :
  LamWF lamVarTy ⟨popLCtx lctx, rterm, rty⟩ :=
  LamWF.fromBVarLiftIdx 0 rterm HWF

def LamWF.fromBVarLifts {lamVarTy lctx} (rterm : LamTerm) (lvl : Nat)
  (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLifts lvl, argTy⟩) :
  LamWF lamVarTy ⟨popLCtxs lctx lvl, rterm, argTy⟩ :=
  match lvl with
  | 0 => HWF
  | lvl' + 1 =>
    let HWF' := LamWF.fromBVarLift (LamTerm.bvarLifts rterm lvl') HWF
    let IH := LamWF.fromBVarLifts _ _ HWF'
    let castIH := fun f =>
      LamWF lamVarTy ⟨f, rterm, argTy⟩
    popLCtx.succ_cast₁ _ castIH _ IH

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we beta-reduce the whole term
-- `bj` is the judgement related to the body, i.e. `lctx ⊢ body : ty`. It's
--   easy to see that the `lctx` which `arg` resides in is `popLCtxs lctx (idx + 1)`
--   and the type of `arg` is `lctx idx`
def LamWF.subst (ltv : LamTyVal) (idx : Nat)
  (arg : LamTerm) (argTy : LamSort)
  (body : LamTerm) (bodyTy : LamSort) :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) →
  (substed : LamTerm) × LamWF ltv ⟨lctx, substed, bodyTy⟩
| lctx, _,     .ofAtom n => ⟨.atom n, .ofAtom _⟩
| lctx, _,     .ofBase (b:=b) H => ⟨.base b, .ofBase H⟩
| lctx, wfArg, .ofBVar n =>
  let lctxty := fun rty => (substed : LamTerm) × LamWF ltv { lctx := lctx, rterm := substed, rty := rty}
  let arg' := LamTerm.bvarLifts arg idx
  pushLCtxAtDep (rty:=lctx) (lctxty:=lctxty) (lctx := fun n => ⟨.bvar n, .ofBVar n⟩) (xty:=argTy) (x := ⟨arg', wfArg⟩) idx n
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLift (lctx:=pushLCtx lctx argTy') _ wfArg
  let IHArg := LamWF.subst ltv (Nat.succ idx) _ _ _ _ _ wfArg' H
  ⟨.lam argTy' IHArg.fst, .ofLam _ IHArg.snd⟩
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.subst ltv idx _ _ _ _ _ wfArg HFn
  let IHArg := LamWF.subst ltv idx _ _ _ _ _ wfArg HArg
  ⟨.app IHFn.fst IHArg.fst, .ofApp argTy' IHFn.snd IHArg.snd⟩

def LamWF.subst_correct.{u} (lval : LamValuation.{u})
  (arg : LamTerm) (argTy : LamSort)
  (body : LamTerm) (bodyTy : LamSort) (idx : Nat) :
  (lctxTy : Nat → LamSort) →
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts arg idx, argTy⟩) →
  (wfBody : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAt lctxTy argTy idx, body, bodyTy⟩) →
  let wfSubst := LamWF.subst lval.ilVal.toLamTyVal idx arg argTy body bodyTy lctxTy wfArg wfBody
  (LamTerm.interp lval (pushLCtxAt lctxTy argTy idx)
    (pushLCtxAtDep lctxTerm (LamTerm.interp lval lctxTy lctxTerm wfArg) idx) wfBody
  = LamTerm.interp lval lctxTy lctxTerm wfSubst.snd)
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBase b => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n =>
  let β := LamSort.interp lval.ilVal.tyVal
  let lctxty := fun (rty : LamSort) => (t : LamTerm) × LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩
  let f := fun (rty : LamSort) (r : lctxty rty) => LamTerm.interp lval lctxTy lctxTerm r.snd
  let lctx := fun n => (⟨LamTerm.bvar n, .ofBVar n⟩ : @Sigma LamTerm
    (fun substed => LamWF lval.ilVal.toLamTyVal ⟨lctxTy, substed, lctxTy n⟩))
  Eq.symm (pushLCtxAtDep.comm (β:=β) (lctxty:=lctxty) f lctx ⟨_, wfArg⟩ _ _)
| lctxTy, lctxTerm, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H => by
  simp [subst, LamTerm.interp]; sorry
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  sorry

end Auto.Embedding.Lam