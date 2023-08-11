import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (Nat.succ ?n)`
def LamTerm.bvarLiftIdx (idx : Nat) : LamTerm → LamTerm
| .atom n     => .atom n
| .base b     => .base b
| .bvar n     => .bvar (popLCtxAtRec id idx n)
| .lam s t    => .lam s (t.bvarLiftIdx (Nat.succ idx))
| .app fn arg => .app (fn.bvarLiftIdx idx) (arg.bvarLiftIdx idx)

def LamTerm.bvarLiftRec : LamTerm → LamTerm := LamTerm.bvarLiftIdx 0

private def LamTerm.bvarLiftsIdxRec (idx : Nat) (t : LamTerm) : (lvl : Nat) → LamTerm
| 0 => t
| lvl' + 1 => (t.bvarLiftsIdxRec idx lvl').bvarLiftIdx idx

private def LamTerm.bvarLiftsRec := LamTerm.bvarLiftsIdxRec 0

private def LamWF.ofBVarLiftIdxRec_bvarAux
  (lctx : Nat → α) (pos n : Nat) :
  pushLCtxAtRec lctx x pos (popLCtxAtRec id pos n) = lctx n := by
  rw [popLCtxAtRec.comm id (pushLCtxAtRec lctx x pos)]; dsimp
  rw [popAtRec_pushAtRec_eq]

private def LamWF.ofBVarLiftIdxRec {lamVarTy lctx} (idx : Nat) (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) →
  LamWF lamVarTy ⟨pushLCtxAtRec lctx x idx, rterm.bvarLiftIdx idx, rTy⟩
| .ofAtom n => .ofAtom n
| .ofBase b => .ofBase b
| .ofBVar n => 
  let IH := @LamWF.ofBVar lamVarTy (pushLCtxAtRec lctx x idx) (popLCtxAtRec id idx n)
  LamWF.ofBVarLiftIdxRec_bvarAux lctx idx _ ▸ IH
| .ofLam (argTy:=argTy) (body:=body) bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (body:=body.bvarLiftIdx (Nat.succ idx))
    (LamWF.ofBVarLiftIdxRec (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.ofBVarLiftIdxRec idx _ HFn
  let IHArg := LamWF.ofBVarLiftIdxRec idx _ HArg
  .ofApp argTy' IHFn IHArg

private def LamWF.ofBVarLiftRec {lamVarTy lctx} (rterm : LamTerm) 
  (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtx lctx x, rterm.bvarLiftRec, rTy⟩ :=
  LamWF.ofBVarLiftIdxRec 0 rterm HWF

private def LamWF.bvarLiftIdxRec.correct_bvarAux {rty : Nat → α}
  {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n))
  {xty : α} (x : lctxty xty) (pos n : Nat) :
  HEq (pushLCtxAtDepRec lctx x pos (popLCtxAtRec id pos n)) (lctx n) := by
  rw [popLCtxAtRec.commDep id (pushLCtxAtDepRec lctx x pos)]; simp
  apply HEq.trans
    (b := @popLCtxAtDepRec _ (pushLCtxAtRec rty xty pos) lctxty (fun n => pushLCtxAtDepRec lctx x pos n) pos n)
  case h₁ => apply HEq.symm; apply @popLCtxAtDepRec.absorbAux'
  case h₂ => apply popAtDepRec_pushAtDepRec_eq

private def LamWF.bvarLiftIdxRec.correct.{u}
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort) (idx : Nat)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.ilVal.tyVal xty) :
  (rterm : LamTerm) → (HWF : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, rterm, rTy⟩) →
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxAtRec lctxTy xty idx) (pushLCtxAtDepRec lctxTerm x idx)
    (ofBVarLiftIdxRec idx rterm HWF)
| .atom n, .ofAtom _ => rfl
| .base _, .ofBase _ => rfl
| .bvar n, .ofBVar _ => by
  dsimp [LamWF.interp, ofBVarLiftIdxRec];
  apply eq_of_heq
  apply HEq.trans (b:=LamWF.interp lval
    (pushLCtxAtRec lctxTy xty idx) (pushLCtxAtDepRec lctxTerm x idx)
    (ofBVar (popLCtxAtRec id idx n)))
  case h.h₁ =>
    dsimp [LamWF.interp]
    apply HEq.symm; apply LamWF.bvarLiftIdxRec.correct_bvarAux
  case h.h₂ =>
    apply LamWF.interp.heq <;> try rfl
| .lam argTy body, .ofLam bodyTy wfBody => funext (fun x' => LamWF.bvarLiftIdxRec.correct
    lval (pushLCtx lctxTy argTy) (Nat.succ idx)
    (pushLCtxDep lctxTerm x') x body wfBody)
| .app fn arg, .ofApp argTy HFn HArg => by
  dsimp [LamWF.interp]
  let IHFn := LamWF.bvarLiftIdxRec.correct lval lctxTy idx lctxTerm x fn HFn
  let IHArg := LamWF.bvarLiftIdxRec.correct lval lctxTy idx lctxTerm x arg HArg
  rw [IHFn]; rw [IHArg]

def LamWF.bvarLiftRec.correct.{u}
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.ilVal.tyVal xty) :
  (rterm : LamTerm) → (HWF : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, rterm, rTy⟩) →
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtx lctxTy xty) (pushLCtxDep lctxTerm x)
    (ofBVarLiftRec rterm HWF) :=
  LamWF.bvarLiftIdxRec.correct lval lctxTy 0 lctxTerm x

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we beta-reduce the whole term
-- `bj` is the judgement related to the body, i.e. `lctx ⊢ body : ty`. It's
--   easy to see that the `lctx` which `arg` resides in is `fun n => lctx (n + idx + 1)`
--   and the type of `arg` is `lctx idx`
private def LamWF.subst' (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩) →
  (substed : LamTerm) × LamWF ltv ⟨lctx, substed, bodyTy⟩
| lctx, _,     .ofAtom n => ⟨.atom n, .ofAtom _⟩
| lctx, _,     .ofBase (b:=b) H => ⟨.base b, .ofBase H⟩
| lctx, wfArg, .ofBVar n =>
  let lctxty := fun rty => (substed : LamTerm) × LamWF ltv { lctx := lctx, rterm := substed, rty := rty}
  let arg' := LamTerm.bvarLiftsRec arg idx
  pushLCtxAtDepRec (rty:=lctx) (lctxty:=lctxty) (lctx := fun n => ⟨.bvar n, .ofBVar n⟩) (xty:=argTy) (x := ⟨arg', wfArg⟩) idx n
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLiftRec (lctx:=lctx) _ wfArg
  let IHArg := LamWF.subst' ltv (Nat.succ idx) _ wfArg' H
  ⟨.lam argTy' IHArg.fst, .ofLam _ IHArg.snd⟩
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.subst' ltv idx _ wfArg HFn
  let IHArg := LamWF.subst' ltv idx _ wfArg HArg
  ⟨.app IHFn.fst IHArg.fst, .ofApp argTy' IHFn.snd IHArg.snd⟩

private def LamWF.subst'.correct.{u}
  (lval : LamValuation.{u}) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort} :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLiftsRec arg idx, argTy⟩) →
  (wfBody : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAtRec lctxTy argTy idx, body, bodyTy⟩) →
  let wfSubst' := LamWF.subst' lval.ilVal.toLamTyVal idx lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtxAtRec lctxTy argTy idx)
    (pushLCtxAtDepRec lctxTerm (LamWF.interp lval lctxTy lctxTerm wfArg) idx) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfSubst'.snd)
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBase b => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n =>
  let β := LamSort.interp lval.ilVal.tyVal
  let lctxty := fun (rty : LamSort) => (t : LamTerm) × LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩
  let f := fun (rty : LamSort) (r : lctxty rty) => LamWF.interp lval lctxTy lctxTerm r.snd
  let lctx := fun n => (⟨LamTerm.bvar n, .ofBVar n⟩ : @Sigma LamTerm
    (fun substed => LamWF lval.ilVal.toLamTyVal ⟨lctxTy, substed, lctxTy n⟩))
  Eq.symm (pushLCtxAtDepRec.comm (β:=β) (lctxty:=lctxty) f lctx ⟨_, wfArg⟩ _ _)
| lctxTy, lctxTerm, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  funext (fun x =>
    let wfArg' := LamWF.ofBVarLiftRec (lctx:=lctxTy) _ wfArg
    let IH := LamWF.subst'.correct lval (.succ idx) (pushLCtx lctxTy argTy') (pushLCtxDep lctxTerm x) wfArg' H
    Eq.trans (by
      dsimp [LamWF.interp]
      rw [← LamWF.bvarLiftRec.correct]
      rfl) IH)
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.subst'.correct lval idx lctxTy lctxTerm wfArg HFn
  let IHArg := LamWF.subst'.correct lval idx lctxTy lctxTerm wfArg HArg
  by dsimp [LamWF.interp]; dsimp at IHFn; dsimp at IHArg; simp [IHFn, IHArg]

def LamTerm.bvarLiftsIdx (idx : Nat) (t : LamTerm) (lvl : Nat) : LamTerm :=
  match t with
  | .atom n     => .atom n
  | .base b     => .base b
  | .bvar n     => .bvar (popLCtxsAt id lvl idx n)
  | .lam s t    => .lam s (t.bvarLiftsIdx (.succ idx) lvl)
  | .app fn arg => .app (fn.bvarLiftsIdx idx lvl) (arg.bvarLiftsIdx idx lvl)

def LamTerm.bvarLiftsIdx.zero (idx : Nat) : (t : LamTerm) → LamTerm.bvarLiftsIdx idx t 0 = t
| .atom n => rfl
| .base b => rfl
| .bvar n => by
  dsimp [bvarLiftsIdx, popLCtxsAt]
  match Nat.ble idx n with
  | true => rfl
  | false => rfl
| .lam s t => by
  dsimp [bvarLiftsIdx];
  rw [LamTerm.bvarLiftsIdx.zero (.succ idx) t]
| .app fn arg => by
  dsimp [bvarLiftsIdx];
  rw [LamTerm.bvarLiftsIdx.zero _ fn];
  rw [LamTerm.bvarLiftsIdx.zero _ arg];

def LamTerm.bvarLiftsIdx.succ (idx : Nat) (t : LamTerm) (lvl : Nat) :
  LamTerm.bvarLiftsIdx idx t (.succ lvl) = LamTerm.bvarLiftIdx idx (LamTerm.bvarLiftsIdx idx t lvl) := by
  revert idx lvl
  induction t <;> intros idx lvl
  case atom a => rfl
  case base b => rfl
  case bvar n =>
    dsimp [bvarLiftsIdx, bvarLiftIdx];
    rw [popLCtxsAt.succ_l, popLCtxAt.equiv]
    rw [popLCtxsAt.comm (popLCtxAt id idx)]; rfl
  case lam s t IH =>
    dsimp [bvarLiftsIdx]
    rw [IH]; rfl
  case app fn arg IHFn IHArg =>
    dsimp [bvarLiftsIdx]
    rw [IHFn, IHArg]; rfl  

private def LamTerm.bvarLiftsIdx.equiv (idx : Nat) (t : LamTerm) (lvl : Nat) :
  LamTerm.bvarLiftsIdxRec idx t lvl = LamTerm.bvarLiftsIdx idx t lvl := by
  revert idx; revert t; induction lvl <;> intro t
  case zero => dsimp [bvarLiftsIdxRec]; intro idx; rw [LamTerm.bvarLiftsIdx.zero]
  case succ lvl' IHlvl =>
    induction t <;> intro idx
    case atom n =>
      dsimp [bvarLiftsIdxRec, bvarLiftsIdx]
      rw [IHlvl]; rfl
    case base b =>
      dsimp [bvarLiftsIdxRec, bvarLiftsIdx]
      rw [IHlvl]; rfl
    case bvar n =>
      dsimp [bvarLiftsIdxRec, bvarLiftsIdx]; rw [IHlvl];
      dsimp [bvarLiftsIdx, bvarLiftIdx]; apply congr_arg LamTerm.bvar
      rw [popLCtxAt.equiv]; rw [popLCtxsAt.comm (popLCtxAt id idx)]; dsimp
      apply Eq.symm; apply popLCtxsAt.succ_l
    case lam s t IH =>
      dsimp [bvarLiftsIdx, bvarLiftsIdxRec];
      rw [IHlvl]; dsimp [bvarLiftsIdx, bvarLiftIdx, bvarLiftsIdx]; rw [← IHlvl];
      dsimp [bvarLiftsIdxRec] at IH; rw [IH]
    case app fn arg IHFn IHArg =>
      simp [bvarLiftsIdxRec, bvarLiftsIdx];
      rw [IHlvl]; dsimp [bvarLiftsIdx, bvarLiftIdx];
      rw [← IHlvl fn]; rw [← IHlvl arg];
      dsimp [bvarLiftsIdxRec] at IHFn; rw [IHFn]
      dsimp [bvarLiftsIdxRec] at IHArg; rw [IHArg]

def LamTerm.bvarLifts (t : LamTerm) (lvl : Nat) := LamTerm.bvarLiftsIdx 0 t lvl 

def LamTerm.bvarLifts.zero (t : LamTerm) : LamTerm.bvarLifts t 0 = t :=
  LamTerm.bvarLiftsIdx.zero 0 t

def LamTerm.bvarLifts.succ (t : LamTerm) (lvl : Nat) :
  LamTerm.bvarLifts t (.succ lvl) = LamTerm.bvarLiftRec (LamTerm.bvarLifts t lvl) :=
  LamTerm.bvarLiftsIdx.succ _ _ _

private def LamTerm.bvarLifts.equiv (t : LamTerm) (lvl : Nat) :
  LamTerm.bvarLiftsRec t lvl = LamTerm.bvarLifts t lvl :=
  LamTerm.bvarLiftsIdx.equiv 0 t lvl

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we beta-reduce the whole term
-- `bj` is the judgement related to the body, i.e. `lctx ⊢ body : ty`. It's
--   easy to see that the `lctx` which `arg` resides in is `fun n => lctx (n + idx + 1)`
--   and the type of `arg` is `lctx idx`
def LamTerm.subst (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n      => .atom n
| .base b      => .base b
| .bvar n      => pushLCtxAt LamTerm.bvar (arg.bvarLifts idx) idx n
| .lam s body  => .lam s (LamTerm.subst (.succ idx) arg body)
| .app fn arg' => .app (LamTerm.subst idx arg fn) (LamTerm.subst idx arg arg')

private def LamTerm.subst.equiv (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort}
  (lctx : Nat → LamSort) :
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩) →
  LamTerm.subst idx arg body = (LamWF.subst' ltv idx lctx wfArg wfBody).fst
| wfArg, .ofAtom n => rfl
| _,     .ofBase (b:=b) H => rfl
| wfArg, .ofBVar n => by
  dsimp [LamTerm.subst, LamWF.subst']
  let f := fun (x : LamSort) (t : (substed : LamTerm) × LamWF ltv ⟨lctx, substed, x⟩) => t.fst
  let β₀ := fun ty substed => LamWF ltv ⟨lctx, substed, ty⟩
  let lctx' := fun n => @Sigma.mk LamTerm (β₀ _) (LamTerm.bvar n) (@LamWF.ofBVar ltv lctx n)
  let x := @Sigma.mk LamTerm (β₀ _) (bvarLiftsRec arg idx) wfArg
  let GEq := @pushLCtxAtDepRec.comm _ _ lctx _ f lctx' _ x idx n
  simp at GEq; rw [GEq]; rw [pushLCtxAtDepRec.nonDep]
  rw [pushLCtxAt.equiv]; rw [LamTerm.bvarLifts.equiv]
| wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H => by
  dsimp [LamTerm.subst, LamWF.subst'];
  rw [← @LamTerm.subst.equiv ltv (.succ idx) arg argTy body' bodyTy']
| wfArg, .ofApp argTy' HFn HArg => by
  dsimp [LamTerm.subst, LamWF.subst']
  rw [← LamTerm.subst.equiv ltv idx lctx wfArg HFn]
  rw [← LamTerm.subst.equiv ltv idx lctx wfArg HArg]

def LamWF.ofBVarLift {lamVarTy lctx} (rterm : LamTerm) 
  (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtx lctx x, rterm.bvarLifts 1, rTy⟩ := by
  rw [← LamTerm.bvarLifts.equiv]; apply LamWF.ofBVarLiftRec _ HWF

def LamWF.subst (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort}
  (lctx : Nat → LamSort)
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩)
  (wfBody : LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) :
  LamWF ltv ⟨lctx, LamTerm.subst idx arg body, bodyTy⟩ :=
  let wfArg' : LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩ := (LamTerm.bvarLifts.equiv arg idx) ▸ wfArg
  let wfBody' : LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩ := pushLCtxAt.equivFn lctx argTy idx ▸ wfBody
  (Eq.symm (LamTerm.subst.equiv ltv idx lctx wfArg' wfBody')) ▸ (LamWF.subst' ltv idx lctx wfArg' wfBody').snd

private def LamWF.subst.equiv (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort}
  (lctx : Nat → LamSort)
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩)
  (wfBody : LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) :
  let wfArg' : LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩ := (LamTerm.bvarLifts.equiv arg idx) ▸ wfArg
  let wfBody' : LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩ := pushLCtxAt.equivFn lctx argTy idx ▸ wfBody
  HEq (LamWF.subst' ltv idx lctx wfArg' wfBody').snd (LamWF.subst ltv idx lctx wfArg wfBody) :=
    let wfArg' : LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩ := (LamTerm.bvarLifts.equiv arg idx) ▸ wfArg
    let wfBody' : LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩ := pushLCtxAt.equivFn lctx argTy idx ▸ wfBody
    heq_of_eqRec_eq'
      (motive:=fun x => LamWF ltv ⟨lctx, x, bodyTy⟩)
      (Eq.symm (LamTerm.subst.equiv ltv idx lctx wfArg' wfBody'))
      _

def LamWF.subst.correct.{u}
  (lval : LamValuation.{u}) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts arg idx, argTy⟩)
  (wfBody : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAt lctxTy argTy idx, body, bodyTy⟩) :
  let wfSubst := LamWF.subst lval.ilVal.toLamTyVal idx lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtxAt lctxTy argTy idx)
    (pushLCtxAtDep lctxTerm (LamWF.interp lval lctxTy lctxTerm wfArg) idx) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfSubst) :=
  let wfArg' : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLiftsRec arg idx, argTy⟩ := (LamTerm.bvarLifts.equiv arg idx) ▸ wfArg
  let wfBody' : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAtRec lctxTy argTy idx, body, bodyTy⟩ := pushLCtxAt.equivFn lctxTy argTy idx ▸ wfBody
  eq_of_heq (
    let bArg := LamWF.subst' lval.ilVal.toLamTyVal idx lctxTy wfArg' wfBody'
    HEq.trans (b := LamWF.interp lval lctxTy lctxTerm bArg.snd) (
      Eq.symm (LamWF.subst'.correct _ _ _ _ wfArg' wfBody') ▸ (
        LamWF.interp.heq _
          (Eq.symm (pushLCtxAt.equivFn _ _ _))
          (let HEquiv := pushLCtxAtDep.equivFn lctxTerm (LamWF.interp lval lctxTy lctxTerm wfArg) idx
           HEq.trans (HEq.symm HEquiv) (
            congr_arg₂_heq _ (pushLCtxAtDepRec lctxTerm) (eq_of_heq (
              LamWF.interp.heq _ rfl HEq.rfl _ _ (Eq.symm (LamTerm.bvarLifts.equiv _ _))
            )) HEq.rfl
          )) _ _ rfl)
     ) (LamWF.interp.heq _ rfl HEq.rfl _ _ (Eq.symm (LamTerm.subst.equiv _ _ _ _ _)))
  )

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
  | .lam s body =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=argTy') (body:=body') bodyTy' wfBody =>
      LamWF.subst ltv 0 lctx
        (by rw [LamTerm.bvarLifts.zero]; exact wfArg)
        (by rw [← pushLCtxAt.equivFn]; exact wfBody)
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
        (pushLCtxAt lctxTy s 0)
        (pushLCtxAtDep lctxTerm (LamWF.interp lval lctxTy lctxTerm wfArg) 0)
        (by rw [← pushLCtxAt.equivFn]; exact wfBody)
      apply Eq.trans (b:=b)
      case h₁ =>
        apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
        rw [← pushLCtxAt.equivFn]; rfl
        exact (pushLCtxAtDep.equivFn lctxTerm _ 0)
      case h₂ =>
        dsimp
        rw [← LamWF.subst.correct]
        apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
        apply heq_of_eq; apply congr_fun; apply congr_arg;
        apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
        rw [LamTerm.bvarLifts.zero]
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