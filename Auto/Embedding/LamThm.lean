import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

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

def LamTerm.bvarLiftsIdx.equiv (idx : Nat) (t : LamTerm) (lvl : Nat) :
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

def LamTerm.bvarLifts.equiv (t : LamTerm) (lvl : Nat) :
  LamTerm.bvarLiftsRec t lvl = LamTerm.bvarLifts t lvl :=
  LamTerm.bvarLiftsIdx.equiv 0 t lvl

def LamTerm.subst (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n      => .atom n
| .base b      => .base b
| .bvar n      => pushLCtxAt LamTerm.bvar (arg.bvarLifts idx) idx n
| .lam s body  => .lam s (LamTerm.subst (.succ idx) arg body)
| .app fn arg' => .app (LamTerm.subst idx arg fn) (LamTerm.subst idx arg arg')

def LamTerm.subst.equiv (ltv : LamTyVal) (idx : Nat)
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

def LamWF.subst (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort}
  (lctx : Nat → LamSort)
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩)
  (wfBody : LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) :
  LamWF ltv ⟨lctx, LamTerm.subst idx arg body, bodyTy⟩ :=
  let GEqArg : (LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩ =
                LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩) := by
    rw [LamTerm.bvarLifts.equiv arg idx]
  let wfArg' := GEqArg ▸ wfArg
  let GEqBody : (LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩ =
                 LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩) := by
    rw [pushLCtxAt.equivFn lctx argTy idx]
  let wfBody' := GEqBody ▸ wfBody
  let GEq : (LamWF ltv ⟨lctx, (subst' ltv idx lctx wfArg' wfBody').fst, bodyTy⟩ =
             LamWF ltv ⟨lctx, LamTerm.subst idx arg body, bodyTy⟩) := by
    rw [LamTerm.subst.equiv]
  GEq ▸ (LamWF.subst' ltv idx lctx wfArg' wfBody').snd

def LamWF.subst.equiv (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort}
  (lctx : Nat → LamSort)
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩)
  (wfBody : LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) :
  let GEqArg : (LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩ =
                LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩) := by
    rw [LamTerm.bvarLifts.equiv arg idx]
  let wfArg' := GEqArg ▸ wfArg
  let GEqBody : (LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩ =
                 LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩) := by
    rw [pushLCtxAt.equivFn lctx argTy idx]
  let wfBody' := GEqBody ▸ wfBody
  HEq (LamWF.subst' ltv idx lctx wfArg' wfBody').snd (LamWF.subst ltv idx lctx wfArg wfBody) := by
    let GEqArg : (LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩ =
                  LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩) := by
      rw [LamTerm.bvarLifts.equiv arg idx]
    let wfArg' := GEqArg ▸ wfArg
    let GEqBody : (LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩ =
                   LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩) := by
      rw [pushLCtxAt.equivFn lctx argTy idx]
    let wfBody' := GEqBody ▸ wfBody
    let GEq : (LamWF ltv ⟨lctx, (subst' ltv idx lctx wfArg' wfBody').fst, bodyTy⟩ =
               LamWF ltv ⟨lctx, LamTerm.subst idx arg body, bodyTy⟩) := by
      rw [LamTerm.subst.equiv]
    apply heq_of_eqRec_eq GEq; rfl

def LamWF.subst.correct.{u}
  (lval : LamValuation.{u}) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts arg idx, argTy⟩)
  (wfBody : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAt lctxTy argTy idx, body, bodyTy⟩) :
  let wfSubst := LamWF.subst lval.ilVal.toLamTyVal idx lctxTy wfArg wfBody
  (LamTerm.interp lval (pushLCtxAt lctxTy argTy idx)
    (pushLCtxAtDep lctxTerm (LamTerm.interp lval lctxTy lctxTerm wfArg) idx) wfBody
  = LamTerm.interp lval lctxTy lctxTerm wfSubst) :=
  let GEqArg : (LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts arg idx, argTy⟩ =
                LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLiftsRec arg idx, argTy⟩) := by
    rw [LamTerm.bvarLifts.equiv arg idx]
  let wfArg' := GEqArg ▸ wfArg
  let GEqBody : (LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAt lctxTy argTy idx, body, bodyTy⟩ =
                 LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAtRec lctxTy argTy idx, body, bodyTy⟩) := by
    rw [pushLCtxAt.equivFn lctxTy argTy idx]
  let wfBody' := GEqBody ▸ wfBody
  by
    dsimp; apply eq_of_heq
    let bArg := (LamWF.subst' lval.ilVal.toLamTyVal idx lctxTy wfArg' wfBody').snd
    apply HEq.trans (b := LamTerm.interp lval lctxTy lctxTerm bArg)
    case h.h₁ =>
      dsimp
      rw [← LamWF.subst'.correct]
      congr
      case h.h.e_4 => rw [pushLCtxAt.equivFn]
      case h.h.e_5 =>
        let HEquiv := pushLCtxAtDep.equivFn lctxTerm (LamTerm.interp lval lctxTy lctxTerm wfArg) idx
        apply HEq.trans (HEq.symm HEquiv);
        apply heq_of_eq;
        apply congrArg (f := fun x => pushLCtxAtDepRec lctxTerm x idx)
        congr;
        case h.h.e_1 => rw [LamTerm.bvarLifts.equiv];
        case h.h.e_6 => apply heq_of_eqRec_eq GEqArg; rfl
      case h.h.e_6 => apply heq_of_eqRec_eq GEqBody; rfl
    case h.h₂ =>
      congr
      case h.h.e_1 => rw [← LamTerm.subst.equiv]
      case h.h.e_6 =>
        dsimp; apply LamWF.subst.equiv

end Auto.Embedding.Lam