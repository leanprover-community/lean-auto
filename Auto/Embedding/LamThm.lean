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
  LamTerm.subst idx arg body = (LamWF.subst ltv idx lctx wfArg wfBody).fst
| wfArg, .ofAtom n => rfl
| _,     .ofBase (b:=b) H => rfl
| wfArg, .ofBVar n => by
  dsimp [LamTerm.subst, LamWF.subst]
  let f := fun (x : LamSort) (t : (substed : LamTerm) × LamWF ltv ⟨lctx, substed, x⟩) => t.fst
  let β₀ := fun ty substed => LamWF ltv ⟨lctx, substed, ty⟩
  let lctx' := fun n => @Sigma.mk LamTerm (β₀ _) (LamTerm.bvar n) (@LamWF.ofBVar ltv lctx n)
  let x := @Sigma.mk LamTerm (β₀ _) (bvarLiftsRec arg idx) wfArg
  let GEq := @pushLCtxAtDepRec.comm _ _ lctx _ f lctx' _ x idx n
  simp at GEq; rw [GEq]; rw [pushLCtxAtDepRec.nonDep]
  rw [pushLCtxAt.equiv]; rw [LamTerm.bvarLifts.equiv]
| wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H => by
  dsimp [LamTerm.subst, LamWF.subst];
  rw [← @LamTerm.subst.equiv ltv (.succ idx) arg argTy body' bodyTy']
| wfArg, .ofApp argTy' HFn HArg => by
  dsimp [LamTerm.subst, LamWF.subst]
  rw [← LamTerm.subst.equiv ltv idx lctx wfArg HFn]
  rw [← LamTerm.subst.equiv ltv idx lctx wfArg HArg]

end Auto.Embedding.Lam