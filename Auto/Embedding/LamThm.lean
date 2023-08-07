import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

def LamTerm.bvarLifts (t : LamTerm) (lvl : Nat) : LamTerm :=
  match t with
  | .atom n     => .atom n
  | .base b     => .base b
  | .bvar n     => .bvar (Nat.add n lvl)
  | .lam s t    => .lam s (t.bvarLifts lvl)
  | .app fn arg => .app (fn.bvarLifts lvl) (arg.bvarLifts lvl)

def LamTerm.subst (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n     => .atom n
| .base b     => .base b
| .bvar n     => pushLCtxAt LamTerm.bvar (arg.bvarLifts idx) idx n
| .lam s body => .lam s (LamTerm.subst (.succ idx) arg body)
| .app fn arg' => .app (LamTerm.subst idx arg fn) (LamTerm.subst idx arg arg')

def LamTerm.subst_correct (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort}
  (lctx : Nat → LamSort) :
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLiftsRec arg idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAtRec lctx argTy idx, body, bodyTy⟩) →
  LamTerm.subst idx arg body = (LamWF.subst ltv idx lctx wfArg wfBody).fst
| wfArg, .ofAtom n => rfl
| wfArg, .ofBase (b:=b) H => rfl
| wfArg, .ofBVar n => by
  simp [LamTerm.subst, LamWF.subst]
  sorry
| wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H => sorry
| wfArg, .ofApp argTy' HFn HArg => sorry

end Auto.Embedding.Lam