import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

def Eq.symm.WF (wf : LamWF ltv ⟨lctx, .app (.app (.base (.eq n)) a) b, .base .prop⟩) :
  LamWF ltv ⟨lctx, .app (.app (.base (.eq n)) b) a, .base .prop⟩ :=
  match wf with
  | .ofApp argTy wfFn wfB =>
    match wfFn with
    | .ofApp argTy' wfEq wfA =>
      match wfEq with
      | .ofBase HB =>
        match HB with
        | .ofEq n => .ofApp _ (.ofApp _ (.ofBase (.ofEq n)) wfB) wfA

theorem Eq.symm (lval : LamValuation)
  {lctxTy : Nat → LamSort} {lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal}
  (wf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app (.app (.base (.eq n)) a) b, .base .prop⟩)
  (_ : GLift.down (LamWF.interp lval lctxTy lctxTerm wf)) :
  GLift.down (LamWF.interp lval lctxTy lctxTerm (Eq.symm.WF wf)) :=
  match wf with
  | .ofApp argTy wfFn wfB =>
    match wfFn with
    | .ofApp argTy' wfEq wfA =>
      match wfEq with
      | .ofBase HB => by
        cases HB; case ofEq H =>
        dsimp [symm.WF, LamWF.interp, LamBaseWF.interp];
        dsimp [symm.WF, LamWF.interp, LamBaseWF.interp] at H;
        have H' := EqLift.down _ _ _ H
        apply EqLift.up
        exact (_root_.Eq.symm H')

end Auto.Embedding.Lam