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
  (H : GLift.down (LamWF.interp lval lctxTy lctxTerm wf)) :
  GLift.down (LamWF.interp lval lctxTy lctxTerm (Eq.symm.WF wf)) :=
  match wf with
  | .ofApp argTy wfFn wfB =>
    match wfFn with
    | .ofApp argTy' wfEq wfA =>
      match wfEq with
      | .ofBase HB => by
        cases HB; case ofEq =>
        have H' := EqLift.down _ _ _ H
        apply EqLift.up
        exact (_root_.Eq.symm H')

def Eq.trans.WF
  (wf₁ : LamWF ltv ⟨lctx, .app (.app (.base (.eq m)) a) b, .base .prop⟩)
  (wf₂ : LamWF ltv ⟨lctx, .app (.app (.base (.eq n)) b) c, .base .prop⟩)
  : LamWF ltv ⟨lctx, .app (.app (.base (.eq n)) a) c, .base .prop⟩ :=
  match wf₁ with
  | .ofApp argTy₁ wfFn₁ wfB₁ =>
    match wfFn₁ with
    | .ofApp argTy₁' wfEq₁ wfA =>
      match wfEq₁ with
      | .ofBase HB₁ =>
        match HB₁ with
        | .ofEq m =>
          match wf₂ with
          | .ofApp argTy₂ wfFn₂ wfC =>
            match wfFn₂ with
            | .ofApp argTy₂' wfEq₂ wfB₂ =>
              match wfEq₂ with
              | .ofBase HB₂ =>
                match HB₂ with
                | .ofEq n =>
                  let heq : LamTyVal.eqLamVal ltv m = LamTyVal.eqLamVal ltv n :=
                    (LamWF.unique ltv wfB₁ wfB₂).left
                  .ofApp _ (.ofApp _ (.ofBase (.ofEq n)) (heq ▸ wfA)) wfC

theorem Eq.trans (lval : LamValuation)
  {lctxTy : Nat → LamSort} {lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal}
  (wf₁ : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app (.app (.base (.eq m)) a) b, .base .prop⟩)
  (H₁ : GLift.down (LamWF.interp lval lctxTy lctxTerm wf₁))
  (wf₂ : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app (.app (.base (.eq n)) b) c, .base .prop⟩)
  (H₂ : GLift.down (LamWF.interp lval lctxTy lctxTerm wf₂)) :
  GLift.down (LamWF.interp lval lctxTy lctxTerm (Eq.trans.WF wf₁ wf₂)) :=
  match wf₁ with
  | .ofApp argTy₁ wfFn₁ wfB₁ =>
    match wfFn₁ with
    | .ofApp argTy₁' wfEq₁ wfA =>
      match wfEq₁ with
      | .ofBase HB₁ =>
        match argTy₁, argTy₁', HB₁ with
        | _, _, .ofEq _ =>
          match wf₂ with
          | .ofApp argTy₂ wfFn₂ wfC =>
            match wfFn₂ with
            | .ofApp argTy₂' wfEq₂ wfB₂ =>
              match wfEq₂ with
              | .ofBase HB₂ =>
                match argTy₂, argTy₂', HB₂ with
                | _, _, .ofEq _ => by
                  let heq : LamTyVal.eqLamVal _ m = LamTyVal.eqLamVal _ n :=
                    (LamWF.unique lval.ilVal.toLamTyVal wfB₁ wfB₂).left
                  dsimp [trans.WF, LamWF.interp, LamBaseWF.interp];
                  dsimp [trans.WF, LamWF.interp, LamBaseWF.interp] at H₁;
                  dsimp [trans.WF, LamWF.interp, LamBaseWF.interp] at H₂;
                  apply EqLift.up;
                  have H₁' := EqLift.down _ _ _ H₁
                  have H₂' := EqLift.down _ _ _ H₂
                  apply eq_of_heq
                  apply HEq.trans (b:=LamWF.interp lval lctxTy lctxTerm wfA)
                  case a.h.h₁ => apply LamWF.interp.heq <;> rfl
                  case a.h.h₂ =>
                    rw [H₁']; rw [← H₂']; apply LamWF.interp.heq <;> rfl                  

end Auto.Embedding.Lam