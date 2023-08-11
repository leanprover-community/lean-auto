import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

structure LamThmJudge where
  lctx  : List LamSort
  rterm : LamTerm
  rty   : LamSort

def LamThmWF (lval : LamValuation) (ltj : LamThmJudge) :=
  ∀ (lctx' : Nat → LamSort), LamWF lval.ilVal.toLamTyVal ⟨pushLCtxs lctx' ltj.lctx, ltj.rterm, ltj.rty⟩

def LamThmWF.ofBVarLifts (lval : LamValuation) (ltj : LamThmJudge)
  (hWF : LamThmWF lval ltj) : Nat := sorry

def LamThmValid (lval : LamValuation) (lctx : List LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort) (lctxTerm : ∀ n, (pushLCtxs lctx' lctx n).interp lval.ilVal.tyVal),
    ∃ (wf : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxs lctx' lctx, t, .base .prop⟩),
      GLift.down (LamWF.interp lval (pushLCtxs lctx' lctx) lctxTerm wf)

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

theorem Eq.symmAux (lval : LamValuation)
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

theorem Eq.symm (lval : LamValuation) (lctx : List LamSort)
  (H : LamThmValid lval lctx (.app (.app (.base (.eq n)) a) b)) :
  LamThmValid lval lctx (.app (.app (.base (.eq n)) b) a) := by
  unfold LamThmValid; unfold LamThmValid at H
  intros lctx' lctxTerm
  cases (H lctx' lctxTerm)
  case intro wf H =>
    exists Eq.symm.WF wf
    apply Eq.symmAux _ _ H

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

theorem Eq.transAux (lval : LamValuation)
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

theorem Eq.trans (lval : LamValuation) (lctx : List LamSort)
  (H₁ : LamThmValid lval lctx (.app (.app (.base (.eq n)) a) b))
  (H₂ : LamThmValid lval lctx (.app (.app (.base (.eq n)) b) c)) :
  LamThmValid lval lctx (.app (.app (.base (.eq n)) a) c) := by
  unfold LamThmValid; unfold LamThmValid at H₁ H₂
  intros lctx' lctxTerm
  cases (H₁ lctx' lctxTerm)
  case intro wf₁ H₁ =>
    cases (H₂ lctx' lctxTerm)
    case intro wf₂ H₂ =>
      exists Eq.trans.WF wf₁ wf₂
      apply Eq.transAux _ _ H₁ _ H₂

def Eq.subst.WF
  (wfEq : LamWF ltv ⟨lctx, .app (.app (.base (.eq n)) a) b, .base .prop⟩)
  (wfP : LamWF ltv ⟨lctx, .app p a, .base .prop⟩) :
  LamWF ltv ⟨lctx, .app p b, .base .prop⟩ :=
  match wfEq with
  | .ofApp bTy wfFn wfB =>
    match wfFn with
    | .ofApp aTy wfEq' wfA =>
      match wfEq' with
      | .ofBase HB =>
        match HB with
        | .ofEq n =>
          match wfP with
          | .ofApp aTy' wfP wfA' =>
            let heq : LamTyVal.eqLamVal ltv n = aTy' :=
              (LamWF.unique ltv wfA wfA').left
            .ofApp _ wfP (heq ▸ wfB)

theorem Eq.substAux (lval : LamValuation)
  {lctxTy : Nat → LamSort} {lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal}
  (wfEq : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app (.app (.base (.eq m)) a) b, .base .prop⟩)
  (hEq : GLift.down (LamWF.interp lval lctxTy lctxTerm wfEq))
  (wfP : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app p a, .base .prop⟩)
  (hP : GLift.down (LamWF.interp lval lctxTy lctxTerm wfP)) :
  GLift.down (LamWF.interp lval lctxTy lctxTerm (Eq.subst.WF wfEq wfP)) :=
  match wfEq with
  | .ofApp bTy wfFn wfB =>
    match wfFn with
    | .ofApp aTy wfEq' wfA =>
      match wfEq' with
      | .ofBase HB =>
        match aTy, bTy, HB with
        | _, _, .ofEq _ =>
          match wfP with
          | .ofApp aTy' wfP wfA' => by
            dsimp [trans.WF, LamWF.interp, LamBaseWF.interp];
            dsimp [trans.WF, LamWF.interp, LamBaseWF.interp] at hEq;
            dsimp [trans.WF, LamWF.interp, LamBaseWF.interp] at hP;
            let hEq' := EqLift.down _ _ _ hEq
            apply Eq.mp _ hP; apply congrArg; apply congrArg
            apply eq_of_heq; apply HEq.trans (b:=LamWF.interp lval lctxTy lctxTerm wfA)
            case h.h.h.h₁ => apply LamWF.interp.heq <;> rfl
            case h.h.h.h₂ =>
              rw [hEq']; apply LamWF.interp.heq <;> rfl

theorem Eq.subst (lval : LamValuation) (lctx : List LamSort)
  (hEq : LamThmValid lval lctx (.app (.app (.base (.eq n)) a) b))
  (hP : LamThmValid lval lctx (.app p a)) :
  LamThmValid lval lctx (.app p b) := by
  unfold LamThmValid; unfold LamThmValid at hEq hP
  intros lctx' lctxTerm
  cases (hEq lctx' lctxTerm)
  case intro wfEq hEq =>
    cases (hP lctx' lctxTerm)
    case intro wfP hP =>
      exists Eq.subst.WF wfEq wfP
      apply Eq.substAux _ _ hEq _ hP

def Eq.congr.WF
  (wfEq : LamWF ltv ⟨lctx, .app (.app (.base (.eq n)) a) b, .base .prop⟩)
  (wfT : LamWF ltv ⟨lctx, .app f a, s⟩)
  (wfEq' : LamWF ltv ⟨lctx, .base (.eq m), .func s (.func s (.base .prop))⟩) :
  LamWF ltv ⟨lctx, .app (.app (.base (.eq m)) (.app f a)) (.app f b), .base .prop⟩ :=
  match wfEq with
  | .ofApp bTy (.ofApp aTy wfEq'' wfA) wfB =>
    match wfEq'' with
    | .ofBase (.ofEq m) =>
      match wfEq' with
      | .ofBase (.ofEq n) =>
        match wfT with
        | .ofApp aTy' wfF wfA' =>
          let heq : LamTyVal.eqLamVal ltv m = aTy' :=
              (LamWF.unique ltv wfA wfA').left
          .ofApp _
            (.ofApp _ (.ofBase (.ofEq _))
            (.ofApp _ wfF (heq ▸ wfA))) (.ofApp _ wfF (heq ▸ wfB))

theorem Eq.congrAux (lval : LamValuation)
  {lctxTy : Nat → LamSort} {lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal}
  (wfEq : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app (.app (.base (.eq m)) a) b, .base .prop⟩)
  (hEq : GLift.down (LamWF.interp lval lctxTy lctxTerm wfEq))
  (wfT : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app f a, s⟩)
  (wfEq' : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .base (.eq m), .func s (.func s (.base .prop))⟩) :
  GLift.down (LamWF.interp lval lctxTy lctxTerm (Eq.congr.WF wfEq wfT wfEq')) :=
  match wfEq with
  | .ofApp bTy (.ofApp aTy wfEq'' wfA) wfB =>
    match aTy, bTy, wfEq'' with
    | _, _, .ofBase (.ofEq _) =>
      match s, wfEq' with
      | _, .ofBase (.ofEq _) =>
        match wfT with
        | .ofApp aTy' wfF wfA' => by
          dsimp [trans.WF, LamWF.interp, LamBaseWF.interp];
          dsimp [trans.WF, LamWF.interp, LamBaseWF.interp] at hEq;
          apply EqLift.up;
          have heq' := EqLift.down _ _ _ hEq
          apply congrArg; apply eq_of_heq
          apply HEq.trans (b:=LamWF.interp lval lctxTy lctxTerm wfA)
          case a.h.h.h₁ => apply LamWF.interp.heq <;> rfl
          case a.h.h.h₂ => rw [heq']; apply LamWF.interp.heq <;> rfl

theorem Eq.congr (lval : LamValuation) (lctx : List LamSort)
  (hEq : LamThmValid lval lctx (.app (.app (.base (.eq m)) a) b))
  (wfT : LamThmWF lval ⟨lctx, .app f a, s⟩)
  (wfEq' : LamThmWF lval ⟨lctx, .base (.eq m), .func s (.func s (.base .prop))⟩) :
  LamThmValid lval lctx (.app (.app (.base (.eq m)) (.app f a)) (.app f b)) := by
  unfold LamThmValid; unfold LamThmValid at hEq; unfold LamThmWF at wfT wfEq'
  intros lctx' lctxTerm
  cases (hEq lctx' lctxTerm)
  case intro wfEq hEq =>
    let wfT := wfT lctx'
    let wfEq' := wfEq' lctx'
    exists (Eq.congr.WF wfEq wfT wfEq')
    apply Eq.congrAux _ wfEq hEq wfT wfEq'

attribute [irreducible] LamThmWF LamThmValid

end Auto.Embedding.Lam