module

public import Auto.Embedding.LamBase.LamWF
public import Auto.Embedding.LamBase.Valuation

@[expose] public section

/-! The interpretation `LamWF.interp` of well-typed terms -/

namespace Auto.Embedding.Lam

noncomputable def LamWF.interp.{u} (lval : LamValuation.{u})
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) :
  (lwf : LamWF lval.toLamTyVal ⟨lctxTy, t, rty⟩) → rty.interp lval.tyVal
| .ofAtom n => lval.varVal n
| .ofEtom n => lval.eVarVal n
| .ofBase H => LamBaseTerm.LamWF.interp lval H
| .ofBVar n => lctxTerm n
| @ofLam _ _ argTy _ body H =>
  fun (x : argTy.interp lval.tyVal) =>
    LamWF.interp lval (pushLCtx argTy lctxTy) (pushLCtxDep (rty:=lctxTy) x lctxTerm) H
| .ofApp _ HFn HArg =>
  let mfn := LamWF.interp lval lctxTy lctxTerm HFn
  let marg := LamWF.interp lval lctxTy lctxTerm HArg
  mfn marg

theorem LamWF.interp_eq (lval : LamValuation.{u})
  {lctxTerm₁ : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy n).interp lval.tyVal}
  (HLCtxTermEq : HEq lctxTerm₁ lctxTerm₂)
  (lwf₁ : LamWF lval.toLamTyVal ⟨lctxTy, t₁, rty⟩)
  (lwf₂ : LamWF lval.toLamTyVal ⟨lctxTy, t₂, rty⟩)
  (HTeq : t₁ = t₂) :
  LamWF.interp lval lctxTy lctxTerm₁ lwf₁ = LamWF.interp lval lctxTy lctxTerm₂ lwf₂ := by
  cases HTeq; cases HLCtxTermEq;
  have HUniq := LamWF.unique lwf₁ lwf₂
  rcases HUniq with ⟨⟨⟩, ⟨⟩⟩; rfl

theorem LamWF.interp_heq (lval : LamValuation.{u})
  {lctxTy₁ lctxTy₂ : Nat → LamSort} (HLCtxTyEq : lctxTy₁ = lctxTy₂)
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval.tyVal}
  (HLCtxTermEq : HEq lctxTerm₁ lctxTerm₂)
  (lwf₁ : LamWF lval.toLamTyVal ⟨lctxTy₁, t₁, rty₁⟩)
  (lwf₂ : LamWF lval.toLamTyVal ⟨lctxTy₂, t₂, rty₂⟩)
  (HTeq : t₁ = t₂) :
  HEq (LamWF.interp lval lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval lctxTy₂ lctxTerm₂ lwf₂) := by
  cases HTeq; cases HLCtxTyEq; cases HLCtxTermEq;
  have HUniq := LamWF.unique lwf₁ lwf₂
  cases HUniq; case intro left right =>
    cases left; cases right; rfl

-- In most use cases, we would have `b = .prop`
theorem LamWF.interp_substLCtxTerm
  {wf : LamWF lval.toLamTyVal ⟨lctxTy, t, s⟩}
  {wf' : LamWF lval.toLamTyVal ⟨lctxTy', t, s⟩}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm' : ∀ n, (lctxTy' n).interp lval.tyVal}
  (HLCtxTyEq : lctxTy = lctxTy') (HLCtxTermEq : HEq lctxTerm lctxTerm') :
  LamWF.interp lval lctxTy lctxTerm wf = LamWF.interp lval lctxTy' lctxTerm' wf' := by
  cases HLCtxTyEq; cases HLCtxTermEq; rcases (LamWF.unique wf wf') with ⟨_, ⟨⟩⟩; rfl

-- In most use cases, we would have `b = .prop`
theorem LamWF.interp_substLCtxTerm_rec
  {wf : LamWF lval.toLamTyVal ⟨lctxTy, t, s⟩}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm' : ∀ n, (lctxTy' n).interp lval.tyVal}
  (HLCtxTyEq : lctxTy = lctxTy') (HLCtxTermEq : HEq lctxTerm lctxTerm') :
  LamWF.interp lval lctxTy lctxTerm wf = LamWF.interp lval lctxTy' lctxTerm' (HLCtxTyEq ▸ wf) := by
  cases HLCtxTyEq; cases HLCtxTermEq; rfl

theorem LamWF.interp_substWF
  {wf wf' : LamWF lval.toLamTyVal ⟨lctxTy, t, s⟩}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal} :
  LamWF.interp lval lctxTy lctxTerm wf = LamWF.interp lval lctxTy lctxTerm wf' :=
  LamWF.interp_substLCtxTerm rfl HEq.rfl

theorem LamWF.interp_prop_eqExists
  {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∃ (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩), GLift.down (LamWF.interp lval lctx lctxTerm wf)) =
  GLift.down (LamWF.interp lval lctx lctxTerm wf) :=
  propext (Iff.intro
    (fun ⟨wf', H'⟩ => Eq.mp (by
      apply congrArg; apply eq_of_heq; apply interp_heq <;> rfl) H')
    (fun H => ⟨wf, H⟩))

theorem LamWF.interp_prop_eqForall
  {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∀ (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩), GLift.down (LamWF.interp lval lctx lctxTerm wf)) =
  GLift.down (LamWF.interp lval lctx lctxTerm wf) :=
  propext (Iff.intro
    (fun H => H wf)
    (fun H wf => Eq.mp (by
      apply congrArg; apply eq_of_heq; apply interp_heq <;> rfl) H))

theorem LamWF.interp_atom
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .atom n, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (lval.varVal n) :=
  match wft with
  | .ofAtom _ => HEq.rfl

theorem LamWF.interp_etom
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .etom n, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (lval.eVarVal n) :=
  match wft with
  | .ofEtom _ => HEq.rfl

theorem LamWF.interp_base
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .base b, s⟩) {lctxTerm} :
  wft.interp lval lctxTy lctxTerm = wft.getBase.interp lval :=
  match wft with
  | .ofBase _ => rfl

theorem LamWF.interp_base'
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .base b, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (b.interp lval) :=
  match wft with
  | .ofBase _ => LamBaseTerm.interp_equiv _ _

theorem LamWF.interp_bvar
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .bvar n, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (lctxTerm n) :=
  match wft with
  | .ofBVar _ => HEq.rfl

theorem LamWF.interp_lam
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .lam argTy body, .func argTy resTy⟩) {lctxTerm} :
  wft.interp lval lctxTy lctxTerm = (fun x => wft.getLam.interp lval
    (pushLCtx argTy lctxTy) (pushLCtxDep x lctxTerm)) :=
  match wft with
  | .ofLam _ _ => rfl

theorem LamWF.interp_app
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .app argTy fn arg, s⟩) {lctxTerm} :
  wft.interp lval lctxTy lctxTerm = (wft.getFn.interp lval lctxTy lctxTerm) (wft.getArg.interp lval lctxTy lctxTerm) :=
  match wft with
  | .ofApp _ _ _ => rfl

theorem LamWF.interp_bvarAppsRev
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨pushLCtxs lctxTy.reverse lctxTy', t, LamSort.mkFuncs s lctxTy⟩)
  (wfAp : LamWF lval.toLamTyVal ⟨pushLCtxs lctxTy.reverse lctxTy', t.bvarAppsRev lctxTy, s⟩)
  {valPre : HList (LamSort.interp lval.tyVal) lctxTy → LamSort.interp lval.tyVal s}
  {lctxTerm : HList (LamSort.interp lval.tyVal) lctxTy}
  {lctxTerm' : ∀ (n : Nat), (lctxTy' n).interp lval.tyVal}
  (ht : HEq (wft.interp lval _ (pushLCtxsDep lctxTerm.reverse lctxTerm')) (LamSort.curry valPre)) :
  HEq
    (LamWF.interp lval (pushLCtxs lctxTy.reverse lctxTy') (pushLCtxsDep lctxTerm.reverse lctxTerm') wfAp)
    (valPre lctxTerm) := by
  induction lctxTerm generalizing t lctxTy' lctxTerm'
  case nil =>
    apply HEq.trans _ ht; apply LamWF.interp_heq <;> rfl
  case cons lty lctxTy lterm lctxTerm IH =>
    dsimp [LamSort.mkFuncs_cons] at wft;
    rw [List.reverse_cons, pushLCtxs_append_singleton] at wft
    dsimp [LamTerm.bvarAppsRev] at wfAp ⊢
    rw [List.reverse_cons, pushLCtxs_append_singleton] at wfAp
    rw [interp_substLCtxTerm_rec (by rw [List.reverse_cons])
      (pushLCtxsDep_substxs _ _ _ List.reverse_cons HList.reverse_cons)]
    rw [interp_substLCtxTerm_rec
      (pushLCtxs_append_singleton _ _ _) (pushLCtxsDep_append_singleton _ _ _)]
    rw [LamWF.interp_substWF (wf':=wfAp)]
    apply IH (LamWF.ofApp _ wft LamWF.bvarAppsRev_Aux)
    simp only[interp]; apply HEq.trans (b:=LamSort.curry valPre lterm) <;> try rfl
    case h₁ =>
      apply heq_of_eq; apply congr
      case h₁ =>
        apply eq_of_heq; apply HEq.trans _ ht; apply heq_of_eq; apply interp_substLCtxTerm
        rw [List.reverse_cons, pushLCtxs_append_singleton]
        apply HEq.symm; apply HEq.trans _ (pushLCtxsDep_append_singleton _ _ _)
        apply pushLCtxsDep_substxs; rw [List.reverse_cons]; apply HList.reverse_cons
      case h₂ =>
        apply eq_of_heq; apply HEq.trans (LamWF.interp_bvar _)
        apply HEq.trans (pushLCtxsDep_ge _ (Nat.le_of_eq List.length_reverse))
        rw [List.length_reverse, Nat.sub_self]; rfl

theorem LamWF.interp_eqForallEF
  {wf : LamWF lval.toLamTyVal ⟨pushLCtx s lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEF wf)) = (∀ x,
    GLift.down (LamWF.interp lval (pushLCtx s lctx) (pushLCtxDep x lctxTerm) wf)) := rfl

theorem LamWF.interp_eqForallEFN'
  {lval : LamValuation.{u}} {lctxTerm : ∀ n, (lctx n).interp lval.tyVal}
  {wf : LamWF lval.toLamTyVal ⟨pushLCtxs ls lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEFN' wf)) = (∀ xs,
    GLift.down (LamWF.interp lval (pushLCtxs ls lctx) (pushLCtxsDep xs lctxTerm) wf)) := by
  generalize LamWF.mkForallEFN' wf = wfMkF
  induction ls generalizing t
  case nil =>
    dsimp [mkForallEFN, interp]
    conv =>
      enter [2]; rw [IsomType.eqForall HList.nil_IsomType.{0, u + 1, u + 1}]
      rw [PUnit.eqForall]; unfold HList.nil_IsomType; dsimp
      dsimp [pushLCtxs, pushLCtxsDep, Nat.blt, Nat.ble]
    apply congrArg; apply interp_substWF
  case cons s ls IH =>
    revert wfMkF; rw [List.reverse_cons, LamTerm.mkForallEFN_append_singleton]; intro wfMkF
    apply Eq.trans (IH (wf:=LamWF.fromMkForallEFN' wfMkF) _)
    conv =>
      enter [2]; rw [IsomType.eqForall HList.cons_IsomType]; rw [Prod.eqForall']
      unfold HList.cons_IsomType; dsimp; enter [xs, x]
    apply forall_congr; intro xs
    conv => lhs; rw [interp_substWF
      (wf':=LamWF.mkForallEF (LamWF.fromMkForallEF (LamWF.fromMkForallEFN' wfMkF)))]
    rw [interp_eqForallEF]
    apply forall_congr; intro x
    apply congrArg; apply eq_of_heq; apply interp_heq <;> try rfl
    case HLCtxTyEq => rw [pushLCtxs_cons]
    case HLCtxTermEq => apply HEq.symm; apply pushLCtxsDep_cons

theorem LamWF.interp_eqForallEFN
  {lval : LamValuation.{u}} {ls : List LamSort} {lctxTerm : ∀ n, (lctx n).interp lval.tyVal}
  {wf : LamWF lval.toLamTyVal ⟨pushLCtxs ls.reverse lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEFN wf)) = (∀ xs,
    GLift.down (LamWF.interp lval (pushLCtxs ls.reverse lctx) (pushLCtxsDep xs lctxTerm) wf)) := by
  apply Eq.trans _ interp_eqForallEFN'; apply congrArg
  apply eq_of_heq; apply interp_heq <;> try rfl
  rw [List.reverse_reverse]

theorem LamWF.interp_bvarApps
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨pushLCtxs (List.reverseAux tyex lctx) lctx', t, LamSort.mkFuncsRev s lctx⟩)
  (wfAp : LamWF lval.toLamTyVal ⟨pushLCtxs (List.reverseAux tyex lctx) lctx', LamTerm.bvarApps t lctx (List.length tyex), s⟩)
  {valPre : HList (LamSort.interp lval.tyVal) lctx → LamSort.interp lval.tyVal s}
  {termex : HList (LamSort.interp lval.tyVal) tyex}
  {lctxTerm : HList (LamSort.interp lval.tyVal) lctx}
  {lctxTerm' : ∀ (n : Nat), (lctx' n).interp lval.tyVal}
  (ht : HEq (wft.interp lval _ (pushLCtxsDep (HList.reverseAux termex lctxTerm) lctxTerm')) (LamSort.curryRev valPre)) :
  HEq
    (LamWF.interp lval
      (pushLCtxs (List.reverseAux tyex lctx) lctx')
      (pushLCtxsDep (lctxty:=LamSort.interp lval.tyVal) (HList.reverseAux termex lctxTerm) lctxTerm')
      wfAp)
    (valPre lctxTerm) := by
  induction lctxTerm generalizing s tyex
  case nil =>
    apply HEq.trans _ ht; apply LamWF.interp_heq <;> rfl
  case cons lty lctx lx lctxTerm IH =>
    dsimp [LamSort.mkFuncsRev] at wft
    dsimp [LamTerm.bvarApps] at wfAp; cases wfAp; case ofApp HArg HFn =>
      apply congr_hd_heq (f₂:=fun lx =>valPre (HList.cons lx lctxTerm)) (x₂:=lx) <;> try rfl
      case h₁ =>
        apply @IH (lty::tyex) (.func lty s) wft _ (fun lctxTerm lx => valPre (.cons lx lctxTerm)) (.cons lx termex) ht
      case h₂ =>
        apply HEq.trans (LamWF.interp_bvar _);
        clear s t wft valPre ht HFn HArg IH
        dsimp [pushLCtxs, pushLCtxsDep]
        have hlt : tyex.length < (tyex.reverseAux (lty :: lctx)).length := by
          rw [List.reverseAux_eq, List.length_append, List.length_reverse];
          dsimp [List.length]; rw [Nat.add_succ]; apply Nat.succ_le_succ_iff.mpr
          apply Nat.le_add_right
        rw [Eq.mp (Eq.symm Nat.blt_eq) hlt]; dsimp
        apply HEq.trans (b:=HList.getD (lctxTerm' 0) (HList.append (termex.reverseAux .nil) (.cons lx lctxTerm)) tyex.length)
        case h₁ =>
          apply HList.getD_heq <;> try rfl
          case htys => rw [List.reverseAux_eq_append]
          case hhl => apply HList.reverseAux_eq_append
        case h₂ =>
          apply HEq.trans (HList.getD_append_right _ _ ?left) ?right <;>
            rw [List.reverseAux_eq, List.append_nil, List.length_reverse]
          case left => apply Nat.le_refl
          case right => rw [Nat.sub_self]; rfl

theorem LamWF.interp_insertEVarAt_eIdx
  {lval : LamValuation.{u}} {val : LamSort.interp lval.tyVal ty}
  (lwf : LamWF {lval.toLamTyVal with lamEVarTy := replaceAt ty pos lamEVarTy'} ⟨lctxTy, .etom pos, rty⟩)
  {lctxTerm : ∀ (n : Nat), LamSort.interp lval.tyVal (lctxTy n)}
  {eVarVal' : (n : Nat) → LamSort.interp lval.tyVal (lamEVarTy' n)} :
  let lval' := {lval with lamEVarTy := replaceAt ty pos lamEVarTy',
                          eVarVal := replaceAtDep val pos eVarVal'}
  HEq (lwf.interp lval' lctxTy lctxTerm) val := by
  cases lwf; simp only [interp, replaceAtDep]; simp only [replaceAt]
  rw [Nat.beq_refl]; rfl

theorem LamWF.interp_eVarIrrelevance
  (lval₁ : LamValuation.{u}) (lval₂ : LamValuation.{u})
  {lctxTy₁ lctxTy₂ : Nat → LamSort}
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval₁.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval₂.tyVal}
  {t : LamTerm} {rty : LamSort}
  (lwf₁ : LamWF lval₁.toLamTyVal ⟨lctxTy₁, t, rty⟩)
  (lwf₂ : LamWF lval₂.toLamTyVal ⟨lctxTy₂, t, rty⟩)
  (hLamVarTy : lval₁.lamVarTy = lval₂.lamVarTy)
  (hLamILTy : lval₁.lamILTy = lval₂.lamILTy)
  (hTyVal : HEq lval₁.tyVal lval₂.tyVal)
  (hVarVal : HEq lval₁.varVal lval₂.varVal)
  (hILVal : HEq lval₁.ilVal lval₂.ilVal)
  (hLCtxTy : lctxTy₁ = lctxTy₂)
  (hLCtxTerm : HEq lctxTerm₁ lctxTerm₂)
  (hirr : ∀ n, n < t.maxEVarSucc →
    lval₁.lamEVarTy n = lval₂.lamEVarTy n ∧ HEq (lval₁.eVarVal n) (lval₂.eVarVal n)) :
  HEq (LamWF.interp lval₁ lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval₂ lctxTy₂ lctxTerm₂ lwf₂) := by
  rcases lval₁ with ⟨⟨lamVarTy₁, lamILTy₁, lamEVarTy₁⟩, tyVal₁, varVal₁, ilVal₁, eVarVal₁⟩
  rcases lval₂ with ⟨⟨lamVarTy₂, lamILTy₂, lamEVarTy₂⟩, tyVal₂, varVal₂, ilVal₂, eVarVal₂⟩
  dsimp at hLamVarTy hLamILTy hTyVal hVarVal hILVal hirr
  cases hLamVarTy; cases hLamILTy; cases hTyVal
  cases hVarVal; cases hILVal; cases hLCtxTy; cases hLCtxTerm
  case refl.refl.refl.refl.refl.refl =>
    dsimp; dsimp at varVal₁ ilVal₁ eVarVal₁ lctxTerm₁ lwf₁ eVarVal₂ lwf₂
    induction t generalizing lctxTy₁ rty <;> try (cases lwf₁; cases lwf₂; rfl)
    case etom n =>
      cases lwf₁
      have htyeq : lamEVarTy₁ n = lamEVarTy₂ n := by
        apply (hirr _ _).left; exact .refl
      dsimp at lwf₂;
      let lwf₂' := htyeq ▸ lwf₂;
      let lval₂ : LamValuation := ⟨⟨lamVarTy₁, lamILTy₁, lamEVarTy₂⟩, tyVal₁, varVal₁, ilVal₁, eVarVal₂⟩
      apply HEq.trans _ (LamWF.interp_heq (lval:=lval₂) (lwf₁ := lwf₂') rfl HEq.rfl _ rfl)
      cases lwf₂'; dsimp [interp]; apply (hirr _ _).right; exact .refl
    case base b =>
      cases lwf₁; cases lwf₂; simp only [interp]
      apply LamBaseTerm.LamWF.interp_lvalIrrelevance <;> rfl
    case lam s t IH =>
      cases lwf₁; case ofLam bodyTy₁ H₁ =>
        cases lwf₂; case ofLam H₂ =>
          simp only [interp]; apply HEq.funext; intro x; apply IH
          exact hirr
    case app s fn arg IHFn IHArg =>
      cases lwf₁; case ofApp HArg₁ HFn₁ =>
        cases lwf₂; case ofApp HArg₂ HFn₂ =>
          simp only [interp]; apply congr_h_heq <;> try rfl
          case h₁ =>
            apply IHFn; intros n hlt;
            apply (hirr n (Nat.le_trans hlt (Nat.le_max_left _ _)))
          case h₂ =>
            apply IHArg; intros n hlt;
            apply (hirr n (Nat.le_trans hlt (Nat.le_max_right _ _)))

theorem LamWF.interp_lctxIrrelevance
  (lval : LamValuation.{u}) {lctxTy₁ lctxTy₂ : Nat → LamSort}
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval.tyVal}
  {t : LamTerm} {rty : LamSort}
  (lwf₁ : LamWF lval.toLamTyVal ⟨lctxTy₁, t, rty⟩)
  (lwf₂ : LamWF lval.toLamTyVal ⟨lctxTy₂, t, rty⟩)
  (hirr : ∀ n, n < t.maxLooseBVarSucc →
    lctxTy₁ n = lctxTy₂ n ∧ HEq (lctxTerm₁ n) (lctxTerm₂ n)) :
  HEq (LamWF.interp lval lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval lctxTy₂ lctxTerm₂ lwf₂) := by
  induction t generalizing lctxTy₁ lctxTy₂ rty <;> try (cases lwf₁; cases lwf₂; rfl)
  case base b =>
    cases lwf₁; cases lwf₂; simp only [interp]; apply LamBaseTerm.LamWF.interp_heq <;> rfl
  case bvar n =>
    cases lwf₁; simp only [interp]
    have htyeq : lctxTy₁ n = lctxTy₂ n := by
      apply (hirr _ _).left; exact .refl
    rw [htyeq] at lwf₂; apply HEq.trans (b:=interp _ _ lctxTerm₂ lwf₂)
    case h₁ =>
      cases lwf₂; simp only [interp]; apply (hirr _ _).right; exact .refl
    case h₂ =>
      apply interp_heq <;> rfl
  case lam s t IH =>
    cases lwf₁; case ofLam bodyTy₁ H₁ =>
      cases lwf₂; case ofLam H₂ =>
        simp only [interp]; apply HEq.funext; intros x; apply IH
        intros n hlt; dsimp [pushLCtx, pushLCtxDep]
        cases n
        case zero => exact And.intro rfl HEq.rfl
        case succ n =>
          apply hirr;
          apply Nat.le_pred_of_succ_le _ hlt
          apply Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hlt
  case app s fn arg IHFn IHArg =>
    cases lwf₁; case ofApp HArg₁ HFn₁ =>
      cases lwf₂; case ofApp HArg₂ HFn₂ =>
        simp only [interp]; apply congr_h_heq <;> try rfl
        case h₁ =>
          apply IHFn; intros n hlt;
          apply (hirr n (Nat.le_trans hlt (Nat.le_max_left _ _)))
        case h₂ =>
          apply IHArg; intros n hlt;
          apply (hirr n (Nat.le_trans hlt (Nat.le_max_right _ _)))

theorem LamTerm.forallEFBody_forallEFTys_eq (wft : LamWF ltv ⟨lctx, t, s⟩) :
  t = LamTerm.mkForallEFN t.getForallEFBody t.getForallEFTys := by
  generalize hsize' : t.size = n
  have hsize : t.size ≤ n := by cases hsize'; apply Nat.le_refl
  clear hsize'; induction n generalizing lctx t s
  case zero => have hnz := @size_gt_zero t; rw [Nat.le_zero.mp hsize] at hnz; cases hnz
  case succ n IH =>
    cases t <;> try rfl
    case app s fn arg =>
      cases fn <;> try rfl
      case base b =>
        cases b <;> try rfl
        case forallE s' =>
          cases arg <;> try rfl
          case lam s'' body =>
            dsimp [getForallEFTys, getForallEFBody, mkForallEFN]
            cases wft.getFn.getBase; cases wft.getArg
            case ofLam wfBody =>
              rw [← IH wfBody]; rfl
              have hsize' := Nat.le_trans size_app_gt_size_arg hsize
              apply Nat.le_of_succ_le_succ (Nat.le_of_succ_le hsize')

end Auto.Embedding.Lam
