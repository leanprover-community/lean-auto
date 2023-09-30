import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

@[reducible] def dfLCtxTy : Nat → LamSort := fun _ => .base .prop

@[reducible] def dfLCtxTerm (val : Nat → Type u) : ∀ n, LamSort.interp val (dfLCtxTy n) :=
  fun _ => GLift.up.{1, u} False

def LamNonempty (tyVal : Nat → Type u) (s : LamSort) := Nonempty (s.interp tyVal)

def LamWF.generalizeTy (wf : LamWF ltv ⟨lctx, t, s⟩) :
  (s : LamSort) × LamWF ltv ⟨lctx, t, s⟩ := ⟨s, wf⟩

def LamThmWF
  (lval : LamValuation) (lctx : List LamSort) (rty : LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t, rty⟩

def LamThmWFP (lval : LamValuation) (lctx : List LamSort) (rty : LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), Nonempty (LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t, rty⟩)

def LamThmWFD (lval : LamValuation.{u}) lctx rty t :=
  ∃ (_ : LamWF lval.toLamTyVal ⟨pushLCtxs lctx dfLCtxTy, t, rty⟩), t.maxLooseBVarSucc ≤ lctx.length

abbrev LamValid (lval : LamValuation) (lctx : Nat → LamSort) (t : LamTerm) :=
  ∃ (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩),
    ∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal), GLift.down (LamWF.interp lval lctx lctxTerm wf)

def LamThmValid (lval : LamValuation) (lctx : List LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamValid lval (pushLCtxs lctx lctx') t

def LamThmValidD (lval : LamValuation.{u}) lctx t :=
  t.maxLooseBVarSucc ≤ lctx.length ∧ 
  ∃ (wf : LamWF lval.toLamTyVal ⟨pushLCtxs lctx dfLCtxTy, t, .base .prop⟩),
    ∀ (lctxTerm : HList (LamSort.interp lval.tyVal) lctx),
      (wf.interp lval _ (pushLCtxsDep lctxTerm (dfLCtxTerm _))).down

abbrev LamEquiv (lval : LamValuation) (lctx : Nat → LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∃ (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, rty⟩),
  ∃ (wf₂ : LamWF lval.toLamTyVal ⟨lctx, t₂, rty⟩),
    ∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal),
      LamWF.interp lval lctx lctxTerm wf₁ =
        LamWF.interp lval lctx lctxTerm wf₂

def LamThmEquiv (lval : LamValuation) (lctx : List LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamEquiv lval (pushLCtxs lctx lctx') rty t₁ t₂

theorem LamValid_substLCtxRecWF
  (lctx' : Nat → LamSort) (heq : ∀ n, lctx' n = lctx n)
  {lval : LamValuation} {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal), GLift.down (LamWF.interp lval lctx lctxTerm wf)) ↔
  (∀ (lctxTerm' : ∀ n, (lctx' n).interp lval.tyVal),
    GLift.down (LamWF.interp (t:=t) (rty:=.base .prop) lval lctx' lctxTerm' ((@id (lctx' = lctx) (funext heq)) ▸ wf))) := by
  cases (@id (lctx' = lctx) (funext heq)); exact Iff.intro id id

theorem LamWF.ofExistsLamWF (H : ∃ (_ : LamWF ltv ⟨lctx, t, s⟩), p) :
  LamWF ltv ⟨lctx, t, s⟩ := by
  apply LamWF.ofNonemptyLamWF; cases H; apply Nonempty.intro; assumption

theorem LamThmWF.ofLamThmWFP (H : LamThmWFP lval lctx s t) :
  LamThmWF lval lctx s t := by
  intro lctx'; apply LamWF.ofNonemptyLamWF (H lctx')

theorem LamThmWFP.ofLamThmWF (H : LamThmWF lval lctx s t) :
  LamThmWFP lval lctx s t :=
  fun lctx => Nonempty.intro (H lctx)

def LamTerm.lamThmWFCheck? (ltv : LamTyVal) (lctx : List LamSort) (t : LamTerm) : Option LamSort :=
  match LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t with
  | .some s =>
    match Nat.ble (t.maxLooseBVarSucc) lctx.length with
    | true => .some s
    | false => .none
  | .none => .none

theorem LamTerm.lamThmWFCheck?_spec
  (H : LamTerm.lamThmWFCheck? ltv lctx t = .some rty) :
  LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t = .some rty ∧ t.maxLooseBVarSucc ≤ lctx.length := by
  dsimp [lamThmWFCheck?] at H; revert H
  match LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t with
  | .some s =>
    dsimp
    match h₂ : Nat.ble t.maxLooseBVarSucc lctx.length with
    | true => dsimp; intro H; apply And.intro H; apply Nat.le_of_ble_eq_true h₂
    | false => intro H; cases H
  | .none => intro H; cases H

theorem LamThmWF.ofLamThmWFCheck?
  {lval : LamValuation} {lctx : List LamSort} {rty : LamSort} {t : LamTerm}
  (h : LamTerm.lamThmWFCheck? lval.toLamTyVal lctx t = .some rty) : LamThmWF lval lctx rty t := by
  revert h; dsimp [LamTerm.lamThmWFCheck?]
  match h₁ : LamTerm.lamCheck? lval.toLamTyVal (pushLCtxs lctx dfLCtxTy) t with
  | .some s =>
    dsimp
    match h₂ : Nat.ble (LamTerm.maxLooseBVarSucc t) (List.length lctx) with
    | true =>
      intros h lctx'; cases h; apply LamWF.ofLamCheck?; apply Eq.trans _ h₁
      apply LamTerm.lamCheck?_irrelevence; intro n hlt; dsimp [pushLCtxs]
      have hlt' : n < List.length lctx := Nat.le_trans hlt (Nat.ble_eq ▸ h₂)
      have htrue : Nat.blt n (List.length lctx) = true := by
        rw [Nat.blt_eq]; exact hlt'
      rw [htrue]; dsimp;
      rw [List.getD_eq_get _ _ hlt']; rw [List.getD_eq_get _ _ hlt']
    | false => intro h; cases h
  | .none => intro h; cases h

theorem LamThmWF.ofLamThmValid (H : LamThmValid lval lctx t) :
  LamThmWF lval lctx (.base .prop) t :=
  LamThmWF.ofLamThmWFP (fun lctx => let ⟨wf, _⟩ := H lctx; Nonempty.intro wf)

theorem LamThmWF.maxLooseBVarSucc (H : LamThmWF lval lctx rty t) :
  t.maxLooseBVarSucc ≤ lctx.length := by
  induction t generalizing lctx rty <;> try apply Nat.zero_le
  case bvar n =>
    dsimp [LamTerm.maxLooseBVarSucc]
    have H₁ := H (fun _ => .base .prop)
    have heq₁ : rty = pushLCtxs lctx (fun _ => LamSort.base LamBaseSort.prop) n := by cases H₁; rfl
    have H₂ := H (fun _ => .func (.base .prop) (.base .prop))
    have heq₂ : rty = pushLCtxs lctx (fun _ => .func (.base .prop) (.base .prop)) n := by cases H₂; rfl
    rw [heq₂] at heq₁; revert heq₁; dsimp [pushLCtxs]
    match h : Nat.blt n lctx.length with
    | true => intro _; dsimp [Nat.blt] at h; apply Nat.le_of_ble_eq_true h
    | false => dsimp; intro H; cases H
  case lam s body IH =>
    dsimp [LamTerm.maxLooseBVarSucc]
    apply Nat.pred_le_pred (m:=.succ _);
    have Htmp := H (fun _ => .base .prop); cases Htmp;
    case ofLam bodyTy H' =>
      clear H'
      apply IH (lctx:=s::lctx) (rty := bodyTy)
      intro lctx'; have H' := H lctx'; cases H'
      case ofLam HBody =>
        rw [pushLCtxs_cons]; exact HBody
  case app s fn arg IHFn IHArg =>
    dsimp [LamTerm.maxLooseBVarSucc]; rw [Nat.max_le]; apply And.intro
    case left =>
      apply IHFn (rty:=.func s rty); intro lctx'
      cases (H lctx'); assumption
    case right =>
      apply IHArg (rty:=s); intro lctx'
      cases (H lctx'); assumption

theorem LamThmValid.maxLooseBVarSucc (H : LamThmValid lval lctx t) :
  t.maxLooseBVarSucc ≤ lctx.length := LamThmWF.maxLooseBVarSucc (LamThmWF.ofLamThmValid H)

theorem LamThmWFD.ofLamThmWF (H : LamThmWF lval lctx rty t) : LamThmWFD lval lctx rty t := by
  exists (H dfLCtxTy); apply LamThmWF.maxLooseBVarSucc H

theorem LamThmWF.ofLamThmWFD (H : LamThmWFD lval lctx rty t) : LamThmWF lval lctx rty t := by
  apply LamThmWF.ofLamThmWFP; have ⟨H, hSucc⟩ := H; apply LamThmWFP.ofLamThmWF
  intro lctx'; apply LamWF.lctxIrrelevance _ H; intros n hlt
  dsimp [pushLCtxs];
  have hlt : n < List.length lctx := Nat.le_trans hlt hSucc
  have hblt : Nat.blt n (List.length lctx) = true := Nat.ble_eq_true_of_le hlt
  rw [hblt]; dsimp; rw [List.getD_eq_get _ _ hlt, List.getD_eq_get _ _ hlt]

theorem LamValid.eVarIrrelevance
  (lval₁ : LamValuation.{u}) (lval₂ : LamValuation.{u})
  {lctxTy₁ lctxTy₂ : Nat → LamSort} {t : LamTerm}
  (hLamVarTy : lval₁.lamVarTy = lval₂.lamVarTy)
  (hLamILTy : lval₁.lamILTy = lval₂.lamILTy)
  (hTyVal : HEq lval₁.tyVal lval₂.tyVal)
  (hVarVal : HEq lval₁.varVal lval₂.varVal)
  (hILVal : HEq lval₁.ilVal lval₂.ilVal)
  (hLCtxTy : lctxTy₁ = lctxTy₂)
  (hirr : ∀ n, n < t.maxEVarSucc →
    lval₁.lamEVarTy n = lval₂.lamEVarTy n ∧ HEq (lval₁.eVarVal n) (lval₂.eVarVal n))
  (hValid : LamValid lval₁ lctxTy₁ t) : LamValid lval₂ lctxTy₂ t := by
  have ⟨wfv, hv⟩ := hValid
  have irr := fun eq₁ eq₂ => LamWF.eVarIrrelevance eq₁ eq₂ (fun n H => (hirr n H).left) wfv
  rcases lval₁ with ⟨⟨lamVarTy₁, lamILTy₁, lamEVarTy₁⟩, tyVal₁, varVal₁, ilVal₁, eVarVal₁⟩
  rcases lval₂ with ⟨⟨lamVarTy₂, lamILTy₂, lamEVarTy₂⟩, tyVal₂, varVal₂, ilVal₂, eVarVal₂⟩
  dsimp at hLamVarTy hLamILTy hTyVal hVarVal hILVal hirr irr
  cases hLamVarTy; cases hLamILTy; cases hTyVal
  cases hVarVal; cases hILVal; cases hLCtxTy
  exists (irr rfl rfl); intro lctxTerm;
  apply Eq.mp _ (hv lctxTerm); apply congrArg
  apply eq_of_heq; apply LamWF.interp_eVarIrrelevance <;> try rfl
  apply hirr

theorem LamThmValidD.ofLamThmValid (H : LamThmValid lval lctx t) :
  LamThmValidD lval lctx t := by
  have hSucc := LamThmValid.maxLooseBVarSucc H
  apply And.intro hSucc
  have ⟨wft, ht⟩ := H dfLCtxTy; exists wft
  intro lctxTerm; apply Eq.mp _ (ht (pushLCtxsDep lctxTerm (dfLCtxTerm lval.tyVal)))
  apply congrArg; apply eq_of_heq; apply LamWF.interp_heq <;> rfl

theorem LamThmValid.ofLamThmValidD (H : LamThmValidD lval lctx t) :
  LamThmValid lval lctx t := by
  have ⟨hSucc, ⟨wft, ht⟩⟩ := H; intro lctx'
  have hirr : ∀ (n : Nat), n < LamTerm.maxLooseBVarSucc t → pushLCtxs lctx dfLCtxTy n = pushLCtxs lctx lctx' n := by
    intros n hlt; dsimp [pushLCtxs]
    have hlt : n < List.length lctx := Nat.le_trans hlt hSucc
    have hblt : Nat.blt n (List.length lctx) = true := Nat.ble_eq_true_of_le hlt
    rw [hblt]; dsimp; rw [List.getD_eq_get _ _ hlt, List.getD_eq_get _ _ hlt]
  exists (LamWF.lctxIrrelevance hirr wft); intro lctxTerm;
  let hlist := HList.ofFun lctxTerm lctx.length
  apply Eq.mp _ (ht (Eq.mp (by rw [ofFun_pushs rfl]) hlist))
  apply congrArg; apply eq_of_heq; apply LamWF.interp_lctxIrrelevance
  intros n hlt; apply And.intro (hirr n hlt)
  have hlt : n < List.length lctx := Nat.le_trans hlt hSucc
  apply HEq.trans (pushLCtxsDep_lt _ hlt)
  apply HEq.trans (b:=HList.getD (dfLCtxTerm lval.tyVal 0) hlist n)
  case h₁ =>
    apply HList.getD_heq <;> try rfl
    case htys => rw [ofFun_pushs]; rfl
    case hhl => apply eqRec_heq'
  case h₂ =>
    dsimp; apply HList.ofFun_getD_eq_some _ _ _ hlt

theorem LamThmValid.eVarIrrelevance
  (lval₁ : LamValuation.{u}) (lval₂ : LamValuation.{u})
  {lctx₁ lctx₂ : List LamSort} {t : LamTerm}
  (hLamVarTy : lval₁.lamVarTy = lval₂.lamVarTy)
  (hLamILTy : lval₁.lamILTy = lval₂.lamILTy)
  (hTyVal : HEq lval₁.tyVal lval₂.tyVal)
  (hVarVal : HEq lval₁.varVal lval₂.varVal)
  (hILVal : HEq lval₁.ilVal lval₂.ilVal)
  (hLCtxTy : lctx₁ = lctx₂)
  (hirr : ∀ n, n < t.maxEVarSucc →
    lval₁.lamEVarTy n = lval₂.lamEVarTy n ∧ HEq (lval₁.eVarVal n) (lval₂.eVarVal n)) :
  LamThmValid lval₁ lctx₁ t → LamThmValid lval₂ lctx₂ t :=
  fun h lctx' => LamValid.eVarIrrelevance lval₁ lval₂
    (lctxTy₁:=pushLCtxs lctx₁ lctx') (lctxTy₂:=pushLCtxs lctx₂ lctx')
    hLamVarTy hLamILTy hTyVal hVarVal hILVal
    (by rw [hLCtxTy]) hirr (h lctx')

theorem LamThmWF.ofLamThmEquiv_l (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₁ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨wf, _⟩ := teq lctx'; ⟨wf⟩))

theorem LamThmWF.ofLamThmEquiv_r (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₂ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨_, ⟨wf, _⟩⟩ := teq lctx'; ⟨wf⟩))

theorem LamValid.ofLamEquiv
  (leq : LamEquiv lval lctx s t₁ t₂) : LamValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  let ⟨wf₁, ⟨wf₂, h₁₂⟩⟩ := leq; ⟨LamWF.mkEq wf₁ wf₂, h₁₂⟩

theorem LamThmValid.ofLamThmEquiv
  {lval : LamValuation} (lctx : List LamSort)
  (eT : LamThmEquiv lval lctx s t₁ t₂) :
  LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) := fun lctx' => LamValid.ofLamEquiv (eT lctx')

def LamThmWF.append (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (lctx ++ ex) rty t := by
  dsimp [LamThmWF]; intros lctx'; rw [pushLCtxs_append]; apply H

def LamThmWF.prepend (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (ex ++ lctx) rty (t.bvarLifts ex.length) := by
  dsimp [LamThmWF]; intros lctx';
  rw [pushLCtxs_append]; rw [← pushLCtxsAt_zero ex]
  apply LamWF.ofBVarLiftsIdx (idx:=0); rfl; apply H

theorem LamValid.revert1F (H : LamValid lval (pushLCtx s lctx) t) : LamValid lval lctx (.mkForallEF s t) :=
  have ⟨wft, ht⟩ := H
  ⟨LamWF.mkForallEF wft, fun lctxTerm x => ht (pushLCtxDep x lctxTerm)⟩

theorem LamThmValid.revert1F (H : LamThmValid lval (s :: lctx) t) : LamThmValid lval lctx (.mkForallEF s t) := by
  intro lctx'; have H' := H lctx'; rw [pushLCtxs_cons] at H'; apply H'.revert1F

theorem LamValid.intro1F (H : LamValid lval lctx (.mkForallEF s t)) : LamValid lval (pushLCtx s lctx) t :=
  have ⟨.ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ HBody), ht⟩ := H
  ⟨HBody, fun lctxTerm => by
    have ht' := ht (fun n => lctxTerm (.succ n)) (lctxTerm 0)
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp] at ht';
    apply Eq.mp _ ht'; apply congrArg;
    apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
    apply HEq.funext; intro n; cases n <;> rfl⟩

theorem LamThmValid.intro1F (H : LamThmValid lval lctx (.mkForallEF s t)) : LamThmValid lval (s :: lctx) t := by
  intro lctx'; rw [pushLCtxs_cons]; apply LamValid.intro1F; apply H

theorem LamValid.eqForallEF : LamValid lval lctx (.mkForallEF s t) ↔ LamValid lval (pushLCtx s lctx) t :=
  Iff.intro LamValid.intro1F LamValid.revert1F

theorem LamThmValid.eqForallEF : LamThmValid lval lctx (.mkForallEF s t) ↔ LamThmValid lval (s :: lctx) t :=
  Iff.intro LamThmValid.intro1F LamThmValid.revert1F

theorem LamWF.interp_eqForallEH
  {wf : LamWF lval.toLamTyVal ⟨lctx, t, .func argTy (.base .prop)⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallE wf)) = (∀ x,
    GLift.down (LamWF.interp lval (pushLCtx argTy lctx) (pushLCtxDep x lctxTerm) (.ofApp _ wf.ofBVarLift .pushLCtx_ofBVar))) := by
  dsimp [interp, LamBaseTerm.LamWF.interp, forallLiftFn]
  conv => enter [2, x, 1]; rw [← interp_ofBVarLift]

theorem LamValid.revert1H (H : LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0))) :
  LamValid lval lctx (.mkForallE s t) :=
  have ⟨wfAp, ht⟩ := LamValid.revert1F H
  have .ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ (.ofApp _ wft (.ofBVar _))) := wfAp
  ⟨LamWF.mkForallE (.fromBVarLift _ wft), fun lctxTerm => by
    dsimp [LamWF.mkForallE, LamWF.interp, LamBaseTerm.LamWF.interp]; intro x
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, forallLiftFn] at ht
    apply Eq.mp _ (ht lctxTerm x); apply congrArg; apply congrFun
    apply Eq.trans (b := LamWF.interp lval (pushLCtx s lctx) (pushLCtxDep x lctxTerm)
      (.ofBVarLift _ (.fromBVarLift _ wft)))
    case h₁ => apply eq_of_heq; apply LamWF.interp_heq <;> rfl
    case h₂ => rw [← LamWF.interp_ofBVarLift]⟩

theorem LamThmValid.revert1H (H : LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0))) :
  LamThmValid lval lctx (.mkForallE s t) := by
  intro lctx'; have H' := H lctx'; rw [pushLCtxs_cons] at H'; apply LamValid.revert1H H'

theorem LamValid.intro1H (H : LamValid lval lctx (.mkForallE s t)) :
  LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  LamValid.intro1F (
    have ⟨wfF, hF⟩ := H
    have .ofApp _ (.ofBase (.ofForallE _)) wft := wfF
    ⟨.mkForallEF (.ofApp _ (.ofBVarLift _ wft) .pushLCtx_ofBVar), fun lctxTerm => by
      dsimp [LamWF.mkForallEF, LamWF.interp, LamBaseTerm.LamWF.interp]; intro x; dsimp
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, forallLiftFn] at hF
      apply Eq.mp _ (hF lctxTerm x); apply congrArg; rw [← LamWF.interp_ofBVarLift]⟩
  )

theorem LamThmValid.intro1H (H : LamThmValid lval lctx (.mkForallE s t)) :
  LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0)) := by
  intro lctx'; rw [pushLCtxs_cons]; apply LamValid.intro1H (H lctx')

theorem LamValid.eqForallEH : LamValid lval lctx (.mkForallE s t) ↔ LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  Iff.intro LamValid.intro1H LamValid.revert1H

theorem LamThmValid.eqForallEH : LamThmValid lval lctx (.mkForallE s t) ↔ LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0)) :=
  Iff.intro LamThmValid.intro1H LamThmValid.revert1H

theorem LamValid.eqForallEFN : LamValid lval lctx (.mkForallEFN t l) ↔ LamValid lval (pushLCtxs l lctx) t := by
  induction l generalizing t
  case nil => rw [pushLCtxs_nil]; rfl
  case cons s l IH =>
    dsimp [LamTerm.mkForallEFN]; rw [pushLCtxs_cons]
    rw [IH, ← LamValid.eqForallEF]

theorem LamThmValid.eqForallEFN : LamThmValid lval lctx (.mkForallEFN t l) ↔ LamThmValid lval (l ++ lctx) t :=
  Iff.intro
    (fun H lctx' => by rw [pushLCtxs_append]; exact LamValid.eqForallEFN.mp (H lctx'))
    (fun H lctx' => have H' := H lctx'; by rw [pushLCtxs_append] at H'; exact LamValid.eqForallEFN.mpr H')

theorem LamThmValid.append (H : LamThmValid lval lctx t)
  (ex : List LamSort) : LamThmValid lval (lctx ++ ex) t := by
  dsimp [LamThmValid]; intros lctx'; rw [pushLCtxs_append]; exact H (pushLCtxs ex lctx')

theorem LamValid.prepend (H : LamValid lval lctx t)
  (ex : List LamSort) : LamValid lval (pushLCtxs ex lctx) (t.bvarLifts ex.length) := by
  have ⟨wft, ht⟩ := H
  rw [← pushLCtxsAt_zero ex]; exists (LamWF.ofBVarLiftsIdx rfl _ wft)
  intro lctxTerm;
  let lctxTerm₁ := fun n => lctxTerm (n + ex.length)
  have lctxeq : ∀ (n : Nat), pushLCtxsAt ex 0 lctx (n + List.length ex) = lctx n := by
    intro n; rw [pushLCtxsAt_zero, pushLCtxs_ge, Nat.add_sub_cancel]; apply Nat.le_add_left
  have ht' := (LamValid_substLCtxRecWF _ lctxeq).mp ht lctxTerm₁
  apply Eq.mp _ ht'; apply congrArg
  let hl' : HList (LamSort.interp lval.tyVal) ex := by
    apply Eq.mp _ (HList.ofFun lctxTerm ex.length)
    rw [pushLCtxsAt_zero, List.ofFun_ofPushLCtx]; rfl
  apply Eq.trans (@LamWF.interp_ofBVarLiftsIdx _ _ 0 _ ex hl' rfl _ lctxTerm₁ _ _) _
  apply LamWF.interp_substLCtxTerm
  case HLCtxTermEq =>
    apply HEq.trans (HEq.trans (pushLCtxsAtDep_zero _ _) ?eq') (pushsDep_popsDep_eq (lvl:=ex.length) _)
    apply pushLCtxsDep_heq <;> try rfl
    case h₃ => rw [pushLCtxsAt_zero]; rw [List.ofFun_ofPushLCtx]; rfl
    case h₄ => apply cast_heq
  case HLCtxTyEq =>
    apply congrArg; apply funext lctxeq

theorem LamThmValid.prepend (H : LamThmValid lval lctx t)
  (ex : List LamSort) : LamThmValid lval (ex ++ lctx) (t.bvarLifts ex.length) :=
  fun lctx' => pushLCtxs_append _ _ _ ▸ LamValid.prepend (H lctx') ex

theorem LamEquiv.ofLamValid
  (heq : LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamEquiv lval lctx s t₁ t₂ :=
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq
  ⟨wft₁, ⟨wft₂, heq'⟩⟩ 

theorem LamEquiv.ofLamValidSymm
  (heq : LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamEquiv lval lctx s t₂ t₁ :=
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq
  ⟨wft₂, wft₁, fun _ => Eq.symm (heq' _)⟩

theorem LamThmEquiv.ofLamThmValid
  {lval : LamValuation} (lctx : List LamSort)
  (heq : LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamThmEquiv lval lctx s t₁ t₂ :=
  fun lctx' => LamEquiv.ofLamValid (heq lctx')

theorem LamEquiv.eqLamValid :
  LamEquiv lval lctx s t₁ t₂ = (LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :=
  propext (Iff.intro LamValid.ofLamEquiv LamEquiv.ofLamValid)

theorem LamThmEquiv.eqLamThmValid
  {lval : LamValuation} (lctx : List LamSort) :
  LamThmEquiv lval lctx s t₁ t₂ = LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  propext (Iff.intro (LamThmValid.ofLamThmEquiv _) (LamThmEquiv.ofLamThmValid _))

theorem LamValid.mpLamEquiv (hp : LamValid lval lctx p₁)
  (hequiv : LamEquiv lval lctx s p₁ p₂) : LamValid lval lctx p₂ := by
  let ⟨wfp₁, hp₁⟩ := hp
  let ⟨wfp₁', ⟨wfp₂, heqp⟩⟩ := hequiv
  rcases LamWF.unique wfp₁ wfp₁' with ⟨⟨⟩, ⟨⟩⟩
  exact ⟨wfp₂, fun lctxTerm' => heqp _ ▸ hp₁ lctxTerm'⟩

theorem LamThmValid.mpLamThmEquiv
  {lval : LamValuation} (lctx : List LamSort)
  (hequiv : LamThmEquiv lval lctx (.base .prop) p₁ p₂)
  (hp : LamThmValid lval lctx p₁) : LamThmValid lval lctx p₂ := by
  intros lctx';
  let ⟨wfp₁, ⟨wfp₂, heqp⟩⟩ := hequiv lctx'
  exists wfp₂; intro lctxTerm'; rw [← heqp]
  let ⟨wfp₁', hp₁⟩ := hp lctx'
  have wfeq : wfp₁ = wfp₁' := eq_of_heq (LamWF.unique wfp₁ wfp₁').right
  cases wfeq; apply hp₁

theorem LamEquiv.refl {lval : LamValuation} (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t t := ⟨wf, ⟨wf, fun _ => rfl⟩⟩

theorem LamThmEquiv.refl {lval : LamValuation} (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t := fun lctx' => LamEquiv.refl (wf lctx')

theorem LamEquiv.eq {lval : LamValuation} (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩)
  (heq : t₁ = t₂) : LamEquiv lval lctx s t₁ t₂ := heq ▸ LamEquiv.refl wf

theorem LamThmEquiv.eq {lval : LamValuation} (wf : LamThmWF lval lctx s t₁)
  (heq : t₁ = t₂) : LamThmEquiv lval lctx s t₁ t₂ := fun lctx => LamEquiv.eq (wf lctx) heq

theorem LamEquiv.symm {lval : LamValuation} (e : LamEquiv lval lctx s a b) : LamEquiv lval lctx s b a :=
  let ⟨wfa, ⟨wfb, eq⟩⟩ := e; ⟨wfb, ⟨wfa, fun lctxTerm => Eq.symm (eq lctxTerm)⟩⟩

theorem LamThmEquiv.symm {lval : LamValuation} (e : LamThmEquiv lval lctx rty a b) :
  LamThmEquiv lval lctx rty b a := fun lctx => LamEquiv.symm (e lctx)

theorem LamEquiv.trans {lval : LamValuation}
  (eab : LamEquiv lval lctx s a b) (ebc : LamEquiv lval lctx s b c) : LamEquiv lval lctx s a c := by
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := eab; let ⟨wfb', ⟨wfc, eqbc⟩⟩ := ebc
  rcases LamWF.unique wfb wfb' with ⟨_, ⟨⟩⟩
  exact ⟨wfa, ⟨wfc, fun lctxTerm => by rw [eqab, ←eqbc]⟩⟩

theorem LamEquiv.trans' {lval : LamValuation}
  (eab : LamEquiv lval lctx s a b) (ebc : LamEquiv lval lctx s' b c) : LamEquiv lval lctx s a c := by
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := eab; let ⟨wfb', ⟨wfc, eqbc⟩⟩ := ebc
  rcases LamWF.unique wfb wfb' with ⟨⟨⟩, ⟨⟩⟩
  exact ⟨wfa, ⟨wfc, fun lctxTerm => by rw [eqab, ←eqbc]⟩⟩

theorem LamThmEquiv.trans
  (e₁ : LamThmEquiv lval lctx rty a b) (e₂ : LamThmEquiv lval lctx rty b c) :
  LamThmEquiv lval lctx rty a c :=
  fun lctx' => LamEquiv.trans (e₁ lctx') (e₂ lctx')

theorem LamEquiv.ofLam {lval : LamValuation} (e : LamEquiv lval (pushLCtx w lctx) s a b) :
  LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := e; ⟨.ofLam _ wfa, .ofLam _ wfb, fun _ => funext (fun _ => eqab _)⟩

theorem LamThmEquiv.ofLam (e : LamThmEquiv lval (w :: lctx) s a b) :
  LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) := fun lctx' =>
    LamEquiv.ofLam (pushLCtxs_cons _ _ ▸ e lctx')

theorem LamEquiv.fromLam
  (e : LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamEquiv lval (pushLCtx w lctx) s a b :=
  let ⟨.ofLam _ wfa, .ofLam _ wfb, eqlab⟩ := e
  ⟨wfa, wfb, fun lctxTerm =>
    let h := congrFun (eqlab (fun n => lctxTerm (.succ n))) (lctxTerm 0)
    by
      dsimp [LamWF.interp] at h
      apply Eq.trans ?left (Eq.trans h ?right) <;>
        apply eq_of_heq
      case left =>
        apply LamWF.interp_heq <;> try rfl
        apply HEq.symm; apply pushDep_popDep_eq lctxTerm
      case right =>
        apply LamWF.interp_heq <;> try rfl
        apply pushDep_popDep_eq⟩

theorem LamThmEquiv.fromLam {lval : LamValuation}
  (e : LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamThmEquiv lval (w :: lctx) s a b := fun lctx' => by
  rw [pushLCtxs_cons]; apply LamEquiv.fromLam (e lctx')

theorem LamEquiv.eqLam :
  LamEquiv lval (pushLCtx w lctx) s a b = LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro LamEquiv.ofLam LamEquiv.fromLam)

theorem LamThmEquiv.eqLam {lval : LamValuation} :
  LamThmEquiv lval (w :: lctx) s a b = LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro LamThmEquiv.ofLam LamThmEquiv.fromLam)

theorem LamEquiv.congr
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) :=
  let ⟨wfFn₁, wfFn₂, HFn⟩ := eFn
  let ⟨wfArg₁, wfArg₂, HArg⟩ := eArg
  ⟨.ofApp _ wfFn₁ wfArg₁, .ofApp _ wfFn₂ wfArg₂, fun _ => _root_.congr (HFn _) (HArg _)⟩

theorem LamThmEquiv.congr {lval : LamValuation}
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := fun lctx' =>
    LamEquiv.congr (eFn lctx') (eArg lctx')

theorem LamEquiv.congrFun
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamEquiv.congr eFn (LamEquiv.refl wfArg)

theorem LamThmEquiv.congrFun {lval : LamValuation}
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamThmWF lval lctx argTy arg) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamThmEquiv.congr eFn (LamThmEquiv.refl wfArg)

theorem LamEquiv.congrArg
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn, .func argTy resTy⟩)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamEquiv.congr (LamEquiv.refl wfFn) eArg

theorem LamThmEquiv.congrArg {lval : LamValuation}
  (wfFn : LamThmWF lval lctx (.func argTy resTy) fn)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamThmEquiv.congr (LamThmEquiv.refl wfFn) eArg

theorem LamEquiv.congr_mkLamFN :
  LamEquiv lval (pushLCtxs l lctx) s t₁ t₂ ↔ LamEquiv lval lctx (s.mkFuncsRev l) (.mkLamFN t₁ l) (.mkLamFN t₂ l) := by
  induction l generalizing t₁ t₂ s
  case nil => exact Iff.intro id id
  case cons ls l IH =>
    dsimp [LamTerm.mkLamFN, LamWF.mkLamFN]; apply Iff.trans _ IH
    apply Iff.intro
    case mp =>
      intro H; apply LamEquiv.ofLam; apply Eq.mp _ H
      rw [pushLCtxs_cons]
    case mpr =>
      intro H; rw [pushLCtxs_cons]
      apply LamEquiv.fromLam; apply H

theorem LamEquiv.congrs {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hFn : LamEquiv lval lctx fnTy fn₁ fn₂)
  (hArgs : HList ((fun (s, arg₁, arg₂) => LamEquiv lval lctx s arg₁ arg₂)) args) :
  LamEquiv lval lctx resTy
    (LamTerm.mkAppN fn₁ (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn₂ (args.map (fun (s, _, t₂) => (s, t₂)))) := by
  induction args generalizing fn₁ fn₂ fnTy
  case nil =>
    have ⟨wfFn, _⟩ := hFn
    rcases LamWF.unique wfFn wfApp with ⟨⟨⟩, ⟨⟩⟩; apply hFn
  case cons head tail IH =>
    match head with
    | ⟨s, t₁, t₂⟩ =>
      have ⟨wfFn, _⟩ := hFn
      have ⟨fnTy', wfAp⟩ := LamWF.generalizeTy
        (wfApp.fnWFOfMkAppN (args:=tail.map (fun (s, t₁, snd) => (s, t₁))))
      rcases LamWF.unique wfFn wfAp.getFn with ⟨⟨⟩, ⟨⟩⟩
      apply IH wfApp (fnTy:=fnTy'); dsimp [LamTerm.mkAppN] at wfApp
      case hFn =>
        apply LamEquiv.congr hFn
        match hArgs with
        | .cons hHead _ => apply hHead
      case hArgs =>
        match hArgs with
        | .cons _ hTail => apply hTail

theorem LamEquiv.congrArgs {lval : LamValuation} {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hArgs : HList ((fun (s, arg₁, arg₂) => LamEquiv lval lctx s arg₁ arg₂)) args) :
  LamEquiv lval lctx resTy
    (LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn (args.map (fun (s, _, t₂) => (s, t₂))))
   := LamEquiv.congrs wfApp (LamEquiv.refl wfApp.fnWFOfMkAppN) hArgs

theorem LamEquiv.congrFunN {lval : LamValuation} {args : List (LamSort × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn₁ args, resTy⟩)
  (hFn : LamEquiv lval lctx fnTy fn₁ fn₂) :
  LamEquiv lval lctx resTy (LamTerm.mkAppN fn₁ args) (LamTerm.mkAppN fn₂ args) := by
  let masterArr := args.map (fun (s, arg) => (s, arg, arg))
  have eq₁ : args = masterArr.map (fun (s, arg₁, _) => (s, arg₁)) := by
    rw [List.map_map]; rw [List.map_equiv _ id, List.map_id];
    intro x; cases x; rfl
  have eq₂ : args = masterArr.map (fun (s, _, arg₂) => (s, arg₂)) := by
    rw [List.map_map]; rw [List.map_equiv _ id, List.map_id];
    intro x; cases x; rfl
  have eqt₂ : LamTerm.mkAppN fn₂ args = LamTerm.mkAppN fn₂ (masterArr.map (fun (s, _, arg₂) => (s, arg₂))) := by
    rw [← eq₂]
  rw [eqt₂]; revert wfApp; rw [eq₁]; intro wfApp; apply LamEquiv.congrs wfApp hFn
  apply HList.toMapTy; dsimp [Function.comp]
  apply HList.map (β:=fun (s, t) => LamWF lval.toLamTyVal ⟨lctx, t, s⟩)
    (fun (s, t) => LamEquiv.refl (s:=s) (t:=t))
  have wfArgs := wfApp.argsWFOfMkAppN; rw [← eq₁] at wfArgs; exact wfArgs

theorem LamEquiv.forall_congr {lval : LamValuation}
  (eFn : LamEquiv lval (pushLCtx argTy lctx) (.base .prop) fn₁ fn₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEF argTy fn₁) (.mkForallEF argTy fn₂) := by
  have ⟨wfFn₁, wfFn₂, eqFn⟩ := eFn
  exists LamWF.mkForallEF wfFn₁, LamWF.mkForallEF wfFn₂; intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, forallLiftFn]
  apply _root_.congrArg; apply _root_.forall_congr; intro x
  apply _root_.congrArg; apply eqFn

theorem LamEquiv.congr_mkForallEFN
  (H : LamEquiv lval (pushLCtxs l lctx) (.base .prop) t₁ t₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEFN t₁ l) (.mkForallEFN t₂ l) := by
  induction l generalizing t₁ t₂
  case nil => exact H
  case cons ls l IH =>
    dsimp [LamTerm.mkForallEFN, LamWF.mkForallEFN]; apply IH
    apply LamEquiv.forall_congr; apply Eq.mp _ H
    rw [pushLCtxs_cons]

theorem LamValid.eq_refl {lval : LamValuation}
  (wfA : LamWF lval.toLamTyVal ⟨lctx, a, s⟩) : LamValid lval lctx (.mkEq s a a) := by
  exists (.mkEq wfA wfA); intro lctxTerm; rfl

theorem LamValid.eq_eq {lval : LamValuation} (heq : a = b)
  (wfA : LamWF lval.toLamTyVal ⟨lctx, a, s⟩) : LamValid lval lctx (.mkEq s a b) := by
  cases heq; apply LamValid.eq_refl wfA

theorem LamValid.eq_symm
  (H : LamValid lval lctx (.mkEq s a b)) :
  LamValid lval lctx (.mkEq s b a) := LamValid.ofLamEquiv (LamEquiv.symm (LamEquiv.ofLamValid H))

theorem LamValid.eq_trans
  (H₁ : LamValid lval lctx (.mkEq s a b))
  (H₂ : LamValid lval lctx (.mkEq s b c)) :
  LamValid lval lctx (.mkEq s a c) :=
  have heqab := LamEquiv.ofLamValid H₁
  have heqbc := LamEquiv.ofLamValid H₂
  LamValid.ofLamEquiv (LamEquiv.trans heqab heqbc)

theorem LamValid.eq_congr
  (HFn : LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂))
  (HArg : LamValid lval lctx (.mkEq argTy arg₁ arg₂)) :
  LamValid lval lctx (.mkEq resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂)) :=
  have heqFn := LamEquiv.ofLamValid HFn
  have heqArg := LamEquiv.ofLamValid HArg
  have heqAp := LamEquiv.congr heqFn heqArg
  LamValid.ofLamEquiv heqAp

theorem LamValid.eq_congrFun
  (HFn : LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂))
  (wfArg₁ : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamValid lval lctx (.mkEq resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg)) := by
  apply LamValid.eq_congr HFn; apply LamValid.eq_refl wfArg₁

theorem LamValid.eq_congrArg
  (HArg : LamValid lval lctx (.mkEq argTy arg₁ arg₂))
  (wfFn₁ : LamWF lval.toLamTyVal ⟨lctx, fn, .func argTy resTy⟩) :
  LamValid lval lctx (.mkEq resTy (.app argTy fn arg₁) (.app argTy fn arg₂)) := by
  apply LamValid.eq_congr _ HArg; apply LamValid.eq_refl wfFn₁

def LamWF.funext
  (wf : LamWF ltv ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, s⟩) :
  LamWF ltv ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), .base .prop⟩ :=
  let wflAp := LamWF.ofApp _ wf.getFn.getArg.ofBVarLift .pushLCtx_ofBVar
  let wfrAp := LamWF.ofApp _ wf.getArg.ofBVarLift .pushLCtx_ofBVar
  LamWF.mkEq wflAp wfrAp

def LamWF.ofFunext
  (wf : LamWF ltv ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), s⟩) :
  LamWF ltv ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, .base .prop⟩ :=
  let wfl := wf.getFn.getArg.getFn.fromBVarLift
  let wfr := wf.getArg.getFn.fromBVarLift
  LamWF.mkEq wfl wfr

theorem LamWF.interp_funext
  {wf₁ : LamWF lval.toLamTyVal ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, .base .prop⟩}
  {wf₂ : LamWF lval.toLamTyVal ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm wf₁) = (∀ (x : argTy.interp lval.tyVal),
    GLift.down (LamWF.interp lval (pushLCtx argTy lctx) (pushLCtxDep x lctxTerm) wf₂)) :=
  match wf₁ with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) HLhs) HRhs =>
    match wf₂ with
    | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) (.ofApp _ HLhs' (.ofBVar _))) (.ofApp _ HRhs' (.ofBVar _)) => by
      dsimp [interp, LamBaseTerm.LamWF.interp, eqLiftFn]
      rcases LamWF.unique HLhs' HLhs.ofBVarLift with ⟨⟨⟩, ⟨⟩⟩
      rcases LamWF.unique HRhs' HRhs.ofBVarLift with ⟨⟨⟩, ⟨⟩⟩
      apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h x; rw [← LamWF.interp_ofBVarLift, ← LamWF.interp_ofBVarLift, h]
      case mpr =>
        intro h; apply _root_.funext; intro x; have h' := h x
        rw [← LamWF.interp_ofBVarLift, ← LamWF.interp_ofBVarLift] at h'; exact h'


theorem LamEquiv.eqFunext {lval : LamValuation}
  (wfEq : LamWF lval.toLamTyVal ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, s⟩) :
  LamEquiv lval lctx s
    (.mkEq (.func argTy resTy) fn₁ fn₂)
    (.mkForallEF argTy (.mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)))) := by
  match wfEq with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wfFn₁) wfFn₂ =>
    let wfAp₁ := LamWF.ofApp _
      (LamWF.ofBVarLift (s:=argTy) _ wfFn₁) LamWF.pushLCtx_ofBVar
    let wfAp₂ := LamWF.ofApp _
      (LamWF.ofBVarLift (s:=argTy) _ wfFn₂) LamWF.pushLCtx_ofBVar
    exists LamWF.mkEq wfFn₁ wfFn₂, LamWF.mkForallEF (LamWF.mkEq wfAp₁ wfAp₂); intro lctxTerm
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, eqLiftFn, forallLiftFn]
    apply _root_.congrArg; apply propext (Iff.intro ?mp ?mpr)
    case mp =>
      intro hinterp h; rw [← LamWF.interp_ofBVarLift, ← LamWF.interp_ofBVarLift, hinterp]
    case mpr =>
      intro hinterp; apply funext; intro x; apply Eq.trans ?left (Eq.trans (hinterp x) ?right)
      case left => rw [← LamWF.interp_ofBVarLift]
      case right => rw [← LamWF.interp_ofBVarLift]

theorem LamEquiv.funext {lval : LamValuation}
  (eAp : LamEquiv lval (pushLCtx argTy lctx) resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0))) :
  LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂ := by
  have ⟨wfFnAp₁, wfFnAp₂, hFnAp⟩ := eAp
  apply LamEquiv.ofLamValid (s:=.func argTy resTy) _
  have hEqValid := LamValid.ofLamEquiv eAp
  apply LamValid.mpLamEquiv (s:=.base .prop) (LamValid.revert1F hEqValid)
  apply LamEquiv.symm; apply LamEquiv.eqFunext
  apply LamWF.mkEq wfFnAp₁.getFn.fromBVarLift wfFnAp₂.getFn.fromBVarLift

theorem LamValid.eqFunext
  {fn₁ fn₂ : LamTerm}
  (HApp : LamValid lval (pushLCtx argTy lctx) (.mkEq resTy
    (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)))) :
  LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂) :=
  have heqAp := LamEquiv.ofLamValid HApp
  have heqFn := LamEquiv.funext heqAp
  LamValid.ofLamEquiv heqFn

end Auto.Embedding.Lam