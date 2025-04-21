import Auto.Embedding.LamBVarOp

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
      LamWF.interp lval lctx lctxTerm wf₁ = LamWF.interp lval lctx lctxTerm wf₂

def LamThmEquiv (lval : LamValuation) (lctx : List LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamEquiv lval (pushLCtxs lctx lctx') rty t₁ t₂

def LamGenEquiv (lval : LamValuation) (t₁ t₂ : LamTerm) := ∀ (lctx : Nat → LamSort) (rty : LamSort),
  LamWF lval.toLamTyVal ⟨lctx, t₁, rty⟩ → LamEquiv lval lctx rty t₁ t₂

def LamGenEquivWith (lval : LamValuation) (rty : LamSort) (t₁ t₂ : LamTerm) :=
  ∀ (lctx : Nat → LamSort), LamWF lval.toLamTyVal ⟨lctx, t₁, rty⟩ → LamEquiv lval lctx rty t₁ t₂

/-- Generic conversions like clausification satisfy `LamGenConv` -/
def LamGenConv (lval : LamValuation) (conv : LamTerm → Option LamTerm) :=
  ∀ (t₁ t₂ : LamTerm), conv t₁ = .some t₂ → LamGenEquiv lval t₁ t₂

/-- Generic conversions like eta expansion satisfy `LamGenConvWith` -/
def LamGenConvWith (lval : LamValuation) (conv : LamSort → LamTerm → Option LamTerm) :=
  ∀ (rty : LamSort) (t₁ t₂ : LamTerm), conv rty t₁ = .some t₂ → LamGenEquivWith lval rty t₁ t₂

def LamGenModify (lval : LamValuation) (modify : LamTerm → Option LamTerm) (weaken? : Bool) :=
  ∀ (t₁ t₂ : LamTerm), modify t₁ = .some t₂ → ∀ (lctx : Nat → LamSort),
    LamWF lval.toLamTyVal ⟨lctx, t₁, .base .prop⟩ →
    match weaken? with
    | false => LamValid lval lctx (.mkImp t₂ t₁)
    | true => LamValid lval lctx (.mkImp t₁ t₂)

def LamTerm.getPos (occ : List Bool) (t : LamTerm) : Option LamTerm :=
  match occ with
  | .nil => t
  | .cons b occ =>
    match t with
    | .lam _ body => getPos occ body
    | .app _ fn arg =>
      match b with
      | false => getPos occ fn
      | true => getPos occ arg
    | _ => .none

/--
  Apply conversion theorem at a given position in `t`
  The conversion should only be ones that satisfy `LamGenConv`
-/
def LamTerm.rwGenAt (occ : List Bool) (conv : LamTerm → Option LamTerm) (t : LamTerm) : Option LamTerm :=
  match occ with
  | .nil => conv t
  | .cons b occ =>
    match t with
    | .lam s body => (rwGenAt occ conv body).bind (LamTerm.lam s ·)
    | .app s fn arg =>
      match b with
      | false => (rwGenAt occ conv fn).bind (LamTerm.app s · arg)
      | true => (rwGenAt occ conv arg).bind (LamTerm.app s fn ·)
    | _ => .none

-- **TODO:** This function always returns `.some`
def LamTerm.rwGenAll (conv : LamTerm → Option LamTerm) (t : LamTerm) : Option LamTerm :=
  match conv t with
  | .some t' => .some t'
  | .none =>
    match t with
    | .lam s body => (rwGenAll conv body).bind (LamTerm.lam s ·)
    | .app s fn arg =>
      match rwGenAll conv fn, rwGenAll conv arg with
      | .some fn', .some arg' => .some (.app s fn' arg')
      | _, _ => .none
    | _ => t

theorem LamTerm.rwGenAll_atom : rwGenAll conv (.atom n) = (conv (.atom n)).getD (.atom n) := by
  simp [rwGenAll]; cases conv (atom n) <;> rfl

theorem LamTerm.rwGenAll_etom : rwGenAll conv (.etom n) = (conv (.etom n)).getD (.etom n) := by
  simp [rwGenAll]; cases conv (etom n) <;> rfl

theorem LamTerm.rwGenAll_base : rwGenAll conv (.base b) = (conv (.base b)).getD (.base b) := by
  simp [rwGenAll]; cases conv (base b) <;> rfl

theorem LamTerm.rwGenAll_bvar : rwGenAll conv (.bvar n) = (conv (.bvar n)).getD (.bvar n) := by
  simp [rwGenAll]; cases conv (bvar n) <;> rfl

theorem LamTerm.rwGenAll_lam : rwGenAll conv (.lam s body) =
  match conv (.lam s body) with
  | .some t' => .some t'
  | .none => (rwGenAll conv body).bind (LamTerm.lam s ·) := by simp [rwGenAll]

theorem LamTerm.rwGenAll_app : rwGenAll conv (.app s fn arg) =
  match conv (.app s fn arg) with
  | .some t' => .some t'
  | .none =>
    match rwGenAll conv fn, rwGenAll conv arg with
    | .some fn', .some arg' => .some (.app s fn' arg')
    | _, _ => .none := by simp [rwGenAll]

def LamTerm.getPosWith (occ : List Bool) (rty : LamSort) (t : LamTerm) : Option (LamSort × LamTerm) :=
  match occ with
  | .nil => .some (rty, t)
  | .cons b occ =>
    match t with
    | .lam _ body =>
      match rty with
      | .func _ resTy => getPosWith occ resTy body
      | _ => .none
    | .app s fn arg =>
      match b with
      | false => getPosWith occ (.func s rty) fn
      | true => getPosWith occ s arg
    | _ => .none

/--
  Apply conversion theorem at a given position in `t`
  The conversion should only be ones that satisfy `LamGenConvWith`
-/
def LamTerm.rwGenAtWith (occ : List Bool) (conv : LamSort → LamTerm → Option LamTerm)
  (rty : LamSort) (t : LamTerm) : Option LamTerm :=
  match occ with
  | .nil => conv rty t
  | .cons b occ =>
    match t with
    | .lam s body =>
      match rty with
      | .func _ resTy => (rwGenAtWith occ conv resTy body).bind (LamTerm.lam s ·)
      | _ => .none
    | .app s fn arg =>
      match b with
      | false => (rwGenAtWith occ conv (.func s rty) fn).bind (LamTerm.app s · arg)
      | true => (rwGenAtWith occ conv s arg).bind (LamTerm.app s fn ·)
    | _ => .none

-- **TODO:** This function always returns `.some`
def LamTerm.rwGenAllWith (conv : LamSort → LamTerm → Option LamTerm)
  (rty : LamSort) (t : LamTerm) : Option LamTerm :=
  match conv rty t with
  | .some t' => .some t'
  | .none =>
    match t with
    | .lam s body =>
      match rty with
      | .func _ resTy => (rwGenAllWith conv resTy body).bind (LamTerm.lam s ·)
      | _ => .none
    | .app s fn arg =>
      match rwGenAllWith conv (.func s rty) fn, rwGenAllWith conv s arg with
      | .some fn', .some arg' => .some (.app s fn' arg')
      | _, _ => .none
    | _ => t

@[reducible] def LamTerm.evarEquiv (conv : LamTerm → Option LamTerm) :=
  ∀ t t', conv t = .some t' → t'.maxEVarSucc = t.maxEVarSucc

@[reducible] def LamTerm.evarBounded (conv : LamTerm → Option LamTerm) (bound : Nat) :=
  ∀ t t', conv t = .some t' → t'.maxEVarSucc ≤ max bound t.maxEVarSucc

theorem LamTerm.rwGenAllWith_atom : rwGenAllWith conv s (.atom n) = (conv s (.atom n)).getD (.atom n) := by
  simp [rwGenAllWith]; cases conv s (atom n) <;> rfl

theorem LamTerm.rwGenAllWith_etom : rwGenAllWith conv s (.etom n) = (conv s (.etom n)).getD (.etom n) := by
  simp [rwGenAllWith]; cases conv s (etom n) <;> rfl

theorem LamTerm.rwGenAllWith_base : rwGenAllWith conv s (.base b) = (conv s (.base b)).getD (.base b) := by
  simp [rwGenAllWith]; cases conv s (base b) <;> rfl

theorem LamTerm.rwGenAllWith_bvar : rwGenAllWith conv s (.bvar n) = (conv s (.bvar n)).getD (.bvar n) := by
  simp [rwGenAllWith]; cases conv s (bvar n) <;> rfl

theorem LamTerm.rwGenAllWith_lam : rwGenAllWith conv rty (.lam s body) =
  match conv rty (.lam s body) with
  | .some t' => .some t'
  | .none =>
    match rty with
    | .func _ resTy => (rwGenAllWith conv resTy body).bind (LamTerm.lam s ·)
    | _ => .none := by cases rty <;> simp [rwGenAllWith]

theorem LamTerm.rwGenAllWith_app : rwGenAllWith conv rty (.app s fn arg) =
  match conv rty (.app s fn arg) with
  | .some t' => .some t'
  | .none =>
    match rwGenAllWith conv (.func s rty) fn, rwGenAllWith conv s arg with
    | .some fn', .some arg' => .some (.app s fn' arg')
    | _, _ => .none := by simp [rwGenAllWith]

/-- Determine whether a position is negative / whether a position is positive -/
def LamTerm.isSign (sign : Bool) (occ : List Bool) (t : LamTerm) :=
  match occ with
  | .nil => sign
  | .cons b occ =>
    match t with
    | .app _ (.base .not) arg =>
      b && isSign (not sign) occ arg
    | .app _ (.app _ (.base .and) arg₁) arg₂ =>
      match b with
      | true => isSign sign occ arg₂
      | false =>
        match occ with
        | .nil => false
        | .cons b' occ => b' && isSign sign occ arg₁
    | .app _ (.app _ (.base .or) arg₁) arg₂ =>
      match b with
      | true => isSign sign occ arg₂
      | false =>
        match occ with
        | .nil => false
        | .cons b' occ => b' && isSign sign occ arg₁
    | .app _ (.app _ (.base .imp) arg₁) arg₂ =>
      match b with
      | true => isSign sign occ arg₂
      | false =>
        match occ with
        | .nil => false
        | .cons b' occ => b' && isSign (not sign) occ arg₁
    -- Args of `↔` are neither positive or negative
    | _ => false

def LamTerm.rwGenAtIfSign (sign : Bool) (occ : List Bool) (conv : LamTerm → Option LamTerm) (t : LamTerm) : Option LamTerm :=
  match LamTerm.isSign sign occ t with
  | true => rwGenAt occ conv t
  | false => .none

noncomputable def LamNonempty.get (h : LamNonempty tyVal s) : s.interp tyVal := Classical.choice h

theorem LamValid_substLCtxRecWF
  (lctx' : Nat → LamSort) (heq : ∀ n, lctx' n = lctx n)
  {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal), GLift.down (LamWF.interp lval lctx lctxTerm wf)) ↔
  (∀ (lctxTerm' : ∀ n, (lctx' n).interp lval.tyVal),
    GLift.down (LamWF.interp (t:=t) (rty:=.base .prop) lval lctx' lctxTerm' ((@id (lctx' = lctx) (funext heq)) ▸ wf))) := by
  cases (@id (lctx' = lctx) (funext heq)); exact Iff.intro id id

@[irreducible] def LamWF.ofExistsLamWF (H : ∃ (_ : LamWF ltv ⟨lctx, t, s⟩), p) :
  LamWF ltv ⟨lctx, t, s⟩ := by
  apply LamWF.ofNonemptyLamWF; cases H; apply Nonempty.intro; assumption

@[irreducible] def LamThmWF.ofLamThmWFP (H : LamThmWFP lval lctx s t) :
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

@[irreducible] def LamThmWF.ofLamThmWFCheck?
  {lctx : List LamSort} {rty : LamSort} {t : LamTerm}
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

@[irreducible] def LamThmWF.ofLamThmValid (H : LamThmValid lval lctx t) :
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

@[irreducible] def LamThmWF.ofLamThmWFD (H : LamThmWFD lval lctx rty t) : LamThmWF lval lctx rty t := by
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

@[irreducible] def LamThmWF.ofLamThmEquiv_l (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₁ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨wf, _⟩ := teq lctx'; ⟨wf⟩))

@[irreducible] def LamThmWF.ofLamThmEquiv_r (teq : LamThmEquiv lval lctx rty t₁ t₂) :
  LamThmWF lval lctx rty t₂ := LamThmWF.ofLamThmWFP (fun lctx' =>
    (let ⟨_, ⟨wf, _⟩⟩ := teq lctx'; ⟨wf⟩))

theorem LamValid.ofLamEquiv
  (leq : LamEquiv lval lctx s t₁ t₂) : LamValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  let ⟨wf₁, ⟨wf₂, h₁₂⟩⟩ := leq; ⟨LamWF.mkEq wf₁ wf₂, h₁₂⟩

theorem LamThmValid.ofLamThmEquiv
  (lctx : List LamSort)
  (eT : LamThmEquiv lval lctx s t₁ t₂) :
  LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) := fun lctx' => LamValid.ofLamEquiv (eT lctx')

def LamThmWF.append (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (lctx ++ ex) rty t := by
  dsimp [LamThmWF]; intros lctx'; rw [pushLCtxs_append]; apply H

def LamThmWF.prepend (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (ex ++ lctx) rty (t.bvarLifts ex.length) := by
  dsimp [LamThmWF]; intros lctx';
  rw [pushLCtxs_append]; rw [← pushLCtxsAt_zero ex]
  apply LamWF.bvarLiftsIdx (idx:=0); rfl; apply H

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
    GLift.down (LamWF.interp lval (pushLCtx argTy lctx) (pushLCtxDep x lctxTerm) (.ofApp _ wf.bvarLift .pushLCtx_ofBVar))) := by
  dsimp [interp, LamBaseTerm.LamWF.interp, LamTerm.mkForallE, mkForallE, forallLiftFn, pushLCtx_ofBVar]
  conv => enter [2, x, 1]; rw [← interp_bvarLift]

theorem LamValid.revert1H (H : LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0))) :
  LamValid lval lctx (.mkForallE s t) :=
  have ⟨wfAp, ht⟩ := LamValid.revert1F H
  have .ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ (.ofApp _ wft (.ofBVar _))) := wfAp
  ⟨LamWF.mkForallE (.fromBVarLift _ wft), fun lctxTerm => by
    dsimp [LamWF.mkForallE, LamTerm.mkForallE, LamWF.interp, LamBaseTerm.LamWF.interp]; intro x
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamTerm.mkForallEF, forallLiftFn] at ht
    apply Eq.mp _ (ht lctxTerm x); apply congrArg; apply congrFun
    apply Eq.trans (b := LamWF.interp lval (pushLCtx s lctx) (pushLCtxDep x lctxTerm)
      (.bvarLift _ (.fromBVarLift _ wft)))
    case h₁ => apply eq_of_heq; apply LamWF.interp_heq <;> rfl
    case h₂ => rw [← LamWF.interp_bvarLift]⟩

theorem LamThmValid.revert1H (H : LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0))) :
  LamThmValid lval lctx (.mkForallE s t) := by
  intro lctx'; have H' := H lctx'; rw [pushLCtxs_cons] at H'; apply LamValid.revert1H H'

theorem LamValid.intro1H (H : LamValid lval lctx (.mkForallE s t)) :
  LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  LamValid.intro1F (
    have ⟨wfF, hF⟩ := H
    have .ofApp _ (.ofBase (.ofForallE _)) wft := wfF
    ⟨.mkForallEF (.ofApp _ (.bvarLift _ wft) .pushLCtx_ofBVar), fun lctxTerm => by
      dsimp [LamWF.mkForallEF, LamWF.interp, LamBaseTerm.LamWF.interp]
      intro x; dsimp [LamWF.pushLCtx_ofBVar, LamWF.interp]
      apply Eq.mp _ (hF lctxTerm x); apply congrArg; rw [← LamWF.interp_bvarLift]⟩
  )

theorem LamThmValid.intro1H (H : LamThmValid lval lctx (.mkForallE s t)) :
  LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0)) := by
  intro lctx'; rw [pushLCtxs_cons]; apply LamValid.intro1H (H lctx')

theorem LamValid.eqForallEH : LamValid lval lctx (.mkForallE s t) ↔ LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  Iff.intro LamValid.intro1H LamValid.revert1H

theorem LamThmValid.eqForallEH : LamThmValid lval lctx (.mkForallE s t) ↔ LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0)) :=
  Iff.intro LamThmValid.intro1H LamThmValid.revert1H

theorem LamValid.eqForallEFN : LamValid lval lctx (.mkForallEFN t l) ↔ LamValid lval (pushLCtxs l.reverse lctx) t := by
  induction l generalizing t lctx
  case nil => rfl
  case cons s l IH =>
    dsimp [LamTerm.mkForallEFN]
    rw [List.reverse_cons, pushLCtxs_append_singleton]
    rw [← IH, ← LamValid.eqForallEF]

theorem LamValid.eqForallEFN' : LamValid lval lctx (.mkForallEFN t l.reverse) ↔ LamValid lval (pushLCtxs l lctx) t := by
  conv => enter [2, 2]; rw [← List.reverse_reverse (as:=l)]
  exact LamValid.eqForallEFN

theorem LamThmValid.eqForallEFN : LamThmValid lval lctx (.mkForallEFN t l) ↔ LamThmValid lval (l.reverse ++ lctx) t :=
  Iff.intro
    (fun H lctx' => by rw [pushLCtxs_append]; exact LamValid.eqForallEFN.mp (H lctx'))
    (fun H lctx' => have H' := H lctx'; by rw [pushLCtxs_append] at H'; exact LamValid.eqForallEFN.mpr H')

theorem LamThmValid.eqForallEFN' : LamThmValid lval lctx (.mkForallEFN t l.reverse) ↔ LamThmValid lval (l ++ lctx) t := by
  conv => enter [2, 2, 1]; rw [← List.reverse_reverse (as:=l)]
  exact LamThmValid.eqForallEFN

theorem LamThmValid.append (H : LamThmValid lval lctx t)
  (ex : List LamSort) : LamThmValid lval (lctx ++ ex) t := by
  dsimp [LamThmValid]; intros lctx'; rw [pushLCtxs_append]; exact H (pushLCtxs ex lctx')

theorem LamValid.prepend (H : LamValid lval lctx t)
  (ex : List LamSort) : LamValid lval (pushLCtxs ex lctx) (t.bvarLifts ex.length) := by
  have ⟨wft, ht⟩ := H
  rw [← pushLCtxsAt_zero ex]; exists (LamWF.bvarLiftsIdx rfl _ wft)
  intro lctxTerm;
  let lctxTerm₁ := fun n => lctxTerm (n + ex.length)
  have lctxeq : ∀ (n : Nat), pushLCtxsAt ex 0 lctx (n + List.length ex) = lctx n := by
    intro n; rw [pushLCtxsAt_zero, pushLCtxs_ge, Nat.add_sub_cancel]; apply Nat.le_add_left
  have ht' := (LamValid_substLCtxRecWF _ lctxeq).mp ht lctxTerm₁
  apply Eq.mp _ ht'; apply congrArg
  let hl' : HList (LamSort.interp lval.tyVal) ex := by
    apply Eq.mp _ (HList.ofFun lctxTerm ex.length)
    rw [pushLCtxsAt_zero, List.ofFun_ofPushLCtx]; rfl
  apply Eq.trans (@LamWF.interp_bvarLiftsIdx _ _ 0 _ ex hl' rfl _ lctxTerm₁ _ _) _
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
  (lctx : List LamSort)
  (heq : LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamThmEquiv lval lctx s t₁ t₂ :=
  fun lctx' => LamEquiv.ofLamValid (heq lctx')

theorem LamEquiv.eqLamValid :
  LamEquiv lval lctx s t₁ t₂ = (LamValid lval lctx (LamTerm.mkEq s t₁ t₂)) :=
  propext (Iff.intro LamValid.ofLamEquiv LamEquiv.ofLamValid)

theorem LamThmEquiv.eqLamThmValid
  (lctx : List LamSort) :
  LamThmEquiv lval lctx s t₁ t₂ = LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  propext (Iff.intro (LamThmValid.ofLamThmEquiv _) (LamThmEquiv.ofLamThmValid _))

theorem LamValid.mpLamEquiv (hp : LamValid lval lctx p₁)
  (hequiv : LamEquiv lval lctx s p₁ p₂) : LamValid lval lctx p₂ := by
  let ⟨wfp₁, hp₁⟩ := hp
  let ⟨wfp₁', ⟨wfp₂, heqp⟩⟩ := hequiv
  rcases LamWF.unique wfp₁ wfp₁' with ⟨⟨⟩, ⟨⟩⟩
  exact ⟨wfp₂, fun lctxTerm' => heqp _ ▸ hp₁ lctxTerm'⟩

theorem LamThmValid.mpLamThmEquiv
  (hequiv : LamThmEquiv lval lctx (.base .prop) p₁ p₂)
  (hp : LamThmValid lval lctx p₁) : LamThmValid lval lctx p₂ := by
  intros lctx';
  let ⟨wfp₁, ⟨wfp₂, heqp⟩⟩ := hequiv lctx'
  exists wfp₂; intro lctxTerm'; rw [← heqp]
  let ⟨wfp₁', hp₁⟩ := hp lctx'
  have wfeq : wfp₁ = wfp₁' := eq_of_heq (LamWF.unique wfp₁ wfp₁').right
  cases wfeq; apply hp₁

theorem LamEquiv.refl (wf : LamWF lval.toLamTyVal ⟨lctx, t, s⟩) :
  LamEquiv lval lctx s t t := ⟨wf, ⟨wf, fun _ => rfl⟩⟩

theorem LamThmEquiv.refl (wf : LamThmWF lval lctx s t) :
  LamThmEquiv lval lctx s t t := fun lctx' => LamEquiv.refl (wf lctx')

theorem LamGenEquiv.refl : LamGenEquiv lval t t := fun _ _ => LamEquiv.refl

theorem LamGenEquivWith.refl : LamGenEquivWith lval s t t := fun _ => LamEquiv.refl

theorem LamEquiv.eq (wf : LamWF lval.toLamTyVal ⟨lctx, t₁, s⟩)
  (heq : t₁ = t₂) : LamEquiv lval lctx s t₁ t₂ := heq ▸ LamEquiv.refl wf

theorem LamThmEquiv.eq (wf : LamThmWF lval lctx s t₁)
  (heq : t₁ = t₂) : LamThmEquiv lval lctx s t₁ t₂ := fun lctx => LamEquiv.eq (wf lctx) heq

theorem LamGenEquiv.eq (heq : t₁ = t₂) : LamGenEquiv lval t₁ t₂ := fun _ _ wf => LamEquiv.eq wf heq

theorem LamEquiv.symm (e : LamEquiv lval lctx s a b) : LamEquiv lval lctx s b a :=
  let ⟨wfa, ⟨wfb, eq⟩⟩ := e; ⟨wfb, ⟨wfa, fun lctxTerm => Eq.symm (eq lctxTerm)⟩⟩

theorem LamThmEquiv.symm (e : LamThmEquiv lval lctx rty a b) :
  LamThmEquiv lval lctx rty b a := fun lctx => LamEquiv.symm (e lctx)

theorem LamEquiv.trans
  (eab : LamEquiv lval lctx s a b) (ebc : LamEquiv lval lctx s b c) : LamEquiv lval lctx s a c := by
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := eab; let ⟨wfb', ⟨wfc, eqbc⟩⟩ := ebc
  rcases LamWF.unique wfb wfb' with ⟨_, ⟨⟩⟩
  exact ⟨wfa, ⟨wfc, fun lctxTerm => by rw [eqab, ←eqbc]⟩⟩

theorem LamEquiv.trans'
  (eab : LamEquiv lval lctx s a b) (ebc : LamEquiv lval lctx s' b c) : LamEquiv lval lctx s a c := by
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := eab; let ⟨wfb', ⟨wfc, eqbc⟩⟩ := ebc
  rcases LamWF.unique wfb wfb' with ⟨⟨⟩, ⟨⟩⟩
  exact ⟨wfa, ⟨wfc, fun lctxTerm => by rw [eqab, ←eqbc]⟩⟩

theorem LamThmEquiv.trans
  (e₁ : LamThmEquiv lval lctx rty a b) (e₂ : LamThmEquiv lval lctx rty b c) :
  LamThmEquiv lval lctx rty a c :=
  fun lctx' => LamEquiv.trans (e₁ lctx') (e₂ lctx')

theorem LamEquiv.ofLam (e : LamEquiv lval (pushLCtx w lctx) s a b) :
  LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  let ⟨wfa, ⟨wfb, eqab⟩⟩ := e; ⟨.ofLam _ wfa, .ofLam _ wfb, fun _ => funext (fun _ => eqab _)⟩

theorem LamThmEquiv.ofLam (e : LamThmEquiv lval (w :: lctx) s a b) :
  LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) := fun lctx' =>
    LamEquiv.ofLam (pushLCtxs_cons _ _ ▸ e lctx')

theorem LamGenEquiv.ofLam (e : LamGenEquiv lval a b) :
  LamGenEquiv lval (.lam w a) (.lam w b) := by
  intro lctx rty wf₁; cases wf₁
  case ofLam _ wfBody =>
    apply LamEquiv.ofLam; apply e _ _ wfBody

theorem LamGenEquivWith.ofLam (e : LamGenEquivWith lval s a b) :
  LamGenEquivWith lval (.func w'' s) (.lam w a) (.lam w b) := by
  intros lctx wf₁; cases wf₁
  case ofLam wfBody =>
    apply LamEquiv.ofLam; apply e _ wfBody

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

theorem LamThmEquiv.fromLam
  (e : LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamThmEquiv lval (w :: lctx) s a b := fun lctx' => by
  rw [pushLCtxs_cons]; apply LamEquiv.fromLam (e lctx')

theorem LamEquiv.eqLam :
  LamEquiv lval (pushLCtx w lctx) s a b = LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro LamEquiv.ofLam LamEquiv.fromLam)

theorem LamThmEquiv.eqLam :
  LamThmEquiv lval (w :: lctx) s a b = LamThmEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro LamThmEquiv.ofLam LamThmEquiv.fromLam)

theorem LamEquiv.congr
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) :=
  let ⟨wfFn₁, wfFn₂, HFn⟩ := eFn
  let ⟨wfArg₁, wfArg₂, HArg⟩ := eArg
  ⟨.ofApp _ wfFn₁ wfArg₁, .ofApp _ wfFn₂ wfArg₂, fun _ => _root_.congr (HFn _) (HArg _)⟩

theorem LamThmEquiv.congr
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := fun lctx' =>
    LamEquiv.congr (eFn lctx') (eArg lctx')

theorem LamGenEquiv.congr (eFn : LamGenEquiv lval fn₁ fn₂) (eArg : LamGenEquiv lval arg₁ arg₂) :
  LamGenEquiv lval (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := by
  intros lctx rty wfAp₁; let .ofApp _ wfFn wfArg := wfAp₁
  apply LamEquiv.congr
  case eFn => apply eFn _ _ wfFn
  case eArg => apply eArg _ _ wfArg

theorem LamGenEquivWith.congr
  (eFn : LamGenEquivWith lval (.func argTy resTy) fn₁ fn₂)
  (eArg : LamGenEquivWith lval argTy arg₁ arg₂) :
  LamGenEquivWith lval resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := by
  intros lctx wfAp₁; cases wfAp₁
  case ofApp wfArg wfFn =>
    apply LamEquiv.congr
    case eFn => apply eFn _ wfFn
    case eArg => apply eArg _ wfArg

theorem LamEquiv.congrFun
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamWF lval.toLamTyVal ⟨lctx, arg, argTy⟩) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamEquiv.congr eFn (LamEquiv.refl wfArg)

theorem LamThmEquiv.congrFun
  (eFn : LamThmEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamThmWF lval lctx argTy arg) :
  LamThmEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamThmEquiv.congr eFn (LamThmEquiv.refl wfArg)

theorem LamGenEquiv.congrFun (eFn : LamGenEquiv lval fn₁ fn₂) :
  LamGenEquiv lval (.app s fn₁ arg) (.app s fn₂ arg) :=
  LamGenEquiv.congr eFn LamGenEquiv.refl

theorem LamGenEquivWith.congrFun (eFn : LamGenEquivWith lval (.func s resTy) fn₁ fn₂) :
  LamGenEquivWith lval resTy (.app s fn₁ arg) (.app s fn₂ arg) :=
  LamGenEquivWith.congr eFn LamGenEquivWith.refl

theorem LamEquiv.congrArg
  (wfFn : LamWF lval.toLamTyVal ⟨lctx, fn, .func argTy resTy⟩)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamEquiv.congr (LamEquiv.refl wfFn) eArg

theorem LamThmEquiv.congrArg
  (wfFn : LamThmWF lval lctx (.func argTy resTy) fn)
  (eArg : LamThmEquiv lval lctx argTy arg₁ arg₂) :
  LamThmEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamThmEquiv.congr (LamThmEquiv.refl wfFn) eArg

theorem LamGenEquiv.congrArg (eArg : LamGenEquiv lval arg₁ arg₂) :
  LamGenEquiv lval (.app s fn arg₁) (.app s fn arg₂) :=
  LamGenEquiv.congr LamGenEquiv.refl eArg

theorem LamGenEquivWith.congrArg (eArg : LamGenEquivWith lval s arg₁ arg₂) :
  LamGenEquivWith lval resTy (.app s fn arg₁) (.app s fn arg₂) :=
  LamGenEquivWith.congr LamGenEquivWith.refl eArg

theorem LamEquiv.congr_mkLamFN :
  LamEquiv lval (pushLCtxs l.reverse lctx) s t₁ t₂ ↔ LamEquiv lval lctx (s.mkFuncs l) (.mkLamFN t₁ l) (.mkLamFN t₂ l) := by
  induction l generalizing t₁ t₂ s lctx
  case nil => exact Iff.intro id id
  case cons argTy l IH =>
    dsimp [LamTerm.mkLamFN, LamWF.mkLamFN]
    rw [LamSort.mkFuncs_cons, List.reverse_cons, pushLCtxs_append_singleton]
    apply Iff.trans IH
    apply Iff.intro
    case mp => apply LamEquiv.ofLam
    case mpr => apply LamEquiv.fromLam

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

theorem LamEquiv.congrArgs {args : List (LamSort × LamTerm × LamTerm)}
  (wfApp : LamWF lval.toLamTyVal ⟨lctx, LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))), resTy⟩)
  (hArgs : HList ((fun (s, arg₁, arg₂) => LamEquiv lval lctx s arg₁ arg₂)) args) :
  LamEquiv lval lctx resTy
    (LamTerm.mkAppN fn (args.map (fun (s, t₁, _) => (s, t₁))))
    (LamTerm.mkAppN fn (args.map (fun (s, _, t₂) => (s, t₂))))
   := LamEquiv.congrs wfApp (LamEquiv.refl wfApp.fnWFOfMkAppN) hArgs

theorem LamEquiv.congrFunN {args : List (LamSort × LamTerm)}
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

theorem LamEquiv.forall_congr
  (eFn : LamEquiv lval (pushLCtx argTy lctx) (.base .prop) fn₁ fn₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEF argTy fn₁) (.mkForallEF argTy fn₂) := by
  have ⟨wfFn₁, wfFn₂, eqFn⟩ := eFn
  exists LamWF.mkForallEF wfFn₁, LamWF.mkForallEF wfFn₂; intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamTerm.mkForallEF, LamWF.mkForallEF, forallLiftFn]
  apply _root_.congrArg; apply _root_.forall_congr; intro x
  apply _root_.congrArg; apply eqFn

theorem LamEquiv.congr_mkForallEFN
  (H : LamEquiv lval (pushLCtxs l.reverse lctx) (.base .prop) t₁ t₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEFN t₁ l) (.mkForallEFN t₂ l) := by
  induction l generalizing t₁ t₂ lctx
  case nil => exact H
  case cons argTy l IH =>
    dsimp [LamTerm.mkForallEFN, LamWF.mkForallEFN];
    apply LamEquiv.forall_congr; apply IH
    rw [List.reverse_cons] at H; rw [pushLCtxs_append_singleton] at H; exact H

theorem LamEquiv.congr_mkForallEFN'
  (H : LamEquiv lval (pushLCtxs l lctx) (.base .prop) t₁ t₂) :
  LamEquiv lval lctx (.base .prop) (.mkForallEFN t₁ l.reverse) (.mkForallEFN t₂ l.reverse) := by
  rw [← List.reverse_reverse (as:=l)] at H; exact congr_mkForallEFN H

theorem LamEquiv.not_imp_not
  (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, .base .prop⟩)
  (wf₂ : LamWF lval.toLamTyVal ⟨lctx, t₂, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) (.mkImp (.mkNot t₁) (.mkNot t₂)) (.mkImp t₂ t₁) := by
  exists (LamWF.mkImp (.mkNot wf₁) (.mkNot wf₂)); exists (LamWF.mkImp wf₂ wf₁); intro lctxTerm
  dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamTerm.mkImp, impLift, notLift]
  apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr)
  case mp =>
    intro nin h; apply Classical.byContradiction; intro nh'; apply nin nh' h
  case mpr =>
    intro nin nh h'; apply nh (nin h')

theorem LamEquiv.imp_swap
  (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, .base .prop⟩)
  (wf₂ : LamWF lval.toLamTyVal ⟨lctx, t₂, .base .prop⟩)
  (wf₃ : LamWF lval.toLamTyVal ⟨lctx, t₃, .base .prop⟩) :
  LamEquiv lval lctx (.base .prop) (.mkImp t₁ (.mkImp t₂ t₃)) (.mkImp t₂ (.mkImp t₁ t₃)) := by
  exists .mkImp wf₁ (.mkImp wf₂ wf₃); exists .mkImp wf₂ (.mkImp wf₁ wf₃); intro lctxTerm
  apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr) <;> intro f <;> exact fun a b => f b a

theorem LamValid.eq_refl
  (wfA : LamWF lval.toLamTyVal ⟨lctx, a, s⟩) : LamValid lval lctx (.mkEq s a a) := by
  exists (.mkEq wfA wfA); intro lctxTerm; rfl

theorem LamValid.eq_eq (heq : a = b)
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

def LamWF.funextF
  (wf : LamWF ltv ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, s⟩) :
  LamWF ltv ⟨pushLCtx argTy lctx, .mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)), .base .prop⟩ :=
  let wflAp := LamWF.ofApp _ wf.getFn.getArg.bvarLift .pushLCtx_ofBVar
  let wfrAp := LamWF.ofApp _ wf.getArg.bvarLift .pushLCtx_ofBVar
  LamWF.mkEq wflAp wfrAp

def LamWF.ofFunextF
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
      dsimp [interp, LamBaseTerm.LamWF.interp, LamTerm.mkEq, eqLiftFn]
      rcases LamWF.unique HLhs' HLhs.bvarLift with ⟨⟨⟩, ⟨⟩⟩
      rcases LamWF.unique HRhs' HRhs.bvarLift with ⟨⟨⟩, ⟨⟩⟩
      apply propext (Iff.intro ?mp ?mpr)
      case mp =>
        intro h x; rw [← LamWF.interp_bvarLift, ← LamWF.interp_bvarLift, h]
      case mpr =>
        intro h; apply funext; intro x; have h' := h x
        rw [← LamWF.interp_bvarLift, ← LamWF.interp_bvarLift] at h'; exact h'

theorem LamEquiv.eqFunextF
  (wfEq : LamWF lval.toLamTyVal ⟨lctx, .mkEq (.func argTy resTy) fn₁ fn₂, s⟩) :
  LamEquiv lval lctx s
    (.mkEq (.func argTy resTy) fn₁ fn₂)
    (.mkForallEF argTy (.mkEq resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)))) := by
  match wfEq with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wfFn₁) wfFn₂ =>
    let wfAp₁ := LamWF.ofApp _
      (LamWF.bvarLift (s:=argTy) _ wfFn₁) LamWF.pushLCtx_ofBVar
    let wfAp₂ := LamWF.ofApp _
      (LamWF.bvarLift (s:=argTy) _ wfFn₂) LamWF.pushLCtx_ofBVar
    exists LamWF.mkEq wfFn₁ wfFn₂, LamWF.mkForallEF (LamWF.mkEq wfAp₁ wfAp₂); intro lctxTerm
    dsimp +zetaDelta [LamWF.interp, LamBaseTerm.LamWF.interp, LamTerm.mkEq, LamWF.mkEq, LamWF.mkForallEF, LamTerm.mkForallEF, eqLiftFn, forallLiftFn, LamWF.pushLCtx_ofBVar]
    apply _root_.congrArg; apply propext (Iff.intro ?mp ?mpr)
    case mp =>
      intro hinterp h; rw [← LamWF.interp_bvarLift, ← LamWF.interp_bvarLift, hinterp]
    case mpr =>
      intro hinterp; apply funext; intro x; apply Eq.trans ?left (Eq.trans (hinterp x) ?right)
      case left => rw [← LamWF.interp_bvarLift]
      case right => rw [← LamWF.interp_bvarLift]

theorem LamEquiv.eqFunextH
  (wfEq : LamWF lval.toLamTyVal ⟨pushLCtx argTy lctx, .mkEq resTy p₁ p₂, s⟩) :
  LamEquiv lval lctx s
    (.mkForallEF argTy (.mkEq resTy p₁ p₂))
    (.mkEq (.func argTy resTy) (.lam argTy p₁) (.lam argTy p₂)) := by
  cases wfEq.getFn.getFn.getBase
  match wfEq with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wfFn₁) wfFn₂ =>
    exists LamWF.mkForallEF (.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wfFn₁) wfFn₂)
    exists LamWF.mkEq (.ofLam _ wfFn₁) (.ofLam _ wfFn₂); intro lctxTerm
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamWF.mkEq, eqLiftFn, forallLiftFn]
    apply GLift.down.inj; dsimp; apply propext (Iff.intro ?mp ?mpr)
    case mp => apply funext
    case mpr => intro h x; apply _root_.congrFun h

theorem LamEquiv.funextF
  (eAp : LamEquiv lval (pushLCtx argTy lctx) resTy (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0))) :
  LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂ := by
  have ⟨wfFnAp₁, wfFnAp₂, hFnAp⟩ := eAp
  apply LamEquiv.ofLamValid (s:=.func argTy resTy) _
  have hEqValid := LamValid.ofLamEquiv eAp
  apply LamValid.mpLamEquiv (s:=.base .prop) (LamValid.revert1F hEqValid)
  apply LamEquiv.symm; apply LamEquiv.eqFunextF
  apply LamWF.mkEq wfFnAp₁.getFn.fromBVarLift wfFnAp₂.getFn.fromBVarLift

theorem LamValid.funextF
  {fn₁ fn₂ : LamTerm}
  (HApp : LamValid lval (pushLCtx argTy lctx) (.mkEq resTy
    (.app argTy fn₁.bvarLift (.bvar 0)) (.app argTy fn₂.bvarLift (.bvar 0)))) :
  LamValid lval lctx (.mkEq (.func argTy resTy) fn₁ fn₂) :=
  have heqAp := LamEquiv.ofLamValid HApp
  have heqFn := LamEquiv.funextF heqAp
  LamValid.ofLamEquiv heqFn

theorem LamValid.impLift (H : LamValid lval lctx (.mkImp t₁ t₂)) :
  LamValid lval lctx t₁ → LamValid lval lctx t₂ := by
  have ⟨.ofApp _ (.ofApp _ (.ofBase .ofImp) wft₁) wft₂, himp⟩ := H; intro ⟨wft₁', ht₁⟩
  cases (LamWF.unique wft₁ wft₁').right
  exists wft₂; intro lctxTerm; exact (himp lctxTerm) (ht₁ lctxTerm)

theorem LamValid.imp_self (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩) :
  LamValid lval lctx (.mkImp t t) := by
  exists .mkImp wf wf; intro lctxTerm; exact id

theorem LamThmValid.imp_self (wf : LamThmWF lval lctx (.base .prop) t) :
  LamThmValid lval lctx (.mkImp t t) :=
  fun lctx' => LamValid.imp_self (wf lctx')

theorem LamValid.imp_trans
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .prop⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .prop⟩)
  (wfc : LamWF lval.toLamTyVal ⟨lctx, c, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp a b) (.mkImp (.mkImp b c) (.mkImp a c))) := by
  exists .mkImp (.mkImp wfa wfb) (.mkImp (.mkImp wfb wfc) (.mkImp wfa wfc)); intro lctxTerm
  exact flip (· ∘ ·)

theorem LamValid.imp_trans'
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .prop⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .prop⟩)
  (wfc : LamWF lval.toLamTyVal ⟨lctx, c, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp b c) (.mkImp (.mkImp a b) (.mkImp a c))) :=
  mpLamEquiv (imp_trans wfa wfb wfc) (LamEquiv.imp_swap
    (.mkImp wfa wfb) (.mkImp wfb wfc) (.mkImp wfa wfc))

theorem LamValid.and_imp_and_of_imp_imp
  (wfa₁ : LamWF lval.toLamTyVal ⟨lctx, a₁, .base .prop⟩)
  (wfa₂ : LamWF lval.toLamTyVal ⟨lctx, a₂, .base .prop⟩)
  (wfb₁ : LamWF lval.toLamTyVal ⟨lctx, b₁, .base .prop⟩)
  (wfb₂ : LamWF lval.toLamTyVal ⟨lctx, b₂, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp a₁ a₂) (.mkImp (.mkImp b₁ b₂) (.mkImp (.mkAnd a₁ b₁) (.mkAnd a₂ b₂)))) := by
  exists .mkImp (.mkImp wfa₁ wfa₂) (.mkImp (.mkImp wfb₁ wfb₂) (.mkImp (.mkAnd wfa₁ wfb₁) (.mkAnd wfa₂ wfb₂))); intro lctxTerm
  intro hai hbi ⟨ha, hb⟩; exact And.intro (hai ha) (hbi hb)

theorem LamValid.and_imp_and_of_left_imp
  (wfa₁ : LamWF lval.toLamTyVal ⟨lctx, a₁, .base .prop⟩)
  (wfa₂ : LamWF lval.toLamTyVal ⟨lctx, a₂, .base .prop⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp a₁ a₂) (.mkImp (.mkAnd a₁ b) (.mkAnd a₂ b))) := by
  exists .mkImp (.mkImp wfa₁ wfa₂) (.mkImp (.mkAnd wfa₁ wfb) (.mkAnd wfa₂ wfb)); intro lctxTerm
  intro hai ⟨ha, hb⟩; exact And.intro (hai ha) hb

theorem LamValid.and_imp_and_of_right_imp
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .prop⟩)
  (wfb₁ : LamWF lval.toLamTyVal ⟨lctx, b₁, .base .prop⟩)
  (wfb₂ : LamWF lval.toLamTyVal ⟨lctx, b₂, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp b₁ b₂) (.mkImp (.mkAnd a b₁) (.mkAnd a b₂))) := by
  exists .mkImp (.mkImp wfb₁ wfb₂) (.mkImp (.mkAnd wfa wfb₁) (.mkAnd wfa wfb₂)); intro lctxTerm
  intro hbi ⟨ha, hb⟩; exact And.intro ha (hbi hb)

theorem LamValid.and_equiv :
  LamValid lval lctx (.mkAnd a b) ↔ LamValid lval lctx a ∧ LamValid lval lctx b := by
  apply Iff.intro
  case mp =>
    intro vand; have ⟨hwf, hv⟩ := vand
    match hwf with
    | .ofApp _ (.ofApp _ (.ofBase .ofAnd) wfa) wfb =>
      apply And.intro ⟨wfa, fun lctxTerm => And.left (hv lctxTerm)⟩ ⟨wfb, fun lctxTerm => And.right (hv lctxTerm)⟩
  case mpr =>
    intro ⟨⟨wfa, va⟩, ⟨wfb, vb⟩⟩; exists (.mkAnd wfa wfb)
    intro lctxTerm; apply And.intro (va lctxTerm) (vb lctxTerm)

theorem LamValid.and_left
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .prop⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkAnd a b) a) := by
  exists LamWF.mkImp (.mkAnd wfa wfb) wfa; intro lctxTerm hand
  apply And.left hand

theorem LamValid.and_right
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .prop⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkAnd a b) b) := by
  exists LamWF.mkImp (.mkAnd wfa wfb) wfb; intro lctxTerm hand
  apply And.right hand

theorem LamValid.or_imp_or_of_imp_imp
  (wfa₁ : LamWF lval.toLamTyVal ⟨lctx, a₁, .base .prop⟩)
  (wfa₂ : LamWF lval.toLamTyVal ⟨lctx, a₂, .base .prop⟩)
  (wfb₁ : LamWF lval.toLamTyVal ⟨lctx, b₁, .base .prop⟩)
  (wfb₂ : LamWF lval.toLamTyVal ⟨lctx, b₂, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp a₁ a₂) (.mkImp (.mkImp b₁ b₂) (.mkImp (.mkOr a₁ b₁) (.mkOr a₂ b₂)))) := by
  exists .mkImp (.mkImp wfa₁ wfa₂) (.mkImp (.mkImp wfb₁ wfb₂) (.mkImp (.mkOr wfa₁ wfb₁) (.mkOr wfa₂ wfb₂))); intro lctxTerm
  intro hai hbi hab; cases hab
  case inl ha => exact Or.inl (hai ha)
  case inr hb => exact Or.inr (hbi hb)

theorem LamValid.or_imp_or_of_left_imp
  (wfa₁ : LamWF lval.toLamTyVal ⟨lctx, a₁, .base .prop⟩)
  (wfa₂ : LamWF lval.toLamTyVal ⟨lctx, a₂, .base .prop⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp a₁ a₂) (.mkImp (.mkOr a₁ b) (.mkOr a₂ b))) := by
  exists .mkImp (.mkImp wfa₁ wfa₂) (.mkImp (.mkOr wfa₁ wfb) (.mkOr wfa₂ wfb)); intro lctxTerm
  intro hai hab; cases hab;
  case inl ha => exact Or.inl (hai ha)
  case inr hb => exact Or.inr hb

theorem LamValid.or_imp_or_of_right_imp
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .prop⟩)
  (wfb₁ : LamWF lval.toLamTyVal ⟨lctx, b₁, .base .prop⟩)
  (wfb₂ : LamWF lval.toLamTyVal ⟨lctx, b₂, .base .prop⟩) :
  LamValid lval lctx (.mkImp (.mkImp b₁ b₂) (.mkImp (.mkOr a b₁) (.mkOr a b₂))) := by
  exists .mkImp (.mkImp wfb₁ wfb₂) (.mkImp (.mkOr wfa wfb₁) (.mkOr wfa wfb₂)); intro lctxTerm
  intro hbi hab; cases hab
  case inl ha => exact Or.inl ha
  case inr hb => exact Or.inr (hbi hb)

theorem LamTerm.evarBounded_of_evarEquiv
  (H : evarEquiv f) : evarBounded f bound := by
  intros t t' heq; rw [H _ _ heq]; apply Nat.le_max_right

theorem LamTerm.evarBounded_le
  (H : evarBounded f bound) (hle : bound ≤ bound') : evarBounded f bound' := by
  intro t t' heq; apply Nat.le_trans (H _ _ heq)
  apply Nat.max_le.mpr (And.intro ?ll ?lr)
  case ll => apply Nat.le_trans hle (Nat.le_max_left _ _)
  case lr => apply Nat.le_max_right

theorem LamTerm.evarBounded_none : evarBounded (fun _ => .none) bound := by
  intro t t' heq; cases heq

theorem LamTerm.evarBounded_eqNone (H : ∀ t, f t = .none) : evarBounded f bound := by
  intro t t' heq; rw [H] at heq; cases heq

theorem LamTerm.evarEquiv_none : evarEquiv (fun _ => .none) := by
  intro t t' heq; cases heq

theorem LamTerm.evarEquiv_eqNone (H : ∀ t, f t = .none) : evarEquiv f := by
  intro t t' heq; rw [H] at heq; cases heq

theorem LamTerm.evarBounded_rwGenAt (H : evarBounded conv bound) : evarBounded (rwGenAt occ conv) bound := by
  induction occ
  case nil => exact H
  case cons b occ IH =>
    dsimp [rwGenAt]; intro t₁ t₂; dsimp
    cases t₁ <;> try (intro h; cases h)
    case lam s body =>
      dsimp; cases h₁ : rwGenAt occ conv body <;> intro h <;> cases h
      case refl body' =>
        dsimp [maxEVarSucc]; apply IH _ _ h₁
    case app s fn arg =>
      match b with
      | true =>
        dsimp; cases h₁ : rwGenAt occ conv arg <;> intro h <;> cases h
        case refl arg' =>
          dsimp [maxEVarSucc]
          apply Nat.max_le.mpr (And.intro ?ll ?lr)
          case ll => apply Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          case lr =>
            cases (Nat.le_max_iff _ _ _).mp (IH _ _ h₁)
            case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
            case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      | false =>
        dsimp; cases h₁ : rwGenAt occ conv fn <;> intro h <;> cases h
        case refl fn' =>
          dsimp [maxEVarSucc]
          apply Nat.max_le.mpr (And.intro ?ll ?lr)
          case ll =>
            cases (Nat.le_max_iff _ _ _).mp (IH _ _ h₁)
            case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
            case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
          case lr => apply Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem LamTerm.evarEquiv_rwGenAt (H : evarEquiv conv) : evarEquiv (rwGenAt occ conv) := by
  induction occ
  case nil => exact H
  case cons b occ IH =>
    dsimp [rwGenAt]; intro t₁ t₂; dsimp
    cases t₁ <;> try (intro h; cases h)
    case lam s body =>
      dsimp; cases h₁ : rwGenAt occ conv body <;> intro h <;> cases h
      case refl body' =>
        dsimp [maxEVarSucc]; apply IH _ _ h₁
    case app s fn arg =>
      match b with
      | true =>
        dsimp; cases h₁ : rwGenAt occ conv arg <;> intro h <;> cases h
        case refl arg' =>
          dsimp [maxEVarSucc]; rw [IH _ _ h₁]
      | false =>
        dsimp; cases h₁ : rwGenAt occ conv fn <;> intro h <;> cases h
        case refl fn' =>
          dsimp [maxEVarSucc]; rw [IH _ _ h₁]

theorem LamGenConv.none : LamGenConv lval (fun _ => .none) := by
  intro t₁ t₂ heq; cases heq

theorem LamGenConv.eqNone (H : ∀ t, f t = .none) : LamGenConv lval f := by
  intro t₁ t₂ heq; rw [H] at heq; cases heq

theorem LamGenConv.rwGenAt (H : LamGenConv lval conv) : LamGenConv lval (LamTerm.rwGenAt occ conv) := by
  induction occ
  case nil => exact H
  case cons b occ IH =>
    dsimp [LamTerm.rwGenAt, LamGenConv]; intros t₁ t₂
    cases t₁ <;> try (intro h; cases h)
    case lam s body =>
      dsimp; cases h₁ : LamTerm.rwGenAt occ conv body <;> intro h <;> cases h
      case refl body' =>
        apply LamGenEquiv.ofLam; apply IH _ _ h₁
    case app s fn arg =>
      match b with
      | true =>
        dsimp; cases h₁ : LamTerm.rwGenAt occ conv arg <;> intro h <;> cases h
        case refl arg' =>
          apply LamGenEquiv.congrArg; apply IH _ _ h₁
      | false =>
        dsimp; cases h₁ : LamTerm.rwGenAt occ conv fn <;> intro h <;> cases h
        case refl fn' =>
          apply LamGenEquiv.congrFun; apply IH _ _ h₁

theorem LamTerm.evarBounded_rwGenAll (H : evarBounded conv bound) :
  evarBounded (rwGenAll conv) bound := by
  intro t₁; induction t₁ <;> intros t₂
  case atom n =>
    rw [rwGenAll_atom]; cases h : conv (atom n) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H; rw [h]; rfl
  case etom n =>
    rw [rwGenAll_etom]; cases h : conv (etom n) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H; rw [h]; rfl
  case base b =>
    rw [rwGenAll_base]; cases h : conv (base b) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H; rw [h]; rfl
  case bvar n =>
    rw [rwGenAll_bvar]; cases h : conv (bvar n) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H; rw [h]; rfl
  case lam s body IH =>
    simp [rwGenAll]
    match h₁ : conv (.lam s body) with
    | .some t' => intro h₂; cases h₂; apply H _ _ h₁
    | .none =>
      match h₂ : rwGenAll conv body with
      | .some t' => intro h; cases h; dsimp [maxEVarSucc]; apply IH _ h₂
      | .none => intro h; cases h
  case app s fn arg IHFn IHArg =>
    simp [rwGenAll]
    match h₁ : conv (.app s fn arg) with
    | .some t' => intro h₂; cases h₂; apply H _ _ h₁
    | .none =>
      match h₂ : rwGenAll conv fn, h₃ : rwGenAll conv arg with
      | .some fn', .some arg' =>
        intro h; cases h; dsimp [maxEVarSucc]; rw [Nat.max, Nat.max]
        apply Nat.max_le.mpr (And.intro ?ll ?lr)
        case ll =>
          cases (Nat.le_max_iff _ _ _).mp (IHFn _ h₂)
          case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
          case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        case lr =>
          cases (Nat.le_max_iff _ _ _).mp (IHArg _ h₃)
          case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
          case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      | .some fn', .none => intro h; cases h
      | .none, _ => intro h; cases h

theorem LamTerm.evarEquiv_rwGenAll (H : evarEquiv conv) : evarEquiv (rwGenAll conv) := by
  intro t₁; induction t₁ <;> intros t₂
  case atom n =>
    rw [rwGenAll_atom]; cases h : conv (atom n) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H; rw [h]; rfl
  case etom n =>
    rw [rwGenAll_etom]; cases h : conv (etom n) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H; rw [h]; rfl
  case base b =>
    rw [rwGenAll_base]; cases h : conv (base b) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H; rw [h]; rfl
  case bvar n =>
    rw [rwGenAll_bvar]; cases h : conv (bvar n) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H; rw [h]; rfl
  case lam s body IH =>
    simp [rwGenAll]
    match h₁ : conv (.lam s body) with
    | .some t' => intro h₂; cases h₂; apply H _ _ h₁
    | .none =>
      match h₂ : rwGenAll conv body with
      | .some t' => intro h; cases h; dsimp [maxEVarSucc]; apply IH _ h₂
      | .none => intro h; cases h
  case app s fn arg IHFn IHArg =>
    simp [rwGenAll]
    match h₁ : conv (.app s fn arg) with
    | .some t' => intro h₂; cases h₂; apply H _ _ h₁
    | .none =>
      match h₂ : rwGenAll conv fn, h₃ : rwGenAll conv arg with
      | .some fn', .some arg' =>
        intro h; cases h; dsimp [maxEVarSucc]; rw [IHFn _ h₂]; rw [IHArg _ h₃]
      | .some fn', .none => intro h; cases h
      | .none, _ => intro h; cases h

theorem LamGenConv.rwGenAll (H : LamGenConv lval conv) : LamGenConv lval (LamTerm.rwGenAll conv) := by
  intro t₁; induction t₁ <;> intros t₂
  case atom n =>
    dsimp [LamGenConv] at H; rw [LamTerm.rwGenAll_atom]
    cases h : conv (.atom n) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquiv.refl
    case some.refl => apply H _ _ h
  case etom n =>
    dsimp [LamGenConv] at H; rw [LamTerm.rwGenAll_etom]
    cases h : conv (.etom n) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquiv.refl
    case some.refl => apply H _ _ h
  case base b =>
    dsimp [LamGenConv] at H; rw [LamTerm.rwGenAll_base]
    cases h : conv (.base b) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquiv.refl
    case some.refl => apply H _ _ h
  case bvar n =>
    dsimp [LamGenConv] at H; rw [LamTerm.rwGenAll_bvar]
    cases h : conv (.bvar n) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquiv.refl
    case some.refl => apply H _ _ h
  case lam s body IH =>
    simp [LamTerm.rwGenAll]
    match h₁ : conv (.lam s body) with
    | .some t' => intro h₂; cases h₂; apply H _ _ h₁
    | .none =>
      match h₂ : LamTerm.rwGenAll conv body with
      | .some t' => intro h; cases h; apply LamGenEquiv.ofLam; apply IH _ h₂
      | .none => intro h; cases h
  case app s fn arg IHFn IHArg =>
    simp [LamTerm.rwGenAll]
    match h₁ : conv (.app s fn arg) with
    | .some t' => intro h₂; cases h₂; apply H _ _ h₁
    | .none =>
      match h₂ : LamTerm.rwGenAll conv fn, h₃ : LamTerm.rwGenAll conv arg with
      | .some fn', .some arg' =>
        intro h; cases h; apply LamGenEquiv.congr
        case eFn => apply IHFn _ h₂
        case eArg => apply IHArg _ h₃
      | .some fn', .none => intro h; cases h
      | .none, _ => intro h; cases h

theorem LamTerm.evarBounded_rwGenAtWith (H : ∀ s, evarBounded (conv s) bound) :
  ∀ s, evarBounded (LamTerm.rwGenAtWith occ conv s) bound := by
  induction occ
  case nil => exact H
  case cons b occ IH =>
    dsimp [LamTerm.rwGenAtWith, LamGenConv]; intros rty t₁ t₂
    cases t₁ <;> try (intro h; cases h)
    case lam s body =>
      dsimp; cases rty <;> try (intro h; cases h)
      case func _ resTy =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv resTy body <;> intro h <;> cases h
        case refl body' =>
          dsimp [maxEVarSucc]; apply IH _ _ _ h₁
    case app s fn arg =>
      dsimp
      match b with
      | true =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv s arg <;> intro h <;> cases h
        case refl arg' =>
          dsimp [maxEVarSucc]
          apply Nat.max_le.mpr (And.intro ?ll ?lr)
          case ll => apply Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          case lr =>
            cases (Nat.le_max_iff _ _ _).mp (IH _ _ _ h₁)
            case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
            case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      | false =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv (.func s rty) fn <;> intro h <;> cases h
        case refl fn' =>
          dsimp [maxEVarSucc]
          apply Nat.max_le.mpr (And.intro ?ll ?lr)
          case ll =>
            cases (Nat.le_max_iff _ _ _).mp (IH _ _ _ h₁)
            case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
            case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
          case lr => apply Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem LamTerm.evarEquiv_rwGenAtWith (H : ∀ s, evarEquiv (conv s)) :
  ∀ s, evarEquiv (LamTerm.rwGenAtWith occ conv s) := by
  induction occ
  case nil => exact H
  case cons b occ IH =>
    dsimp [LamTerm.rwGenAtWith, LamGenConv]; intros rty t₁ t₂
    cases t₁ <;> try (intro h; cases h)
    case lam s body =>
      dsimp; cases rty <;> try (intro h; cases h)
      case func _ resTy =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv resTy body <;> intro h <;> cases h
        case refl body' =>
          dsimp [maxEVarSucc]; apply IH _ _ _ h₁
    case app s fn arg =>
      dsimp
      match b with
      | true =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv s arg <;> intro h <;> cases h
        case refl arg' =>
          dsimp [maxEVarSucc]; rw [IH _ _ _ h₁]
      | false =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv (.func s rty) fn <;> intro h <;> cases h
        case refl fn' =>
          dsimp [maxEVarSucc]; rw [IH _ _ _ h₁]

theorem LamGenConvWith.none : LamGenConvWith lval (fun _ _ => .none) := by
  intro s t₁ t₂ heq; cases heq

theorem LamGenConvWith.eqNone (H : ∀ s t, f s t = .none) : LamGenConvWith lval f := by
  intro s t₁ t₂ heq; rw [H] at heq; cases heq

theorem LamGenConvWith.rwGenAtWith (H : LamGenConvWith lval conv) : LamGenConvWith lval (LamTerm.rwGenAtWith occ conv) := by
  induction occ
  case nil => exact H
  case cons b occ IH =>
    dsimp [LamTerm.rwGenAtWith, LamGenConv]; intros rty t₁ t₂
    cases t₁ <;> try (intro h; cases h)
    case lam s body =>
      dsimp; cases rty <;> try (intro h; cases h)
      case func _ resTy =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv resTy body <;> intro h <;> cases h
        case refl body' =>
          apply LamGenEquivWith.ofLam; apply IH _ _ _ h₁
    case app s fn arg =>
      dsimp
      match b with
      | true =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv s arg <;> intro h <;> cases h
        case refl arg' =>
          apply LamGenEquivWith.congrArg; apply IH _ _ _ h₁
      | false =>
        dsimp; cases h₁ : LamTerm.rwGenAtWith occ conv (.func s rty) fn <;> intro h <;> cases h
        case refl fn' =>
          apply LamGenEquivWith.congrFun; apply IH _ _ _ h₁

theorem LamTerm.evarBounded_rwGenAllWith (H : ∀ s, evarBounded (conv s) bound) :
  ∀ s, evarBounded (LamTerm.rwGenAllWith conv s) bound := by
  intro s t₁; induction t₁ generalizing s <;> intros t₂
  case atom n =>
    rw [LamTerm.rwGenAllWith_atom]
    cases h : conv s (.atom n) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H _ _ _ h
  case etom n =>
    rw [LamTerm.rwGenAllWith_etom]
    cases h : conv s (.etom n) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H _ _ _ h
  case base b =>
    rw [LamTerm.rwGenAllWith_base]
    cases h : conv s (.base b) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H _ _ _ h
  case bvar n =>
    rw [LamTerm.rwGenAllWith_bvar]
    cases h : conv s (.bvar n) <;> intro heq <;> cases heq
    case none.refl => apply Nat.le_max_right
    case some.refl => apply H _ _ _ h
  case lam s' body IH =>
    rw [LamTerm.rwGenAllWith_lam]
    match h₁ : conv s (.lam s' body) with
    | .some t' => intro h₂; cases h₂; apply H _ _ _ h₁
    | .none =>
      dsimp
      cases s <;> try (intro h; cases h)
      case func _ resTy =>
        dsimp
        match h₂ : LamTerm.rwGenAllWith conv resTy body with
        | .some t' => intro h; cases h; dsimp [maxEVarSucc]; apply IH _ _ h₂
        | .none => intro h; cases h
  case app s' fn arg IHFn IHArg =>
    simp [LamTerm.rwGenAllWith]
    match h₁ : conv s (.app s' fn arg) with
    | .some t' => intro h₂; cases h₂; apply H _ _ _ h₁
    | .none =>
      match h₂ : LamTerm.rwGenAllWith conv (.func s' s) fn, h₃ : LamTerm.rwGenAllWith conv s' arg with
      | .some fn', .some arg' =>
        intro h; cases h; dsimp [maxEVarSucc]
        apply Nat.max_le.mpr (And.intro ?ll ?lr)
        case ll =>
          cases (Nat.le_max_iff _ _ _).mp (IHFn _ _ h₂)
          case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
          case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        case lr =>
          cases (Nat.le_max_iff _ _ _).mp (IHArg _ _ h₃)
          case inl w => apply Nat.le_trans w (Nat.le_max_left _ _)
          case inr w => apply Nat.le_trans w (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      | .some fn', .none => intro h; cases h
      | .none, _ => intro h; cases h

theorem LamTerm.evarEquiv_rwGenAllWith (H : ∀ s, evarEquiv (conv s)) :
  ∀ s, evarEquiv (LamTerm.rwGenAllWith conv s) := by
  intro s t₁; induction t₁ generalizing s <;> intros t₂
  case atom n =>
    rw [LamTerm.rwGenAllWith_atom]
    cases h : conv s (.atom n) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H _ _ _ h
  case etom n =>
    rw [LamTerm.rwGenAllWith_etom]
    cases h : conv s (.etom n) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H _ _ _ h
  case base b =>
    rw [LamTerm.rwGenAllWith_base]
    cases h : conv s (.base b) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H _ _ _ h
  case bvar n =>
    rw [LamTerm.rwGenAllWith_bvar]
    cases h : conv s (.bvar n) <;> intro heq <;> cases heq
    case none.refl => rfl
    case some.refl => apply H _ _ _ h
  case lam s' body IH =>
    rw [LamTerm.rwGenAllWith_lam]
    match h₁ : conv s (.lam s' body) with
    | .some t' => intro h₂; cases h₂; apply H _ _ _ h₁
    | .none =>
      dsimp
      cases s <;> try (intro h; cases h)
      case func _ resTy =>
        dsimp
        match h₂ : LamTerm.rwGenAllWith conv resTy body with
        | .some t' => intro h; cases h; dsimp [maxEVarSucc]; apply IH _ _ h₂
        | .none => intro h; cases h
  case app s' fn arg IHFn IHArg =>
    simp [LamTerm.rwGenAllWith]
    match h₁ : conv s (.app s' fn arg) with
    | .some t' => intro h₂; cases h₂; apply H _ _ _ h₁
    | .none =>
      match h₂ : LamTerm.rwGenAllWith conv (.func s' s) fn, h₃ : LamTerm.rwGenAllWith conv s' arg with
      | .some fn', .some arg' =>
        intro h; cases h; dsimp [maxEVarSucc]; rw [IHFn _ _ h₂]; rw [IHArg _ _ h₃]
      | .some fn', .none => intro h; cases h
      | .none, _ => intro h; cases h

theorem LamGenConvWith.rwGenAllWith (H : LamGenConvWith lval conv) : LamGenConvWith lval (LamTerm.rwGenAllWith conv) := by
  intro s t₁; induction t₁ generalizing s <;> intros t₂
  case atom n =>
    dsimp [LamGenConvWith] at H; rw [LamTerm.rwGenAllWith_atom]
    cases h : conv s (.atom n) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquivWith.refl
    case some.refl => apply H _ _ _ h
  case etom n =>
    dsimp [LamGenConvWith] at H; rw [LamTerm.rwGenAllWith_etom]
    cases h : conv s (.etom n) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquivWith.refl
    case some.refl => apply H _ _ _ h
  case base b =>
    dsimp [LamGenConvWith] at H; rw [LamTerm.rwGenAllWith_base]
    cases h : conv s (.base b) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquivWith.refl
    case some.refl => apply H _ _ _ h
  case bvar n =>
    dsimp [LamGenConvWith] at H; rw [LamTerm.rwGenAllWith_bvar]
    cases h : conv s (.bvar n) <;> intro heq <;> cases heq
    case none.refl => apply LamGenEquivWith.refl
    case some.refl => apply H _ _ _ h
  case lam s' body IH =>
    rw [LamTerm.rwGenAllWith_lam]
    match h₁ : conv s (.lam s' body) with
    | .some t' => intro h₂; cases h₂; apply H _ _ _ h₁
    | .none =>
      dsimp
      cases s <;> try (intro h; cases h)
      case func _ resTy =>
        dsimp
        match h₂ : LamTerm.rwGenAllWith conv resTy body with
        | .some t' => intro h; cases h; apply LamGenEquivWith.ofLam; apply IH _ _ h₂
        | .none => intro h; cases h
  case app s' fn arg IHFn IHArg =>
    simp [LamTerm.rwGenAllWith]
    match h₁ : conv s (.app s' fn arg) with
    | .some t' => intro h₂; cases h₂; apply H _ _ _ h₁
    | .none =>
      match h₂ : LamTerm.rwGenAllWith conv (.func s' s) fn, h₃ : LamTerm.rwGenAllWith conv s' arg with
      | .some fn', .some arg' =>
        intro h; cases h; apply LamGenEquivWith.congr
        case eFn => apply IHFn _ _ h₂
        case eArg => apply IHArg _ _ h₃
      | .some fn', .none => intro h; cases h
      | .none, _ => intro h; cases h

theorem LamTerm.evarEquiv_rwGenAtIfSign {modify} (H : evarEquiv modify) :
  evarEquiv (LamTerm.rwGenAtIfSign b occ modify) := by
  intro t t'; dsimp [rwGenAtIfSign]
  cases (isSign b occ t) <;> try (intro h; cases h)
  dsimp; apply LamTerm.evarEquiv_rwGenAt H

theorem LamTerm.evarBounded_rwGenAtIfSign {modify} (H : evarBounded modify n) :
  evarBounded (LamTerm.rwGenAtIfSign b occ modify) n := by
  intro t t'; dsimp [rwGenAtIfSign]
  cases (isSign b occ t) <;> try (intro h; cases h)
  dsimp; apply LamTerm.evarBounded_rwGenAt H

theorem LamGenModify.rwGenAtIfSign {modify} (H : LamGenModify lval modify weaken?) :
  LamGenModify lval (LamTerm.rwGenAtIfSign (weaken? == weaken?') occ modify) weaken?' := by
  generalize hl' : occ.length = l
  have hl : occ.length ≤ l := by cases hl'; exact .refl
  clear hl'
  induction l generalizing occ weaken? weaken?'
  case zero =>
    cases List.length_eq_zero.mp (Nat.le_zero.mp hl)
    match h : weaken? == weaken?' with
    | true => cases (Bool.beq_to_eq _ _).mp h; exact H
    | false => dsimp [LamGenModify]; intro t₁ t₂ h; cases h
  case succ l IH =>
    cases occ
    case nil =>
      exact IH H (Nat.zero_le _)
    case cons b occ =>
      have hl' := Nat.le_of_succ_le_succ hl
      dsimp [LamGenModify, LamTerm.rwGenAtIfSign]
      intros t₁ t₂
      match h₁ : LamTerm.isSign (weaken? == weaken?') (b :: occ) t₁ with
      | true =>
        dsimp; cases t₁ <;> try cases h₁
        case app sI fnI argI =>
          cases fnI <;> try cases h₁
          case base b =>
            cases b <;> try cases h₁
            case pcst p =>
              cases p <;> try cases h₁
              dsimp [LamTerm.isSign] at h₁
              have ⟨beqT, h₁'⟩ := (Bool.and_eq_true _ _).mp h₁
              clear h₁; cases beqT
              dsimp [LamTerm.rwGenAt]
              cases h₂ : LamTerm.rwGenAt occ modify argI <;> intro h <;> cases h
              case refl argI' =>
                have IH' := @IH weaken? (!weaken?') occ H hl' argI argI';
                clear IH; rw [← Bool.not_beq_swap] at IH';
                dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [h₁'] at IH'; dsimp at IH'
                intro lctx wfNArgI; cases wfNArgI.getFn.getBase.getPcst; have .ofApp _ _ wfArgI := wfNArgI
                have IH := IH' h₂ lctx wfArgI; clear IH'
                cases weaken?'
                case true =>
                  have ⟨.ofApp _ (.ofApp _ _ wfArgI') _, _⟩ := IH
                  apply LamValid.mpLamEquiv IH (LamEquiv.not_imp_not wfArgI wfArgI').symm
                case false =>
                  have ⟨.ofApp _ _ wfArgI', _⟩ := IH
                  apply LamValid.mpLamEquiv IH (LamEquiv.not_imp_not wfArgI' wfArgI).symm
          case app sII fnII argII =>
            cases fnII <;> try cases h₁
            case base b' =>
              cases b' <;> try cases h₁
              case pcst p =>
                cases p <;> (try cases h₁) <;> try (
                  unfold LamTerm.isSign at h₁; dsimp at h₁;
                  intro h lctx wfAp; cases wfAp.getFn.getFn.getBase.getPcst; revert h;
                  have .ofApp _ (.ofApp _ _ wfArgII) wfArgI := wfAp)
                case and =>
                  cases b <;> dsimp at h₁ <;> dsimp [LamTerm.rwGenAt]
                  case true =>
                    cases h₂ : LamTerm.rwGenAt occ modify argI <;> intro h <;> cases h
                    case refl argI' =>
                      have IH' := @IH weaken? weaken?' occ H hl' argI argI';
                      clear IH; dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [h₁] at IH'; dsimp at IH'
                      have IH := IH' h₂ lctx wfArgI; clear IH'
                      cases weaken?'
                      case true =>
                        dsimp; have ⟨.ofApp _ _ wfArgI', _⟩ := IH
                        apply LamValid.impLift (LamValid.and_imp_and_of_right_imp wfArgII wfArgI wfArgI') IH
                      case false =>
                        dsimp; have ⟨.ofApp _ (.ofApp _ _ wfArgI') _, _⟩ := IH
                        apply LamValid.impLift (LamValid.and_imp_and_of_right_imp wfArgII wfArgI' wfArgI) IH
                  case false =>
                    cases h₂ : LamTerm.rwGenAt occ modify (.app (.base .prop) (.base (.pcst .and)) argII) <;> intro h <;> cases h
                    case refl argAp' =>
                      cases occ <;> try cases h₁
                      case cons b' occ =>
                        dsimp at h₁; have ⟨b't, h₁'⟩ := (Bool.and_eq_true _ _).mp h₁; cases b't; clear h₁
                        have IH' := @IH weaken? weaken?' occ H (Nat.le_of_lt hl') argII;
                        clear IH; dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [h₁'] at IH'; dsimp at IH'
                        dsimp [LamTerm.rwGenAt] at h₂; revert h₂
                        cases h₃ : LamTerm.rwGenAt occ modify argII <;> intro h₂ <;> cases h₂
                        case refl argII' =>
                          have IH := IH' argII' h₃ lctx wfArgII; clear IH'
                          cases weaken?'
                          case true =>
                            dsimp; have ⟨.ofApp _ _ wfArgII', _⟩ := IH
                            apply LamValid.impLift (LamValid.and_imp_and_of_left_imp wfArgII wfArgII' wfArgI) IH
                          case false =>
                            dsimp; have ⟨.ofApp _ (.ofApp _ _ wfArgII') _, _⟩ := IH
                            apply LamValid.impLift (LamValid.and_imp_and_of_left_imp wfArgII' wfArgII wfArgI) IH
                case or =>
                  cases b <;> dsimp at h₁ <;> dsimp [LamTerm.rwGenAt]
                  case true =>
                    cases h₂ : LamTerm.rwGenAt occ modify argI <;> intro h <;> cases h
                    case refl argI' =>
                      have IH' := @IH weaken? weaken?' occ H hl' argI argI';
                      clear IH; dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [h₁] at IH'; dsimp at IH'
                      have IH := IH' h₂ lctx wfArgI; clear IH'
                      cases weaken?'
                      case true =>
                        dsimp; have ⟨.ofApp _ _ wfArgI', _⟩ := IH
                        apply LamValid.impLift (LamValid.or_imp_or_of_right_imp wfArgII wfArgI wfArgI') IH
                      case false =>
                        dsimp; have ⟨.ofApp _ (.ofApp _ _ wfArgI') _, _⟩ := IH
                        apply LamValid.impLift (LamValid.or_imp_or_of_right_imp wfArgII wfArgI' wfArgI) IH
                  case false =>
                    cases h₂ : LamTerm.rwGenAt occ modify (.app (.base .prop) (.base (.pcst .or)) argII) <;> intro h <;> cases h
                    case refl argAp' =>
                      cases occ <;> try cases h₁
                      case cons b' occ =>
                        dsimp at h₁; have ⟨b't, h₁'⟩ := (Bool.and_eq_true _ _).mp h₁; cases b't; clear h₁
                        have IH' := @IH weaken? weaken?' occ H (Nat.le_of_lt hl') argII;
                        clear IH; dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [h₁'] at IH'; dsimp at IH'
                        dsimp [LamTerm.rwGenAt] at h₂; revert h₂
                        cases h₃ : LamTerm.rwGenAt occ modify argII <;> intro h₂ <;> cases h₂
                        case refl argII' =>
                          have IH := IH' argII' h₃ lctx wfArgII; clear IH'
                          cases weaken?'
                          case true =>
                            dsimp; have ⟨.ofApp _ _ wfArgII', _⟩ := IH
                            apply LamValid.impLift (LamValid.or_imp_or_of_left_imp wfArgII wfArgII' wfArgI) IH
                          case false =>
                            dsimp; have ⟨.ofApp _ (.ofApp _ _ wfArgII') _, _⟩ := IH
                            apply LamValid.impLift (LamValid.or_imp_or_of_left_imp wfArgII' wfArgII wfArgI) IH
                case imp =>
                  cases b <;> dsimp at h₁ <;> dsimp [LamTerm.rwGenAt]
                  case true =>
                    cases h₂ : LamTerm.rwGenAt occ modify argI <;> intro h <;> cases h
                    case refl argI' =>
                      have IH' := @IH weaken? weaken?' occ H hl' argI argI';
                      clear IH; dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [h₁] at IH'; dsimp at IH'
                      have IH := IH' h₂ lctx wfArgI; clear IH'
                      cases weaken?'
                      case true =>
                        dsimp; have ⟨.ofApp _ _ wfArgI', _⟩ := IH
                        apply LamValid.impLift (LamValid.imp_trans' wfArgII wfArgI wfArgI') IH
                      case false =>
                        dsimp; have ⟨.ofApp _ (.ofApp _ _ wfArgI') _, _⟩ := IH
                        apply LamValid.impLift (LamValid.imp_trans' wfArgII wfArgI' wfArgI) IH
                  case false =>
                    cases h₂ : LamTerm.rwGenAt occ modify (.app (.base .prop) (.base (.pcst .imp)) argII) <;> intro h <;> cases h
                    case refl argAp' =>
                      cases occ <;> try cases h₁
                      case cons b' occ =>
                        dsimp at h₁; have ⟨b't, h₁'⟩ := (Bool.and_eq_true _ _).mp h₁; cases b't; clear h₁
                        have IH' := @IH weaken? (!weaken?') occ H (Nat.le_of_lt hl') argII;
                        clear IH; dsimp [LamTerm.rwGenAtIfSign] at IH'; rw [← Bool.not_beq_swap, h₁'] at IH'; dsimp at IH'
                        dsimp [LamTerm.rwGenAt] at h₂; revert h₂
                        cases h₃ : LamTerm.rwGenAt occ modify argII <;> intro h₂ <;> cases h₂
                        case refl argII' =>
                          have IH := IH' argII' h₃ lctx wfArgII; clear IH'
                          cases weaken?'
                          case true =>
                            dsimp; have ⟨.ofApp _ (.ofApp _ _ wfArgII') _, _⟩ := IH
                            apply LamValid.impLift (LamValid.imp_trans wfArgII' wfArgII wfArgI) IH
                          case false =>
                            dsimp; have ⟨.ofApp _ _ wfArgII', _⟩ := IH
                            apply LamValid.impLift (LamValid.imp_trans wfArgII wfArgII' wfArgI) IH
      | false => intro h; cases h

-- Boolean theorems
def LamTerm.emb : LamTerm := .mkForallEF (.base .bool) (.mkOr
  (.mkEq (.base .bool) (.bvar 0) (.base .trueb))
  (.mkEq (.base .bool) (.bvar 0) (.base .falseb)))

def LamWF.emb : LamWF ltv ⟨lctx, LamTerm.emb, .base .prop⟩ :=
  .mkForallEF (.mkOr (.mkEq (.ofBVar 0) (.ofBase .ofTrueB)) (.mkEq (.ofBVar 0) (.ofBase .ofFalseB)))

theorem LamThmValid.emb : LamThmValid lval [] LamTerm.emb := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.emb; intro lctxTerm
  intro b; cases b
  case up b =>
    cases b
    case false => apply Or.inr; rfl
    case true => apply Or.inl; rfl

def LamTerm.false_ne_true : LamTerm := .mkNot (.mkEq (.base .bool) (.base .falseb) (.base .trueb))

def LamWF.false_ne_true : LamWF ltv ⟨lctx, LamTerm.false_ne_true, .base .prop⟩ :=
  .mkNot (.mkEq (.ofBase .ofFalseB) (.ofBase .ofTrueB))

theorem LamThmValid.false_ne_true : LamThmValid lval [] LamTerm.false_ne_true := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.false_ne_true; intro lctxTerm
  intro h; cases h

def LamTerm.not_true_eq_false : LamTerm := .mkEq (.base .bool)
  (.app (.base .bool) (.base .notb) (.base .trueb)) (.base .falseb)

def LamWF.not_true_eq_false : LamWF ltv ⟨lctx, LamTerm.not_true_eq_false, .base .prop⟩ :=
  .mkEq (.ofApp _ (.ofBase .ofNotB) (.ofBase .ofTrueB)) (.ofBase .ofFalseB)

theorem LamThmValid.not_true_eq_false : LamThmValid lval [] LamTerm.not_true_eq_false := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.not_true_eq_false; intro _; rfl

def LamTerm.not_false_eq_true : LamTerm := .mkEq (.base .bool)
  (.app (.base .bool) (.base .notb) (.base .falseb)) (.base .trueb)

def LamWF.not_false_eq_true : LamWF ltv ⟨lctx, LamTerm.not_false_eq_true, .base .prop⟩ :=
  .mkEq (.ofApp _ (.ofBase .ofNotB) (.ofBase .ofFalseB)) (.ofBase .ofTrueB)

theorem LamThmValid.not_false_eq_true : LamThmValid lval [] LamTerm.not_false_eq_true := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.not_false_eq_true; intro _; rfl

def LamTerm.false_and_eq_false : LamTerm := .mkForallEF (.base .bool) (.mkEq (.base .bool)
  (.app (.base .bool) (.app (.base .bool) (.base .andb) (.base .falseb)) (.bvar 0)) (.base .falseb))

def LamWF.false_and_eq_false : LamWF ltv ⟨lctx, LamTerm.false_and_eq_false, .base .prop⟩ :=
  .mkForallEF (.mkEq (.ofApp _ (.ofApp _ (.ofBase .ofAndB) (.ofBase .ofFalseB)) (.ofBVar 0)) (.ofBase .ofFalseB))

theorem LamThmValid.false_and_eq_false : LamThmValid lval [] LamTerm.false_and_eq_false := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.false_and_eq_false; intro _ b; rfl

def LamTerm.true_and_eq_id : LamTerm := .mkForallEF (.base .bool) (.mkEq (.base .bool)
  (.app (.base .bool) (.app (.base .bool) (.base .andb) (.base .trueb)) (.bvar 0)) (.bvar 0))

def LamWF.true_and_eq_id : LamWF ltv ⟨lctx, LamTerm.true_and_eq_id, .base .prop⟩ :=
  .mkForallEF (.mkEq (.ofApp _ (.ofApp _ (.ofBase .ofAndB) (.ofBase .ofTrueB)) (.ofBVar 0)) (.ofBVar 0))

theorem LamThmValid.true_and_eq_id : LamThmValid lval [] LamTerm.true_and_eq_id := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.true_and_eq_id; intro _ b; rfl

def LamTerm.false_or_eq_id : LamTerm := .mkForallEF (.base .bool) (.mkEq (.base .bool)
  (.app (.base .bool) (.app (.base .bool) (.base .orb) (.base .falseb)) (.bvar 0)) (.bvar 0))

def LamWF.false_or_eq_id : LamWF ltv ⟨lctx, LamTerm.false_or_eq_id, .base .prop⟩ :=
  .mkForallEF (.mkEq (.ofApp _ (.ofApp _ (.ofBase .ofOrB) (.ofBase .ofFalseB)) (.ofBVar 0)) (.ofBVar 0))

theorem LamThmValid.false_or_eq_id : LamThmValid lval [] LamTerm.false_or_eq_id := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.false_or_eq_id; intro _ b; rfl

def LamTerm.true_or_eq_true : LamTerm := .mkForallEF (.base .bool) (.mkEq (.base .bool)
  (.app (.base .bool) (.app (.base .bool) (.base .orb) (.base .trueb)) (.bvar 0)) (.base .trueb))

def LamWF.true_or_eq_true : LamWF ltv ⟨lctx, LamTerm.true_or_eq_true, .base .prop⟩ :=
  .mkForallEF (.mkEq (.ofApp _ (.ofApp _ (.ofBase .ofOrB) (.ofBase .ofTrueB)) (.ofBVar 0)) (.ofBase .ofTrueB))

theorem LamThmValid.true_or_eq_true : LamThmValid lval [] LamTerm.true_or_eq_true := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.true_or_eq_true; intro _ b; rfl

def LamTerm.ofPropSpec : LamTerm := .mkForallEF (.base .prop) (.mkEq (.base .prop)
  (.mkEq (.base .bool) (.app (.base .prop) (.base .ofProp) (.bvar 0)) (.base .trueb)) (.bvar 0))

def LamWF.ofPropSpec : LamWF ltv ⟨lctx, LamTerm.ofPropSpec, .base .prop⟩ :=
  .mkForallEF (.mkEq (.mkEq (.ofApp _ (.ofBase .ofOfProp) (.ofBVar 0)) (.ofBase .ofTrueB)) (.ofBVar 0))

theorem LamThmValid.ofPropSpec : LamThmValid lval [] LamTerm.ofPropSpec := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.ofPropSpec; intro _ x
  apply GLift.down.inj; apply propext (Iff.intro ?mp ?mpr)
  case mp =>
    intro h; apply (Bool.ofProp_spec x.down).mp (_root_.congrArg (f:=GLift.down) h)
  case mpr =>
    intro h; apply GLift.down.inj; apply (Bool.ofProp_spec x.down).mpr h

def LamTerm.boolFacts : LamTerm := .mkAnd (.mkAnd
  (.mkAnd (.mkAnd emb false_ne_true) (.mkAnd not_true_eq_false not_false_eq_true))
  (.mkAnd (.mkAnd false_and_eq_false true_and_eq_id) (.mkAnd false_or_eq_id true_or_eq_true)))
  LamTerm.ofPropSpec

def LamWF.boolFacts : LamWF ltv ⟨lctx, LamTerm.boolFacts, .base .prop⟩ := .mkAnd (.mkAnd
  (.mkAnd (.mkAnd emb false_ne_true) (.mkAnd not_true_eq_false not_false_eq_true))
  (.mkAnd (.mkAnd false_and_eq_false true_and_eq_id) (.mkAnd false_or_eq_id true_or_eq_true)))
  ofPropSpec

theorem LamTerm.maxEVarSucc_boolFacts : maxEVarSucc boolFacts = 0 := rfl

theorem LamThmValid.boolFacts : LamThmValid lval [] LamTerm.boolFacts := by
  intro lctx'; rw [pushLCtxs_nil]; dsimp [LamTerm.boolFacts]
  rw [LamValid.and_equiv, LamValid.and_equiv, LamValid.and_equiv, LamValid.and_equiv]
  rw [LamValid.and_equiv, LamValid.and_equiv, LamValid.and_equiv, LamValid.and_equiv]
  apply And.intro (And.intro
    (And.intro (And.intro (emb _) (false_ne_true _)) (And.intro (not_true_eq_false _) (not_false_eq_true _)))
    (And.intro (And.intro (false_and_eq_false _) (true_and_eq_id _)) (And.intro (false_or_eq_id _) (true_or_eq_true _))))
    (ofPropSpec _)

def LamTerm.iteSpec (s : LamSort) : LamTerm :=
  .mkForallEF s (.mkForallEF s (.mkAnd
      (.mkEq s (.mkIte s (.base .trueE) (.bvar 0) (.bvar 1)) (.bvar 0))
      (.mkEq s (.mkIte s (.base .falseE) (.bvar 0) (.bvar 1)) (.bvar 1))))

def LamWF.iteSpec (s : LamSort) : LamWF ltv ⟨lctx, .iteSpec s, .base .prop⟩ :=
  .mkForallEF (.mkForallEF (.mkAnd
    (.mkEq (.mkIte (.ofBase .ofTrueE) (.ofBVar 0) (.ofBVar 1)) (.ofBVar 0))
    (.mkEq (.mkIte (.ofBase .ofFalseE) (.ofBVar 0) (.ofBVar 1)) (.ofBVar 1))))

theorem LamTerm.maxEVarSucc_iteSpec (s : LamSort) : maxEVarSucc (iteSpec s) = 0 := rfl

theorem LamThmValid.iteSpec (s : LamSort) : LamThmValid lval [] (LamTerm.iteSpec s) := by
  intro lctx'; rw [pushLCtxs_nil]; exists LamWF.iteSpec s; intro _ x y; apply And.intro
  case left => apply Bool.ite'_eq_true; exact True.intro
  case right => apply Bool.ite'_eq_false; exact id

end Auto.Embedding.Lam
