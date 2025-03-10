import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

def LamTerm.mapBVarAt (idx : Nat) (f : Nat → Nat) (t : LamTerm) : LamTerm :=
  match t with
  | .atom n       => .atom n
  | .etom n       => .etom n
  | .base b       => .base b
  | .bvar n       => .bvar (mapAt idx f n)
  | .lam s t      => .lam s (t.mapBVarAt (.succ idx) f)
  | .app s fn arg => .app s (fn.mapBVarAt idx f) (arg.mapBVarAt idx f)

theorem LamTerm.maxEVarSucc_mapBVarAt : {t : LamTerm} → (LamTerm.mapBVarAt idx f t).maxEVarSucc = t.maxEVarSucc
| .atom n => rfl
| .etom n => rfl
| .base b => rfl
| .bvar n => rfl
| .lam _ t => LamTerm.maxEVarSucc_mapBVarAt (t:=t)
| .app s fn arg => by
  dsimp [mapBVarAt, maxEVarSucc];
  rw [LamTerm.maxEVarSucc_mapBVarAt (t:=fn)]
  rw [LamTerm.maxEVarSucc_mapBVarAt (t:=arg)]

def LamTerm.mapBVar := LamTerm.mapBVarAt 0

def LamWF.mapBVarAt (covP : coPair f restore) (idx : Nat)
  {lamVarTy lctx} (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨lctx, rterm, rty⟩) →
  LamWF lamVarTy ⟨restoreAt idx restore lctx, rterm.mapBVarAt idx f, rty⟩
| .ofAtom n => .ofAtom n
| .ofEtom n => .ofEtom n
| .ofBase b => .ofBase b
| .ofBVar n => coPairAt.ofcoPair covP idx lctx n ▸ .ofBVar (mapAt idx f n)
| .ofLam (body:=body) bodyTy wfBody =>
  .ofLam bodyTy (restoreAt_succ_pushLCtx_Fn restore _ _ _ ▸ LamWF.mapBVarAt covP (.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  .ofApp argTy' (LamWF.mapBVarAt covP idx _ HFn) (LamWF.mapBVarAt covP idx _ HArg)

def LamWF.fromMapBVarAtAux
  (covP : coPair f restore) (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
  (hLCtx : lctx' = restoreAt idx restore lctx)
  (hRTerm : rterm' = rterm.mapBVarAt idx f)
  (HWF : LamWF lamVarTy ⟨lctx', rterm', rty⟩) : LamWF lamVarTy ⟨lctx, rterm, rty⟩ := by
  revert hRTerm
  match HWF with
  | .ofAtom _ => intro hRTerm; cases rterm <;> try cases hRTerm <;> apply ofAtom
  | .ofEtom _ => intro hRTerm; cases rterm <;> try cases hRTerm <;> apply ofEtom
  | .ofBase H => intro hRTerm; cases rterm <;> try cases hRTerm <;> apply ofBase H
  | .ofBVar _ =>
    intro hRTerm; cases rterm <;> try cases hRTerm
    rw [hLCtx, coPairAt.ofcoPair covP idx lctx]
    apply ofBVar
  | .ofLam bodyTy wfBody =>
    intro hRTerm; cases rterm <;> try cases hRTerm
    rw [hLCtx, ← restoreAt_succ_pushLCtx_Fn restore _ _ _] at wfBody
    apply LamWF.ofLam bodyTy
    apply LamWF.fromMapBVarAtAux covP (.succ idx) _ rfl rfl wfBody
  | .ofApp _ HFn HArg =>
    intro hRTerm; cases rterm <;> try cases hRTerm
    exact LamWF.ofApp _
      (LamWF.fromMapBVarAtAux covP idx _ hLCtx rfl HFn)
      (LamWF.fromMapBVarAtAux covP idx _ hLCtx rfl HArg)

def LamWF.fromMapBVarAt
  (covP : coPair f restore) (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
  (HWF : LamWF lamVarTy ⟨restoreAt idx restore lctx, rterm.mapBVarAt idx f, rty⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rty⟩ := LamWF.fromMapBVarAtAux covP idx rterm rfl rfl HWF

theorem LamWF.mapBVarAt.correct (lval : LamValuation.{u}) {restoreDep : _}
  (covPD : coPairDep (LamSort.interp lval.tyVal) f restore restoreDep) (idx : Nat)
  {lctxTy : Nat → LamSort} (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) :
  (rterm : LamTerm) → (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) →
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (restoreAt idx restore lctxTy)
    (restoreAtDep idx restoreDep lctxTerm)
    (mapBVarAt (restore:=restore) covPD.left idx rterm HWF)
| .atom _, .ofAtom _ => rfl
| .etom _, .ofEtom _ => rfl
| .base _, .ofBase _ => rfl
| .bvar n, .ofBVar _ => by
  dsimp [mapBVarAt, LamWF.interp]
  apply eq_of_heq; apply HEq.symm (HEq.trans (interp_bvar _) _)
  apply (coPairDepAt.ofCoPairDep covPD).right
| .lam argTy body, .ofLam bodyTy wfBody => by
  apply funext; intros x; dsimp [LamWF.interp]
  apply Eq.trans (LamWF.mapBVarAt.correct _ covPD (.succ idx) _ _ wfBody)
  apply LamWF.interp_substLCtxTerm_rec
  apply restoreAtDep_succ_pushLCtxDep_Fn
| .app s fn arg, .ofApp _ wfFn wfArg => by
  dsimp [LamWF.interp]
  let IHFn := LamWF.mapBVarAt.correct lval covPD idx lctxTerm fn wfFn
  let IHArg := LamWF.mapBVarAt.correct lval covPD idx lctxTerm arg wfArg
  rw [IHFn]; rw [IHArg]; rfl

/-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (?n + lvl)` -/
def LamTerm.bvarLiftsIdx (idx lvl : Nat) := LamTerm.mapBVarAt idx (fun x => Nat.add x lvl)

theorem LamTerm.bvarLiftsIdx_eq_bvar :
  bvarLiftsIdx idx lvl t = bvar n ↔
  (n < idx ∧ t = .bvar n) ∨ (n ≥ idx + lvl ∧ t = .bvar (n - lvl)) := by
  cases t <;> simp [bvarLiftsIdx, mapBVarAt]
  case bvar n' =>
    dsimp [mapAt]; cases h₁ : idx.ble n' <;> dsimp
    case false =>
      have h₁' := Nat.lt_of_ble_eq_false h₁; clear h₁
      apply Iff.intro
      case mp => intro h; cases h; apply Or.inl (And.intro h₁' rfl)
      case mpr =>
        intro h; cases h
        case inl h => apply h.right
        case inr h =>
          apply False.elim (Nat.not_le_of_lt h₁' _); cases h.right
          apply Nat.le_sub_of_add_le h.left
    case true =>
      have h₁' := Nat.le_of_ble_eq_true h₁; clear h₁
      rw [Nat.add_assoc, Nat.add_comm lvl idx, ← Nat.add_assoc]
      rw [Nat.sub_add_cancel h₁']; apply Iff.intro
      case mp =>
        intro h; cases h; apply Or.inr (And.intro (Nat.add_le_add_right h₁' _) _)
        rw [Nat.add_sub_cancel]
      case mpr =>
        intro h; cases h
        case inl h => cases h.right; apply False.elim (Nat.not_le_of_lt h.left h₁')
        case inr h =>
          cases h.right; rw [Nat.sub_add_cancel]; apply Nat.le_trans _ h.left
          apply Nat.le_add_left

theorem LamTerm.maxEVarSucc_bvarLiftsIdx {t : LamTerm} :
  (t.bvarLiftsIdx idx lvl).maxEVarSucc = t.maxEVarSucc := maxEVarSucc_mapBVarAt

@[reducible] def LamTerm.bvarLifts := LamTerm.bvarLiftsIdx 0

theorem LamTerm.maxEVarSucc_bvarLifts {t : LamTerm} :
  (t.bvarLifts lvl).maxEVarSucc = t.maxEVarSucc := maxEVarSucc_mapBVarAt

/-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (Nat.succ ?n)` -/
def LamTerm.bvarLiftIdx (idx : Nat) (t : LamTerm) := LamTerm.bvarLiftsIdx idx 1 t

theorem LamTerm.maxEVarSucc_bvarLiftIdx {t : LamTerm} :
  (t.bvarLiftIdx idx).maxEVarSucc = t.maxEVarSucc := maxEVarSucc_mapBVarAt

@[reducible] def LamTerm.bvarLift := LamTerm.bvarLiftIdx 0

theorem LamTerm.maxEVarSucc_bvarLift {t : LamTerm} :
  t.bvarLift.maxEVarSucc = t.maxEVarSucc := maxEVarSucc_mapBVarAt

theorem LamTerm.bvarLiftsIdx_atom :
  LamTerm.bvarLiftsIdx idx lvl (.atom n) = .atom n := rfl

theorem LamTerm.bvarLiftIdx_atom :
  LamTerm.bvarLiftIdx idx (.atom n) = .atom n := rfl

theorem LamTerm.bvarLiftsIdx_etom :
  LamTerm.bvarLiftsIdx idx lvl (.etom n) = .etom n := rfl

theorem LamTerm.bvarLiftIdx_etom :
  LamTerm.bvarLiftIdx idx (.etom n) = .etom n := rfl

theorem LamTerm.bvarLiftsIdx_base :
  LamTerm.bvarLiftsIdx idx lvl (.base b) = .base b := rfl

theorem LamTerm.bvarLiftIdx_base :
  LamTerm.bvarLiftIdx idx (.base b) = .base b := rfl

theorem LamTerm.bvarLiftsIdx_bvar :
  LamTerm.bvarLiftsIdx idx lvl (.bvar n) = .bvar (mapAt idx (fun x => x + lvl) n) := rfl

theorem LamTerm.bvarLiftIdx_bvar :
  LamTerm.bvarLiftIdx idx (.bvar n) = .bvar (mapAt idx (fun x => x.succ) n) := rfl

theorem LamTerm.bvarLiftsIdx_app :
  LamTerm.bvarLiftsIdx idx lvl (.app s fn arg) = .app s (.bvarLiftsIdx idx lvl fn) (.bvarLiftsIdx idx lvl arg) := rfl

theorem LamTerm.bvarLiftIdx_app :
  LamTerm.bvarLiftIdx idx (.app s fn arg) = .app s (.bvarLiftIdx idx fn) (.bvarLiftIdx idx arg) := rfl

theorem LamTerm.bvarLiftsIdx_lam :
  LamTerm.bvarLiftsIdx idx lvl (.lam s body) = .lam s (.bvarLiftsIdx idx.succ lvl body) := rfl

theorem LamTerm.bvarLiftIdx_lam :
  LamTerm.bvarLiftIdx idx (.lam s body) = .lam s (.bvarLiftIdx idx.succ body) := rfl

theorem LamTerm.bvarLiftsIdx_zero (idx : Nat) : (t : LamTerm) → LamTerm.bvarLiftsIdx idx 0 t = t
| .atom n => rfl
| .etom n => rfl
| .base b => rfl
| .bvar n => by
  dsimp [bvarLiftsIdx, mapBVarAt]
  rw [mapAt_id_eq_id']; rfl
| .lam s t => by
  dsimp [bvarLiftsIdx, mapBVarAt];
  have IH := LamTerm.bvarLiftsIdx_zero (.succ idx) t
  dsimp [bvarLiftsIdx] at IH
  rw [IH]
| .app s fn arg => by
  dsimp [bvarLiftsIdx, mapBVarAt];
  have IHFn := LamTerm.bvarLiftsIdx_zero idx fn
  have IHArg := LamTerm.bvarLiftsIdx_zero idx arg
  dsimp [bvarLiftsIdx] at IHFn IHArg
  rw [IHFn];
  rw [IHArg];

theorem LamTerm.bvarLifts_zero : LamTerm.bvarLifts 0 t = t := LamTerm.bvarLiftsIdx_zero 0 t

theorem LamTerm.bvarLiftsIdx_succ_l (idx lvl : Nat) (t : LamTerm) :
  LamTerm.bvarLiftsIdx idx (.succ lvl) t = LamTerm.bvarLiftsIdx idx lvl (LamTerm.bvarLiftIdx idx t) := by
  induction t generalizing idx lvl
  case atom n => rfl
  case etom n => rfl
  case base b => rfl
  case bvar n =>
    dsimp [bvarLiftsIdx, bvarLiftIdx, mapBVarAt];
    have hAddAt := addAt_succ_r lvl idx n
    dsimp [addAt] at hAddAt; rw [hAddAt]
  case lam s t IH =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IH
    rw [IH]; rfl
  case app fn arg IHFn IHArg =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IHFn IHArg;
    rw [IHFn, IHArg]; rfl

theorem LamTerm.bvarLifts_succ_l : LamTerm.bvarLifts (.succ lvl) t = LamTerm.bvarLifts lvl (LamTerm.bvarLift t) :=
  LamTerm.bvarLiftsIdx_succ_l 0 lvl t

theorem LamTerm.bvarLiftsIdx_succ_r (idx lvl : Nat) (t : LamTerm) :
  LamTerm.bvarLiftsIdx idx (.succ lvl) t = LamTerm.bvarLiftIdx idx (LamTerm.bvarLiftsIdx idx lvl t) := by
  induction t generalizing idx lvl
  case atom n => rfl
  case etom n => rfl
  case base b => rfl
  case bvar n =>
    dsimp [bvarLiftsIdx, bvarLiftIdx, mapBVarAt];
    have hAddAt := addAt_succ_l lvl idx n
    dsimp [addAt] at hAddAt; rw [hAddAt];
  case lam s t IH =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IH
    rw [IH]; rfl
  case app fn arg IHFn IHArg =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IHFn IHArg;
    rw [IHFn, IHArg]; rfl

theorem LamTerm.bvarLifts_succ_r : LamTerm.bvarLifts (.succ lvl) t = LamTerm.bvarLift (LamTerm.bvarLifts lvl t) :=
  LamTerm.bvarLiftsIdx_succ_r 0 lvl t

theorem LamTerm.bvarLifts_add :
  LamTerm.bvarLiftsIdx idx (lvl₁ + lvl₂) t = LamTerm.bvarLiftsIdx idx lvl₁ (LamTerm.bvarLiftsIdx idx lvl₂ t) := by
  rw [Nat.add_comm]; induction lvl₁
  case zero => rw [bvarLiftsIdx_zero]; rfl
  case succ lvl₁ IH =>
    rw [Nat.add_succ]; rw [bvarLiftsIdx_succ_r, bvarLiftsIdx_succ_r, IH]

def LamWF.bvarLiftsIdx
  {lamVarTy lctx} {idx lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxsAt xs idx lctx, rterm.bvarLiftsIdx idx lvl, rTy⟩ :=
  LamWF.mapBVarAt (coPair.ofPushsPops _ _ heq) idx rterm HWF

def LamWF.fromBVarLiftsIdx
  {lamVarTy lctx} {idx lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtxsAt xs idx lctx, rterm.bvarLiftsIdx idx lvl, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromMapBVarAt (coPair.ofPushsPops _ _ heq) idx rterm HWF

theorem LamWF.interp_bvarLiftsIdx
  (lval : LamValuation.{u}) {idx lvl : Nat}
  {tys : List LamSort} (xs : HList (LamSort.interp lval.tyVal) tys) (heq : tys.length = lvl)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxsAt tys idx lctxTy) (pushLCtxsAtDep xs idx lctxTerm)
    (bvarLiftsIdx heq rterm HWF) :=
  LamWF.mapBVarAt.correct lval (coPairDep.ofPushsDepPopsDep _ _ heq) idx lctxTerm rterm HWF

def LamWF.bvarLifts
  {lamVarTy lctx} {lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxs xs lctx, rterm.bvarLifts lvl, rTy⟩ :=
  Eq.mp (by rw [pushLCtxsAt_zero]) (LamWF.bvarLiftsIdx (idx:=0) heq rterm HWF)

def LamWF.fromBVarLifts
  {lamVarTy lctx} {lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtxs xs lctx, rterm.bvarLifts lvl, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromBVarLiftsIdx (idx:=0) heq rterm (Eq.mp (by rw [pushLCtxsAt_zero]) HWF)

theorem LamWF.interp_bvarLifts
  (lval : LamValuation.{u}) {lvl : Nat}
  {tys : List LamSort} (xs : HList (LamSort.interp lval.tyVal) tys) (heq : tys.length = lvl)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxs tys lctxTy) (pushLCtxsDep xs lctxTerm)
    (bvarLifts heq rterm HWF) := by
  apply Eq.trans (LamWF.interp_bvarLiftsIdx (idx:=0) _ xs heq _ lctxTerm _ _)
  apply interp_substLCtxTerm; rw [pushLCtxsAt_zero]; apply pushLCtxsAtDep_zero

def LamWF.bvarLiftIdx {lamVarTy lctx} (idx : Nat)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxAt s idx lctx, rterm.bvarLiftIdx idx, rTy⟩ :=
  LamWF.mapBVarAt (coPair.ofPushPop _) idx rterm HWF

def LamWF.fromBVarLiftIdx {lamVarTy lctx} (idx : Nat)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtxAt s idx lctx, rterm.bvarLiftIdx idx, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromMapBVarAt (coPair.ofPushPop _) idx rterm HWF

theorem LamWF.interp_bvarLiftIdx
  (lval : LamValuation.{u}) {idx : Nat}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.tyVal xty)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxAt xty idx lctxTy) (pushLCtxAtDep x idx lctxTerm)
    (bvarLiftIdx idx rterm HWF) :=
  LamWF.mapBVarAt.correct lval (coPairDep.ofPushDepPopDep _) idx lctxTerm rterm HWF

def LamWF.bvarLift {lamVarTy lctx}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtx s lctx, rterm.bvarLift, rTy⟩ :=
  Eq.mp (by rw [pushLCtxAt_zero]) (LamWF.bvarLiftIdx (s:=s) 0 _ HWF)

def LamWF.fromBVarLift {lamVarTy lctx}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtx s lctx, rterm.bvarLift, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromBVarLiftIdx (s:=s) 0 _ (Eq.mp (by rw [pushLCtxAt_zero]) HWF)

theorem LamWF.interp_bvarLift
  (lval : LamValuation.{u})
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.tyVal xty)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtx xty lctxTy) (pushLCtxDep x lctxTerm) (bvarLift rterm HWF) := by
  apply Eq.trans (LamWF.interp_bvarLiftIdx (idx:=0) _ _ lctxTerm x _ _)
  apply interp_substLCtxTerm; rw [pushLCtxAt_zero]; apply pushLCtxAtDep_zero

def LamWF.pushLCtxAt_ofBVar :
  LamWF lamVarTy ⟨pushLCtxAt s idx lctx, .bvar idx, s⟩ :=
  Eq.mp (by rw [pushLCtxAt_eq]) (@LamWF.ofBVar lamVarTy (pushLCtxAt s idx lctx) idx)

def LamWF.pushLCtx_ofBVar :
  LamWF lamVarTy ⟨pushLCtx s lctx, .bvar 0, s⟩ :=
  Eq.mp (by rw [pushLCtx_zero]) (@LamWF.ofBVar lamVarTy (pushLCtx s lctx) 0)

def LamTerm.bvarLowersIdx? (idx : Nat) (lvl : Nat) : LamTerm → Option LamTerm
| .atom n => .some (.atom n)
| .etom n => .some (.etom n)
| .base b => .some (.base b)
| .bvar n =>
  match idx.ble n with
  | true =>
    match (idx + lvl).ble n with
    | true => .some (.bvar (n - lvl))
    | false => .none
  | false => .some (.bvar n)
| .lam s body =>
  match bvarLowersIdx? (.succ idx) lvl body with
  | .some body' => .some (.lam s body')
  | .none => .none
| .app s fn arg =>
  match bvarLowersIdx? idx lvl fn, bvarLowersIdx? idx lvl arg with
  | .some fn', .some arg' => .some (.app s fn' arg')
  | _, _ => .none

theorem LamTerm.bvarLowersIdx?_bvar_eq_some :
  bvarLowersIdx? idx lvl (bvar n) = .some t ↔
  (n < idx ∧ t = .bvar n) ∨ (n ≥ idx + lvl ∧ t = .bvar (n - lvl)) := by
  dsimp [bvarLowersIdx?]; cases h₁ : idx.ble n <;> simp
  case false =>
    have h₁' := Nat.lt_of_ble_eq_false h₁; clear h₁
    apply Iff.intro
    case mp =>
      intro h; cases h; apply Or.inl; apply And.intro h₁' rfl
    case mpr =>
      intro h; cases h
      case inl h' => apply h'.right.symm
      case inr h' =>
        have h₁ := Nat.not_le_of_lt h₁'
        have h'' := Nat.le_trans (Nat.le_add_right _ _) h'.left
        apply False.elim (h₁ h'')
  case true =>
    have h₁' := Nat.le_of_ble_eq_true h₁; clear h₁
    cases h₂ : (idx + lvl).ble n <;> simp
    case false =>
      have h₂' := Nat.lt_of_ble_eq_false h₂; clear h₂
      apply And.intro ?nlt ?nge
      case nlt => intro h; have h' := Nat.not_le_of_lt h; contradiction
      case nge => intro h; have h' := Nat.not_le_of_lt h₂'; contradiction
    case true =>
      have h₂' := Nat.le_of_ble_eq_true h₂; clear h₂
      apply Iff.intro <;> intro h
      case mp => cases h; apply Or.inr (And.intro h₂' rfl)
      case mpr =>
        cases h
        case inl h => have h' := Nat.not_le_of_lt h.left; apply False.elim (h' h₁')
        case inr h => apply h.right.symm

theorem LamTerm.bvarLowersIdx?_spec :
  bvarLowersIdx? idx lvl t = .some t' ↔ bvarLiftsIdx idx lvl t' = t := by
  induction t generalizing idx lvl t' <;> try (
    dsimp [bvarLowersIdx?]; cases t' <;> simp <;> try (intro h; cases h)
    simp [bvarLiftsIdx, mapBVarAt]; apply Iff.intro <;> apply Eq.symm)
  case bvar n =>
    rw [LamTerm.bvarLowersIdx?_bvar_eq_some]
    rw [LamTerm.bvarLiftsIdx_eq_bvar]
  case lam s body IH =>
    dsimp [bvarLowersIdx?]
    cases t' <;> try (
      simp [bvarLiftsIdx, mapBVarAt]
      cases h₁ : bvarLowersIdx? (Nat.succ idx) lvl body <;> (solve | simp))
    case lam s' body' =>
      rw [bvarLiftsIdx_lam]; simp
      rw [← IH]; cases h : bvarLowersIdx? (Nat.succ idx) lvl body
      case none => simp
      case some bodyL => simp; intro _; apply Iff.intro Eq.symm Eq.symm
  case app s fn arg IHFn IHArg =>
    dsimp [bvarLowersIdx?]
    cases t' <;> try (
      simp [bvarLiftsIdx, mapBVarAt];
      cases h₁ : bvarLowersIdx? idx lvl fn <;>
      cases h₂ : bvarLowersIdx? idx lvl arg <;> (solve | simp))
    case app s' fn' arg' =>
      rw [bvarLiftsIdx_app]; simp; rw [← IHFn, ← IHArg]
      cases h₁ : bvarLowersIdx? idx lvl fn <;> simp
      case some fnL =>
        cases h₂ : bvarLowersIdx? idx lvl arg <;> simp
        intro _ _; apply Iff.intro Eq.symm Eq.symm

theorem LamTerm.maxEVarSucc_bvarLowersIdx?
  (heq : LamTerm.bvarLowersIdx? idx lvl t = .some t') : t'.maxEVarSucc = t.maxEVarSucc := by
  cases bvarLowersIdx?_spec.mp heq; rw [maxEVarSucc_bvarLiftsIdx]

def LamTerm.bvarLowers? (lvl : Nat) (t : LamTerm) := bvarLowersIdx? 0 lvl t

theorem LamTerm.bvarLowers?_spec : bvarLowers? lvl t = .some t' ↔ bvarLifts lvl t' = t :=
  bvarLowersIdx?_spec

theorem LamTerm.maxEVarSucc_bvarLowers?
  (heq : LamTerm.bvarLowers? lvl t = .some t') : t'.maxEVarSucc = t.maxEVarSucc :=
  LamTerm.maxEVarSucc_bvarLowersIdx? heq

def LamTerm.bvarLowerIdx? (idx : Nat) (t : LamTerm) := bvarLowersIdx? idx 1 t

theorem LamTerm.bvarLowerIdx?_spec : bvarLowerIdx? idx t = .some t' ↔ bvarLiftIdx idx t' = t :=
  bvarLowersIdx?_spec

theorem LamTerm.maxEVarSucc_bvarLowerIdx?
  (heq : LamTerm.bvarLowerIdx? idx t = .some t') : t'.maxEVarSucc = t.maxEVarSucc :=
  LamTerm.maxEVarSucc_bvarLowersIdx? heq

def LamTerm.bvarLower? := bvarLowerIdx? 0

theorem LamTerm.bvarLower?_spec : bvarLower? t = .some t' ↔ bvarLift t' = t :=
  bvarLowersIdx?_spec

theorem LamTerm.maxEVarSucc_bvarLower?
  (heq : LamTerm.bvarLower? t = .some t') : t'.maxEVarSucc = t.maxEVarSucc :=
  LamTerm.maxEVarSucc_bvarLowersIdx? heq

private def getILSortString : LamBaseTerm → String
| .eq s      => s!"{s}"
| .forallE s => s!"{s}"
| .existE s  => s!"{s}"
| .ite s     => s!"{s}"
| _ => "❌"

-- Unfortunately, we have to define `bvarLift` before defining `toStringLCtx`
partial def LamTerm.toStringLCtx (lctx : Nat) : LamTerm → String
| .atom n => s!"!{n}"
| .etom n => s!"?{n}"
| .base b =>
  match b.beq .trueE || b.beq .falseE with
  | true => s!"{b}"
  | false => s!"({b})"
| .bvar m =>
  if m < lctx then
    s!"x{lctx - m - 1}"
  else
    s!"⟨{m - lctx}⟩"
| .lam s t => s!"(λx{lctx} : {s}, {toStringLCtx (.succ lctx) t})"
| t@(.app ..) =>
  let fn := t.getAppFn
  let args := t.getAppArgs
  match fn with
  | .base b =>
    -- Nice trick
    match (b.lamCheck Inhabited.default).getArgTys.length with
    | 0 => "❌"
    | 1 =>
      match args with
      | [(_, arg)] =>
        match b.isForallE || b.isForallEI || b.isExistE || b.isExistEI with
        | true =>
          match arg with
          | .lam s t => s!"({b} x{lctx} : {s}, {toStringLCtx (.succ lctx) t})"
          | arg =>
            let arg's := toStringLCtx (.succ lctx) arg.bvarLift
            s!"({b}x{lctx} : {getILSortString b}, {arg's} x{lctx})"
        | false =>
          match b with
          | .icst .iabs => s!"|{toStringLCtx lctx arg}|ᵢ"
          | .bvcst (.bvabs _) => s!"|{toStringLCtx lctx arg}|ᵇᵥ"
          | _ => s!"({b} {toStringLCtx lctx arg})"
      | _ => "❌"
    | 2 =>
      match args with
      | [(_, arg)] => s!"({toStringLCtx lctx arg} {b})"
      | [(_, arg₁), (_, arg₂)] => s!"({toStringLCtx lctx arg₁} {b} {toStringLCtx lctx arg₂})"
      | _ => "❌"
    | _ =>
      match b with
      | .ite _ =>
        match args with
        | [] => "❌"
        | [(_, arg)] => s!"({toStringLCtx lctx arg} ? · : ·)"
        | [(_, arg₁), (_, arg₂)] => s!"({toStringLCtx lctx arg₁} ? {toStringLCtx lctx arg₂} : ·)"
        | [(_, arg₁), (_, arg₂), (_, arg₃)] => s!"({toStringLCtx lctx arg₁} ? {toStringLCtx lctx arg₂} : {toStringLCtx lctx arg₃})"
        | (_, arg₁) :: (_, arg₂) :: (_, arg₃) :: tail@(_::_) =>
          let head := s!"({toStringLCtx lctx arg₁} ? {toStringLCtx lctx arg₂} : {toStringLCtx lctx arg₃})"
          "(" ++ head ++ String.join (tail.map (fun (_, arg) => " " ++ toStringLCtx lctx arg)) ++ ")"
      | _ => s!"({b}" ++ String.join (args.map (fun (_, arg) => " " ++ toStringLCtx lctx arg)) ++ ")"
  | fn => "(" ++ toStringLCtx lctx fn ++ " " ++ String.intercalate " " (args.map (fun x => toStringLCtx lctx x.snd)) ++ ")"

def LamTerm.toString := LamTerm.toStringLCtx 0

instance : ToString LamTerm where
  toString := LamTerm.toString

end Auto.Embedding.Lam
