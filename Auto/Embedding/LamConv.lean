import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we reduce the top-level redex
-- Suppose `lctx ⊢ body : ty`. It's easy to see that the `lctx` which `arg`
--   resides in is `fun n => lctx (n + idx + 1)` and the type of `arg` is `lctx idx`
def LamTerm.instantiateAt (idx : Nat) (arg : LamTerm) : (body : LamTerm) → LamTerm
| .atom n        => .atom n
| .base b        => .base b
| .bvar n        => pushLCtxAt (arg.bvarLifts idx) idx LamTerm.bvar n
| .lam s body    => .lam s (LamTerm.instantiateAt (.succ idx) arg body)
| .app s fn arg' => .app s (LamTerm.instantiateAt idx arg fn) (LamTerm.instantiateAt idx arg arg')

def LamWF.instantiateAt
  (ltv : LamTyVal) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, arg.bvarLifts idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAt argTy idx lctx, body, bodyTy⟩) →
  LamWF ltv ⟨lctx, LamTerm.instantiateAt idx arg body, bodyTy⟩
| lctx, _,     .ofAtom n => .ofAtom _
| lctx, _,     .ofBase (b:=b) H => .ofBase H
| lctx, wfArg, .ofBVar n => by
  dsimp [LamTerm.instantiateAt, pushLCtxAt, restoreAt, pushLCtx]
  match Nat.ble idx n with
  | true =>
    dsimp;
    match (n - idx) with
    | 0 => exact wfArg
    | _ + 1 => exact .ofBVar _
  | false => exact .ofBVar n
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLiftIdx (s:=argTy') (lctx:=lctx) 0 _ wfArg
  let IHArg := LamWF.instantiateAt ltv (Nat.succ idx) _
    (by
      rw [pushLCtxAt.zero] at wfArg'
      dsimp [LamTerm.bvarLifts] at wfArg'
      rw [← LamTerm.bvarLiftsIdx.succ_r] at wfArg'
      exact wfArg')
    (by
      rw [pushLCtx_pushLCtxAt] at H
      exact H)
  .ofLam _ IHArg
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.instantiateAt ltv idx _ wfArg HFn
  let IHArg := LamWF.instantiateAt ltv idx _ wfArg HArg
  .ofApp argTy' IHFn IHArg

theorem LamWF.instantiateAt.correct.{u}
  (lval : LamValuation.{u}) (idx : Nat)
  {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort} :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts idx arg, argTy⟩) →
  (wfBody : LamWF lval.toLamTyVal ⟨pushLCtxAt argTy idx lctxTy, body, bodyTy⟩) →
  let wfInstantiateAt' := LamWF.instantiateAt lval.toLamTyVal idx lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtxAt argTy idx lctxTy)
    (pushLCtxAtDep (LamWF.interp lval lctxTy lctxTerm wfArg) idx lctxTerm) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfInstantiateAt')
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBase b => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n => by
  dsimp [LamWF.interp, LamWF.instantiateAt, LamTerm.instantiateAt]
  dsimp [pushLCtxAt, pushLCtxAtDep, restoreAt, restoreAtDep, pushLCtx]
  match Nat.ble idx n with
  | true =>
    dsimp;
    match (n - idx) with
    | 0 => rfl
    | _ + 1 => rfl
  | false => rfl
| lctxTy, lctxTerm, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  funext (fun x => by
    let wfArg' := LamWF.ofBVarLiftIdx (s:=argTy') (lctx:=lctxTy) 0 _ wfArg
    rw [pushLCtxAt.zero] at wfArg'
    dsimp [LamTerm.bvarLifts] at wfArg'
    rw [← LamTerm.bvarLiftsIdx.succ_r] at wfArg'
    rw [pushLCtx_pushLCtxAt] at H
    let IH := LamWF.instantiateAt.correct lval (.succ idx) (pushLCtx argTy' lctxTy) (pushLCtxDep x lctxTerm) wfArg' H
    apply Eq.trans ?eqLarge (Eq.trans IH ?eqSmall)
    case eqLarge =>
      dsimp [interp]; apply eq_of_heq; apply interp.heq <;> try rfl
      case h.HLCtxTyEq => apply pushLCtx_pushLCtxAt
      case h.HLCtxTermEq =>
        apply HEq.trans (pushLCtxDep_pushLCtxAtDep _ _ _ _)
        apply heq_of_eq
        apply congrArg (f := fun x => pushLCtxAtDep x _ _)
        rw [LamWF.ofBVarLiftIdx.correct (idx:=0) lval _ lctxTerm x _ wfArg]
        apply eq_of_heq; apply interp.heq
        case h.h.HLCtxTyEq => rw [pushLCtxAt.zero]
        case h.h.HLCtxTermEq => apply pushLCtxAtDep.zero
        case h.h.HTeq => rw [← LamTerm.bvarLiftsIdx.succ_r]
    case eqSmall =>
      dsimp [interp]; apply eq_of_heq; apply interp.heq <;> rfl)
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.instantiateAt.correct lval idx lctxTy lctxTerm wfArg HFn
  let IHArg := LamWF.instantiateAt.correct lval idx lctxTy lctxTerm wfArg HArg
  by dsimp [LamWF.interp]; dsimp at IHFn; dsimp at IHArg; simp [IHFn, IHArg]

def LamTerm.instantiate1 := LamTerm.instantiateAt 0

def LamWF.instantiate1
  (ltv : LamTyVal) {arg : LamTerm} {argTy : LamSort}
  {body : LamTerm} {bodyTy : LamSort} :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, arg, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtx argTy lctx, body, bodyTy⟩) →
  LamWF ltv ⟨lctx, LamTerm.instantiate1 arg body, bodyTy⟩ :=
  Eq.mp (by
    dsimp [LamTerm.bvarLifts]
    rw [pushLCtxAt.zero, LamTerm.bvarLiftsIdx.zero]
    rfl) (@LamWF.instantiateAt ltv 0 arg argTy body bodyTy)

def LamThmWF.instantiate1
  (wfArg : LamThmWF lval lctx argTy arg) (wfBody : LamThmWF lval (argTy :: lctx) bodyTy body) :
  LamThmWF lval lctx bodyTy (LamTerm.instantiate1 arg body) := by
  intro lctx'; have hArg := wfArg lctx'; have hBody := wfBody lctx'
  rw [pushLCtxs.cons] at hBody; apply LamWF.instantiate1 _ _ hArg hBody

theorem LamWF.instantiate1.correct.{u}
  (lval : LamValuation.{u}) {arg : LamTerm} {argTy : LamSort} {body : LamTerm} {bodyTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, arg, argTy⟩)
  (wfBody : LamWF lval.toLamTyVal ⟨pushLCtx argTy lctxTy, body, bodyTy⟩) :
  let wfInstantiate1' := LamWF.instantiate1 lval.toLamTyVal lctxTy wfArg wfBody
  (LamWF.interp lval (pushLCtx argTy lctxTy)
    (pushLCtxDep (LamWF.interp lval lctxTy lctxTerm wfArg) lctxTerm) wfBody
  = LamWF.interp lval lctxTy lctxTerm wfInstantiate1') := by
  apply Eq.trans ?eqLarge (Eq.trans (@LamWF.instantiateAt.correct lval 0
    arg argTy body bodyTy lctxTy lctxTerm (Eq.mp ?eqArg wfArg) (Eq.mp ?eqBody wfBody)) ?eqSmall)
  case eqArg => dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx.zero]
  case eqBody => rw [pushLCtxAt.zero]
  case eqLarge =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => rw [pushLCtxAt.zero]
    case h.HLCtxTermEq =>
      apply HEq.trans (HEq.symm (pushLCtxAtDep.zero _ _)) _
      apply HEq.funext; intro x;
      apply pushLCtxAtDep.heq <;> try rfl
      apply LamWF.interp.heq <;> try rfl
      dsimp [LamTerm.bvarLifts]; rw [LamTerm.bvarLiftsIdx.zero]
  case eqSmall =>
    apply eq_of_heq; apply LamWF.interp.heq <;> rfl

theorem LamThmValid.instantiate1
  (hw : LamThmWF lval lctx argTy arg) (hv : LamThmValid lval (argTy :: lctx) body) :
  LamThmValid lval lctx (LamTerm.instantiate1 arg body) := by
  intro lctx'; have hArg := hw lctx'; have hBody := hv lctx'
  rw [pushLCtxs.cons] at hBody; have ⟨wfBody, vBody⟩ := hBody
  exists (LamWF.instantiate1 _ _ hArg wfBody); intro lctxTerm;
  rw [← LamWF.instantiate1.correct]; apply vBody

def LamTerm.topBetaAux (s : LamSort) (arg : LamTerm) : (fn : LamTerm) → LamTerm
| .lam _ body => LamTerm.instantiateAt 0 arg body
| t           => .app s t arg

def LamWF.topBetaAux (ltv : LamTyVal)
  {arg : LamTerm} {argTy : LamSort} {fn : LamTerm} {resTy : LamSort}
  (lctx : Nat → LamSort) (wfArg : LamWF ltv ⟨lctx, arg, argTy⟩) 
  (wfFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩) :
  LamWF ltv ⟨lctx, LamTerm.topBetaAux argTy arg fn, resTy⟩ :=
  match fn with
  | .atom _  => .ofApp _ wfFn wfArg
  | .base _  => .ofApp _ wfFn wfArg
  | .bvar _  => .ofApp _ wfFn wfArg
  | .lam _ body =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=argTy') (body:=body') bodyTy' wfBody =>
      LamWF.instantiate1 ltv lctx (argTy:=argTy') wfArg wfBody
  | .app _ _ _ => .ofApp _ wfFn wfArg

def LamWF.topBetaAux.correct.{u} (lval : LamValuation.{u})
  {arg : LamTerm} {argTy : LamSort} {fn : LamTerm} {resTy : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfArg : LamWF lval.toLamTyVal ⟨lctxTy, arg, argTy⟩)
  (wfFn : LamWF lval.toLamTyVal ⟨lctxTy, fn, .func argTy resTy⟩) :
  let wfHB := LamWF.topBetaAux _ lctxTy wfArg wfFn
  (LamWF.interp lval lctxTy lctxTerm (.ofApp _ wfFn wfArg)
  = LamWF.interp lval lctxTy lctxTerm wfHB) :=
  match fn with
  | .atom _  => rfl
  | .base _  => rfl
  | .bvar _  => rfl
  | .lam _ _ =>
    match argTy, wfFn with
    | _, .ofLam (argTy:=_) (body:=_) _ _ => LamWF.instantiate1.correct _ _ _ _ _
  | .app _ _ _ => rfl

def LamTerm.topBeta : LamTerm → LamTerm
| .app s fn arg => LamTerm.topBetaAux s arg fn
| t => t

def LamWF.topBeta
  (ltv : LamTyVal) {t : LamTerm} {ty : LamSort} (lctx : Nat → LamSort)
  (wf : LamWF ltv ⟨lctx, t, ty⟩) : LamWF ltv ⟨lctx, LamTerm.topBeta t, ty⟩ :=
  match t with
  | .atom _ => wf
  | .base _ => wf
  | .bvar _ => wf
  | .lam .. => wf
  | .app .. =>
    match wf with
    | .ofApp _ wfFn wfArg => LamWF.topBetaAux _ lctx wfArg wfFn

def LamThmWF.topBeta
  (wf : LamThmWF lval lctx rty t) : LamThmWF lval lctx rty t.topBeta := by
  intro lctx; apply LamWF.topBeta _ _ (wf lctx)

theorem LamWF.topBeta.correct
  {lval : LamValuation.{u}} {t : LamTerm} {ty : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfT : LamWF lval.toLamTyVal ⟨lctxTy, t, ty⟩) :
  let wfHB := LamWF.topBeta lval.toLamTyVal lctxTy wfT
  LamWF.interp lval lctxTy lctxTerm wfT = LamWF.interp lval lctxTy lctxTerm wfHB :=
  match t with
  | .atom _ => rfl
  | .base _ => rfl
  | .bvar _ => rfl
  | .lam .. => rfl
  | .app .. =>
    match wfT with
    | .ofApp _ wfFn wfArg => LamWF.topBetaAux.correct _ lctxTy lctxTerm wfArg wfFn

theorem LamThmValid.topBeta (H : LamThmValid lval lctx t) :
  LamThmValid lval lctx t.topBeta := by
  intros lctx; let ⟨wf, h⟩ := H lctx; exists (LamWF.topBeta _ _ wf);
  intro lctxTerm; rw [← LamWF.topBeta.correct]; apply h

def LamBaseTerm.resolveImport (ltv : LamTyVal) : LamBaseTerm → LamBaseTerm
| .eqI n      => .eq (ltv.lamILTy n)
| .forallEI n => .forallE (ltv.lamILTy n)
| .existEI n  => .existE (ltv.lamILTy n)
| t           => t

def LamBaseTerm.LamWF.resolveImport {ltv : LamTyVal} {b : LamBaseTerm} {ty : LamSort}
  (wfB : LamBaseTerm.LamWF ltv b ty) : LamBaseTerm.LamWF ltv (b.resolveImport ltv) ty := by
  cases wfB <;> constructor

theorem LamBaseTerm.LamWF.resolveImport.correct
  (lval : LamValuation.{u}) {b : LamBaseTerm} {ty : LamSort}
  (wfB : LamBaseTerm.LamWF lval.toLamTyVal b ty) :
  let wfRB := LamBaseTerm.LamWF.resolveImport wfB
  LamBaseTerm.LamWF.interp lval wfB = LamBaseTerm.LamWF.interp lval wfRB := by
  cases wfB <;> first | rfl | dsimp [resolveImport, LamBaseTerm.resolveImport, interp]
  case ofEqI n =>
    generalize LamValuation.ilVal lval n = ilVal
    cases ilVal
    case mk eqL _ _ =>
      apply funext; intros a; apply funext; intros b;
      apply GLift.down.inj; apply propext;
      apply Iff.intro (eqL.down _ _) (eqL.up _ _)
  case ofForallEI n =>
    generalize LamValuation.ilVal lval n = ilVal
    cases ilVal
    case mk _ forallL _ =>
      apply funext; intros p;
      apply GLift.down.inj; apply propext;
      apply Iff.intro (forallL.down _) (forallL.up _)
  case ofExistEI n =>
    generalize LamValuation.ilVal lval n = ilVal
    cases ilVal
    case mk _ _ existL =>
      apply funext; intros p;
      apply GLift.down.inj; apply propext;
      apply Iff.intro (existL.down _) (existL.up _)

def LamTerm.resolveImport (ltv : LamTyVal) : LamTerm → LamTerm
| .atom n       => .atom n
| .base b       => .base (b.resolveImport ltv)
| .bvar n       => .bvar n
| .lam s t      => .lam s (t.resolveImport ltv)
| .app s fn arg => .app s (fn.resolveImport ltv) (arg.resolveImport ltv)

def LamWF.resolveImport
  {ltv : LamTyVal} {t : LamTerm} {ty : LamSort}
  {lctx : Nat → LamSort} (wfT : LamWF ltv ⟨lctx, t, ty⟩) :
  LamWF ltv ⟨lctx, LamTerm.resolveImport ltv t, ty⟩ :=
  match wfT with
  | .ofAtom n => .ofAtom n
  | .ofBase b => .ofBase (LamBaseTerm.LamWF.resolveImport b)
  | .ofBVar n => .ofBVar n
  | .ofLam s hwf => .ofLam s hwf.resolveImport
  | .ofApp s fn arg => .ofApp s fn.resolveImport arg.resolveImport

def LamThmWF.resolveImport
  {lval : LamValuation} {lctx : List LamSort} {rty : LamSort} {t : LamTerm}
  (wf : LamThmWF lval lctx rty t) : LamThmWF lval lctx rty (t.resolveImport lval.toLamTyVal) :=
  fun lctx => LamWF.resolveImport (wf lctx)

theorem LamWF.resolveImport.correct
  {lval : LamValuation.{u}} {t : LamTerm} {ty : LamSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (wfT : LamWF lval.toLamTyVal ⟨lctxTy, t, ty⟩) :
  let wfRB := LamWF.resolveImport wfT
  LamWF.interp lval lctxTy lctxTerm wfT = LamWF.interp lval lctxTy lctxTerm wfRB :=
  match wfT with
  | .ofAtom _ => rfl
  | .ofBase b => LamBaseTerm.LamWF.resolveImport.correct lval b
  | .ofBVar n => rfl
  | .ofLam s hwf => by
    apply funext; intros x; dsimp [interp]
    rw [LamWF.resolveImport.correct _ _ hwf]
  | .ofApp s wfFn wfArg => by
    dsimp [interp];
    rw [LamWF.resolveImport.correct _ _ wfFn]
    rw [LamWF.resolveImport.correct _ _ wfArg]

theorem LamThmValid.resolveImport (H : LamThmValid lval lctx t) :
  LamThmValid lval lctx (t.resolveImport lval.toLamTyVal) := by
  intro lctx; let ⟨wf, h⟩ := H lctx;
  exists (LamWF.resolveImport wf); intro lctxTerm
  rw [← LamWF.resolveImport.correct]; apply h

-- Semantic Equivalence
-- Note that we do not expect to reorder binders or remove
--   unused binders, because doing so makes the term not equivalent
--   to the original one
def LamEquiv (lval : LamValuation) (lctx : List LamSort) (rty : LamSort)
  (t₁ t₂ : LamTerm) :=
  ∀ (lctx' : Nat → LamSort),
    ∃ (wf₁ : LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t₁, rty⟩),
    ∃ (wf₂ : LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t₂, rty⟩),
    ∀ (lctxTerm : ∀ n, (pushLCtxs lctx lctx' n).interp lval.tyVal),
    LamWF.interp lval (pushLCtxs lctx lctx') lctxTerm wf₁ =
      LamWF.interp lval (pushLCtxs lctx lctx') lctxTerm wf₂

theorem LamEquiv.refl (lval : LamValuation) (wf : LamThmWF lval lctx s t) :
  LamEquiv lval lctx s t t := by
  dsimp [LamEquiv]; intros lctx';
  let wf' := wf lctx'
  exists wf'; exists wf'
  intros lctxTerm; rfl

theorem LamEquiv.symm (lval : LamValuation) (e : LamEquiv lval lctx rty a b) :
  LamEquiv lval lctx rty b a := by
  dsimp [LamEquiv]; intros lctx'
  let ⟨wfa, ⟨wfb, Hab⟩⟩ := e lctx'
  exists wfb, wfa; intros lctxTerm
  apply Eq.symm; apply Hab

theorem LamEquiv.trans (lval : LamValuation)
  (e₁ : LamEquiv lval lctx rty a b) (e₂ : LamEquiv lval lctx rty b c) :
  LamEquiv lval lctx rty a c := by
  dsimp [LamEquiv]; intros lctx'
  let ⟨wfa, ⟨wfb₁, Hab⟩⟩ := e₁ lctx'
  let ⟨wfb₂, ⟨wfc, Hbc⟩⟩ := e₂ lctx'
  exists wfa; exists wfc; intros lctxTerm
  apply Eq.trans (Hab lctxTerm) (Eq.trans _ (Hbc lctxTerm))
  apply eq_of_heq; apply LamWF.interp.heq <;> rfl

theorem LamEquiv.ofLam (lval : LamValuation)
  (e : LamEquiv lval (w :: lctx) s a b) :
  LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) := by
  dsimp [LamEquiv]; intros lctx'
  let ⟨wfa, ⟨wfb, Hab⟩⟩ := e lctx'
  let wfsa := LamWF.ofLam _ (pushLCtxs.cons _ _ ▸ wfa)
  let wfsb := LamWF.ofLam _ (pushLCtxs.cons _ _ ▸ wfb)
  exists wfsa; exists wfsb; intros lctxTerm
  dsimp [LamWF.interp]; apply funext; intros x
  let ieq := Hab ((pushLCtxs.cons (x:=w) lctx lctx') ▸ pushLCtxDep x lctxTerm);
  apply Eq.trans _ (Eq.trans ieq _)
  case _ =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => exact Eq.symm (pushLCtxs.cons _ _)
    case h.HLCtxTermEq => apply HEq.symm; apply eqRec_heq'
  case _ =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => exact pushLCtxs.cons _ _
    case h.HLCtxTermEq => apply eqRec_heq'

theorem LamEquiv.fromLam (lval : LamValuation)
  (e : LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b)) :
  LamEquiv lval (w :: lctx) s a b := by
  dsimp [LamEquiv]; intros lctx'
  let ⟨wfa, ⟨wfb, Hab⟩⟩ := e lctx'
  let .ofLam _ Ha := wfa
  let .ofLam _ Hb := wfb
  exists (pushLCtxs.cons _ _ ▸ Ha); exists (pushLCtxs.cons _ _ ▸ Hb);
  intros lctxTerm
  let lctxTerm' : (n : Nat) → LamSort.interp lval.tyVal (pushLCtxs lctx lctx' n) :=
    fun n => pushLCtxs.cons_succ _ _ _ ▸ lctxTerm (.succ n)
  let x : LamSort.interp lval.tyVal w := by
    let x' := lctxTerm 0
    rw [pushLCtxs.cons_zero] at x'
    exact x'
  let ieq := congrFun (Hab lctxTerm') x
  apply Eq.trans _ (Eq.trans ieq _)
  case _ =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => exact pushLCtxs.cons _ _
    case h.HLCtxTermEq =>
      apply HEq.funext; intros n; cases n
      case zero => rw [pushLCtxDep.zero]; apply HEq.symm; apply eqRec_heq'
      case succ n => rw [pushLCtxDep.succ]; apply HEq.symm; apply eqRec_heq'
  case _ =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => apply Eq.symm; exact pushLCtxs.cons _ _
    case h.HLCtxTermEq =>
      apply HEq.funext; intros n; cases n
      case zero => rw [pushLCtxDep.zero]; apply eqRec_heq'
      case succ n => rw [pushLCtxDep.succ]; apply eqRec_heq'

theorem LamEquiv.eqLam (lval : LamValuation) :
  LamEquiv lval (w :: lctx) s a b = LamEquiv lval lctx (.func w s) (.lam w a) (.lam w b) :=
  propext (Iff.intro (LamEquiv.ofLam _) (LamEquiv.fromLam _))

theorem LamEquiv.congr (lval : LamValuation)
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg₁) (.app argTy fn₂ arg₂) := by
  dsimp [LamEquiv]; intros lctx'
  let ⟨wfFn₁, ⟨wfFn₂, HFn⟩⟩ := eFn lctx'
  let ⟨wfArg₁, ⟨wfArg₂, HArg⟩⟩ := eArg lctx'
  exists (.ofApp _ wfFn₁ wfArg₁); exists (.ofApp _ wfFn₂ wfArg₂); intros lctxTerm
  dsimp [LamWF.interp]; apply _root_.congr
  case h₁ => rw [HFn]
  case h₂ => rw [HArg]

theorem LamEquiv.congrFn (lval : LamValuation)
  (eFn : LamEquiv lval lctx (.func argTy resTy) fn₁ fn₂)
  (wfArg : LamThmWF lval lctx argTy arg) :
  LamEquiv lval lctx resTy (.app argTy fn₁ arg) (.app argTy fn₂ arg) :=
  LamEquiv.congr lval eFn (LamEquiv.refl lval wfArg)

theorem LamEquiv.congrArg (lval : LamValuation)
  (wfFn : LamThmWF lval lctx (.func argTy resTy) fn)
  (eArg : LamEquiv lval lctx argTy arg₁ arg₂) :
  LamEquiv lval lctx resTy (.app argTy fn arg₁) (.app argTy fn arg₂) :=
  LamEquiv.congr lval (LamEquiv.refl lval wfFn) eArg

theorem LamEquiv.ofTopBeta (wf : LamThmWF lval lctx s t) :
  LamEquiv lval lctx s t t.topBeta := by
  dsimp [LamEquiv]; intros lctx'; let wf' := wf lctx'
  exists wf'; exists LamWF.topBeta _ _ wf'
  intros lctxTerm; apply LamWF.topBeta.correct

theorem LamEquiv.ofResolveImport
  (lval : LamValuation) (wfT : LamThmWF lval lctx s t) :
  LamEquiv lval lctx s t (t.resolveImport lval.toLamTyVal) := by
  dsimp [LamEquiv]; intros lctx';
  let wfT' := wfT lctx'; exists wfT'; exists (LamWF.resolveImport wfT')
  intros lctxTerm; apply LamWF.resolveImport.correct

theorem LamThmValid.ofLamEquiv
  (lval : LamValuation) (lctx : List LamSort)
  (eT : LamEquiv lval lctx s t₁ t₂) :
  LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) := by
  dsimp [LamThmValid]; intros lctx'
  let ⟨wfT₁, ⟨wfT₂, heq⟩⟩ := eT lctx';
  exact Exists.intro (LamWF.mkEq wfT₁ wfT₂) heq

theorem LamEquiv.ofLamThmValid
  (lval : LamValuation) (lctx : List LamSort)
  (heq : LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂)) :
  LamEquiv lval lctx s t₁ t₂ := by
  dsimp [LamEquiv]; intros lctx'
  let ⟨.ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂, heq'⟩ := heq lctx'
  exact Exists.intro wft₁ (.intro wft₂ heq')

theorem LamEquiv.eqLamThmValid
  (lval : LamValuation) (lctx : List LamSort) :
  LamEquiv lval lctx s t₁ t₂ = LamThmValid lval lctx (LamTerm.mkEq s t₁ t₂) :=
  propext (Iff.intro (LamThmValid.ofLamEquiv _ _) (LamEquiv.ofLamThmValid _ _))

theorem LamThmValid.mpLamEquiv
  (lval : LamValuation) (lctx : List LamSort)
  (hequiv : LamEquiv lval lctx (.base .prop) p₁ p₂)
  (hp : LamThmValid lval lctx p₁) : LamThmValid lval lctx p₂ := by
  intros lctx';
  let ⟨wfp₁, ⟨wfp₂, heqp⟩⟩ := hequiv lctx'
  exists wfp₂; intro lctxTerm'; rw [← heqp]
  let ⟨wfp₁', hp₁⟩ := hp lctx'
  have wfeq : wfp₁ = wfp₁' := eq_of_heq (LamWF.unique wfp₁ wfp₁').right
  cases wfeq; apply hp₁

theorem Eq.symm (lval : LamValuation) (lctx : List LamSort)
  (H : LamThmValid lval lctx (.mkEq s a b)) :
  LamThmValid lval lctx (.mkEq s b a) := by
  apply LamThmValid.ofLamEquiv
  apply LamEquiv.symm;
  apply LamEquiv.ofLamThmValid _ _ H

theorem Eq.trans (lval : LamValuation) (lctx : List LamSort)
  (H₁ : LamThmValid lval lctx (.mkEq s a b))
  (H₂ : LamThmValid lval lctx (.mkEq s b c)) :
  LamThmValid lval lctx (.mkEq s a c) := by
  apply LamThmValid.ofLamEquiv
  apply LamEquiv.trans (b:=b)
  case e₁ => apply LamEquiv.ofLamThmValid _ _ H₁
  case e₂ => apply LamEquiv.ofLamThmValid _ _ H₂

theorem Eq.subst (lval : LamValuation) (lctx : List LamSort)
  (hEq : LamThmValid lval lctx (.mkEq s a b))
  (hPa : LamThmValid lval lctx (.app s p a)) :
  LamThmValid lval lctx (.app s p b) := by
  apply LamThmValid.mpLamEquiv _ _ _ hPa
  apply LamEquiv.congrArg
  case wfFn =>
    intros lctx'
    let .ofApp _ Hp _ := LamThmWF.ofLamThmValid hPa lctx'
    exact Hp
  case eArg =>
    apply LamEquiv.ofLamThmValid _ _ hEq

theorem Eq.congr (lval : LamValuation) (lctx : List LamSort)
  (hEq : LamThmValid lval lctx (.mkEq s' a b))
  (wfT : LamThmWF lval lctx s (.app s' f a))
  : LamThmValid lval lctx (.mkEq s (.app s' f a) (.app s' f b)) := by
  apply LamThmValid.ofLamEquiv
  apply LamEquiv.congrArg
  case wfFn =>
    intros lctx'
    let .ofApp _ Hf _ := wfT lctx'
    exact Hf
  case eArg => exact LamEquiv.ofLamThmValid _ _ hEq

def LamTerm.impApp? (t₁₂ t₁ : LamTerm) : Option LamTerm :=
  match t₁₂ with
  | .app _ fn concl =>
    match fn with
    | .app _ imp hyp =>
      match hyp.beq t₁ with
      | true =>
        match imp with
        | .base b =>
          match b with
          | .imp => .some concl
          | _ => .none
        | _ => .none
      | false => .none
    | _ => .none
  | _ => .none

theorem LamValid.impApp
  (v₁₂ : LamValid lval lctx t₁₂) (v₁ : LamValid lval lctx t₁)
  (heq : LamTerm.impApp? t₁₂ t₁ = .some t₂) : LamValid lval lctx t₂ := by
  dsimp [LamTerm.impApp?] at heq
  cases t₁₂ <;> try cases heq
  case app bp₁ hypimp concl =>
    cases hypimp <;> try cases heq
    case app bp₂ imp hyp =>
      dsimp at heq
      match h : LamTerm.beq hyp t₁ with
      | true =>
        rw [h] at heq
        cases imp <;> try cases heq
        case base b =>
          cases b <;> cases heq
          case imp =>
            have ⟨wf₁₂, h₁₂⟩ := v₁₂
            match wf₁₂ with
            | .ofApp _ (.ofApp _ (.ofBase .ofImp) HArg) wfConcl =>
              exists wfConcl; have ⟨wf₁, h₁⟩ := v₁;
              intro lctxTerm; apply h₁₂; apply Eq.mp _ (h₁ lctxTerm);
              apply congrArg; apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
              exact .symm (LamTerm.beq_eq _ _ h)
      | false =>
        rw [h] at heq; cases heq

theorem LamThmValid.impApp
  (H₁₂ : LamThmValid lval lctx t₁₂) (H₁ : LamThmValid lval lctx t₁)
  (heq : LamTerm.impApp? t₁₂ t₁ = .some res) : LamThmValid lval lctx res :=
  fun lctx' => LamValid.impApp (H₁₂ lctx') (H₁ lctx') heq

end Auto.Embedding.Lam