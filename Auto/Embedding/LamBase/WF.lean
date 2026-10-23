module

public import Auto.Embedding.LamBase.Term

@[expose] public section

/-! Type checking `LamTerm.lamCheck?` and typing derivations `LamWF` -/

namespace Auto.Embedding.Lam

-- Typecheck. `ltv, lctx ⊢ term : type?`
-- `ltv`          : LamTyVal
-- `Nat → LamSort` : Local Context
def LamTerm.lamCheck? (ltv : LamTyVal) :
  (Nat → LamSort) → LamTerm → Option LamSort
| _,    .atom n  => ltv.lamVarTy n
| _,    .etom n  => ltv.lamEVarTy n
| _,    .base b  => b.lamCheck ltv
| lctx, .bvar n  => lctx n
| lctx, .lam s t =>
  match t.lamCheck? ltv (pushLCtx s lctx) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app s fn arg =>
  match fn.lamCheck? ltv lctx, arg.lamCheck? ltv lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    match ty₁.beq argTy, ty₁.beq s with
    | true, true => .some ty₂
    | _,    _    => none
  | _, _ => .none

theorem LamTerm.lamCheck?_irrelevence
  {ltv : LamTyVal} {lctx₁ lctx₂ : Nat → LamSort} {t : LamTerm}
  (hirr : ∀ n, n < t.maxLooseBVarSucc → lctx₁ n = lctx₂ n) :
  LamTerm.lamCheck? ltv lctx₁ t = LamTerm.lamCheck? ltv lctx₂ t := by
  induction t generalizing lctx₁ lctx₂ <;> dsimp [LamTerm.lamCheck?]
  case bvar n =>
    apply congrArg; apply hirr; exact .refl
  case lam s t IHt =>
    rw [IHt]; intros n hlt; cases n
    case zero => rfl
    case succ n =>
      dsimp [pushLCtx]; rw [hirr]; dsimp [maxLooseBVarSucc]
      apply Nat.le_pred_of_succ_le _ hlt;
      apply Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hlt
  case app s fn arg IHFn IHArg =>
    rw [IHFn]; rw [IHArg];
    intros n hlt; rw [hirr n (Nat.le_trans hlt (Nat.le_max_right _ _))]
    intros n hlt; rw [hirr n (Nat.le_trans hlt (Nat.le_max_left _ _))]

/--
  Judgement. `lamVarTy, lctx ⊢ term : type?`
  We put `rterm` before `rty` to avoid dependent elimination failure
-/
structure LamJudge where
  lctx   : Nat → LamSort
  rterm  : LamTerm
  rty    : LamSort
deriving Inhabited

inductive LamWF (ltv : LamTyVal) : LamJudge → Type
  | ofAtom
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF ltv ⟨lctx, .atom n, ltv.lamVarTy n⟩
  | ofEtom
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF ltv ⟨lctx, .etom n, ltv.lamEVarTy n⟩
  | ofBase
      {lctx : Nat → LamSort} {b : LamBaseTerm} {s : LamSort}
      (H : LamBaseTerm.LamWF ltv b s) :
    LamWF ltv ⟨lctx, .base b, s⟩
  | ofBVar
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF ltv ⟨lctx, .bvar n, lctx n⟩
  | ofLam
      {lctx : Nat → LamSort}
      {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
      (H : LamWF ltv ⟨pushLCtx argTy lctx, body, bodyTy⟩) :
    LamWF ltv ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
  | ofApp
      {lctx : Nat → LamSort}
      (argTy : LamSort) {resTy : LamSort}
      {fn : LamTerm} {arg : LamTerm}
      (HFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩)
      (HArg : LamWF ltv ⟨lctx, arg, argTy⟩) :
    LamWF ltv ⟨lctx, .app argTy fn arg, resTy⟩

theorem LamWF.unique {ltv : LamTyVal} :
  (lwf₁ : LamWF ltv ⟨lctx, t, s₁⟩) → (lwf₂ : LamWF ltv ⟨lctx, t, s₂⟩) →
  s₁ = s₂ ∧ HEq lwf₁ lwf₂
| .ofAtom _,  .ofAtom _  => And.intro rfl HEq.rfl
| .ofEtom _,  .ofEtom _  => And.intro rfl HEq.rfl
| .ofBase H₁, .ofBase H₂ =>
  have ⟨.refl _, .refl _⟩ := LamBaseTerm.LamWF.unique H₁ H₂
  And.intro rfl HEq.rfl
| .ofBVar _,  .ofBVar _  => And.intro rfl HEq.rfl
| .ofLam _ H₁, .ofLam _ H₂ =>
  have ⟨.refl _, .refl _⟩ := LamWF.unique H₁ H₂
  And.intro rfl HEq.rfl
| .ofApp _ HFn₁ HArg₁, .ofApp _ HFn₂ HArg₂ =>
  have ⟨.refl _, .refl _⟩ := LamWF.unique HFn₁ HFn₂
  have ⟨.refl _, .refl _⟩ := LamWF.unique HArg₁ HArg₂
  And.intro rfl HEq.rfl

def LamWF.lctxIrrelevance
  (hirr : ∀ n, n < t.maxLooseBVarSucc → lctx₁ n = lctx₂ n) :
  (lwf : LamWF ltv ⟨lctx₁, t, s⟩) → LamWF ltv ⟨lctx₂, t, s⟩
| .ofAtom _ => .ofAtom _
| .ofEtom _ => .ofEtom _
| .ofBase H => .ofBase H
| .ofBVar _ => hirr _ (Nat.le_refl _) ▸ .ofBVar _
| .ofLam bodyTy H => by
  apply LamWF.ofLam bodyTy (lctxIrrelevance _ H); intros n hlt
  cases n <;> try rfl
  case succ n =>
    apply hirr;
    apply Nat.le_pred_of_succ_le _ hlt
    apply Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hlt
| .ofApp argTy HFn HArg => .ofApp argTy
  (lctxIrrelevance (fun n H => hirr _ (Nat.le_trans H (Nat.le_max_left _ _))) HFn)
  (lctxIrrelevance (fun n H => hirr _ (Nat.le_trans H (Nat.le_max_right _ _))) HArg)

def LamWF.insertEVarAt_eIdx {ltv : LamTyVal} :
  LamWF {ltv with lamEVarTy := replaceAt s eIdx lamEVarTy'} ⟨lctx, .etom eIdx, s⟩ := by
  have : s = replaceAt s eIdx lamEVarTy' eIdx := by
    dsimp [replaceAt]; rw [Nat.beq_refl]
  conv =>
    arg 2; arg 3; rw [this]
  exact LamWF.ofEtom _

def LamWF.eVarIrrelevance
  (hLamVarTy : ltv₁.lamVarTy = ltv₂.lamVarTy)
  (hLamILTy : ltv₁.lamILTy = ltv₂.lamILTy)
  (hirr : ∀ n, n < t.maxEVarSucc → ltv₁.lamEVarTy n = ltv₂.lamEVarTy n) :
  (lwf : LamWF ltv₁ ⟨lctx, t, s⟩) → LamWF ltv₂ ⟨lctx, t, s⟩
| .ofAtom _ => hLamVarTy ▸ .ofAtom _
| .ofEtom _ => hirr _ (Nat.le_refl _) ▸ .ofEtom _
| .ofBase H => .ofBase (LamBaseTerm.LamWF.eVarIrrelevance hLamVarTy hLamILTy H)
| .ofBVar _ => .ofBVar _
| .ofLam bodyTy H => .ofLam bodyTy (eVarIrrelevance hLamVarTy hLamILTy hirr H)
| .ofApp argTy HFn HArg => .ofApp argTy
  (eVarIrrelevance hLamVarTy hLamILTy (fun _ H => hirr _ (Nat.le_trans H (Nat.le_max_left _ _))) HFn)
  (eVarIrrelevance hLamVarTy hLamILTy (fun _ H => hirr _ (Nat.le_trans H (Nat.le_max_right _ _))) HArg)

theorem LamWF.getAtom {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .atom n, s⟩) : ltv.lamVarTy n = s :=
  match wft with
  | .ofAtom _ => rfl

theorem LamWF.getEtom {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .etom n, s⟩) : ltv.lamEVarTy n = s :=
  match wft with
  | .ofEtom _ => rfl

def LamWF.getBase {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .base b, s⟩) : LamBaseTerm.LamWF ltv b s :=
  match wft with
  | .ofBase H => H

theorem LamWF.getBVar {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .bvar n, s⟩) : lctx n = s :=
  match wft with
  | .ofBVar _ => rfl

def LamWF.getLam {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .lam s body, .func s argTy⟩) : LamWF ltv ⟨pushLCtx s lctx, body, argTy⟩ :=
  match wft with
  | .ofLam _ HBody => HBody

def LamWF.getFn {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .app argTy fn arg, resTy⟩) : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩ :=
  match wft with
  | .ofApp _ HFn _ => HFn

def LamWF.getArg {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .app argTy fn arg, resTy⟩) : LamWF ltv ⟨lctx, arg, argTy⟩ :=
  match wft with
  | .ofApp _ _ HArg => HArg

def LamWF.flip :
  LamWF ltv ⟨lctx, LamTerm.flip argTy₁ argTy₂ resTy,
    .func (.func argTy₁ (.func argTy₂ resTy)) (.func argTy₂ (.func argTy₁ resTy))⟩ :=
  .ofLam _ (.ofLam _ (.ofLam _ (.ofApp _ (.ofApp _ (.ofBVar 2) (.ofBVar 0)) (.ofBVar 1))))

def LamWF.flipApp
  (wft : LamWF ltv ⟨lctx, t, .func argTy₁ (.func argTy₂ resTy)⟩) :
  LamWF ltv ⟨lctx, LamTerm.flipApp t argTy₁ argTy₂ resTy, .func argTy₂ (.func argTy₁ resTy)⟩ :=
  .ofApp _ .flip wft

def LamWF.ofNmodeq : LamWF ltv ⟨lctx, LamTerm.nmodeq, .func (.base .nat) (.func (.base .nat) (.func (.base .nat) (.base .prop)))⟩ :=
  .ofLam _ (.ofLam _ (.ofLam _ (.ofApp _ (.ofApp _ (.ofBase (.ofEq _))
    (.ofApp _ (.ofApp _ (.ofBase .ofNmod) (.ofBVar 1)) (.ofBVar 2)))
    (.ofApp _ (.ofApp _ (.ofBase .ofNmod) (.ofBVar 0)) (.ofBVar 2)))))

def LamWF.ofNge : LamWF ltv ⟨lctx, LamTerm.nge, .func (.base .nat) (.func (.base .nat) (.base .prop))⟩ :=
  .flipApp (.ofBase .ofNle)

def LamWF.ofNgt : LamWF ltv ⟨lctx, LamTerm.ngt, .func (.base .nat) (.func (.base .nat) (.base .prop))⟩ :=
  .flipApp (.ofBase .ofNlt)

def LamWF.ofImodeq : LamWF ltv ⟨lctx, LamTerm.imodeq, .func (.base .int) (.func (.base .int) (.func (.base .int) (.base .prop)))⟩ :=
  .ofLam _ (.ofLam _ (.ofLam _ (.ofApp _ (.ofApp _ (.ofBase (.ofEq _))
    (.ofApp _ (.ofApp _ (.ofBase .ofIemod) (.ofBVar 1)) (.ofBVar 2)))
    (.ofApp _ (.ofApp _ (.ofBase .ofIemod) (.ofBVar 0)) (.ofBVar 2)))))

def LamWF.ofIge : LamWF ltv ⟨lctx, LamTerm.ige, .func (.base .int) (.func (.base .int) (.base .prop))⟩ :=
  .flipApp (.ofBase .ofIle)

def LamWF.ofIgt : LamWF ltv ⟨lctx, LamTerm.igt, .func (.base .int) (.func (.base .int) (.base .prop))⟩ :=
  .flipApp (.ofBase .ofIlt)

def LamWF.ofSge : LamWF ltv ⟨lctx, LamTerm.sge, .func (.base .string) (.func (.base .string) (.base .prop))⟩ :=
  .flipApp (.ofBase .ofSle)

def LamWF.ofSgt : LamWF ltv ⟨lctx, LamTerm.sgt, .func (.base .string) (.func (.base .string) (.base .prop))⟩ :=
  .flipApp (.ofBase .ofSlt)

def LamWF.ofBvuge (n : Nat) : LamWF ltv ⟨lctx, LamTerm.bvuge n, .func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool))⟩ :=
  .flipApp (.ofBase (.ofBvule n))

def LamWF.ofBvugt (n : Nat) : LamWF ltv ⟨lctx, LamTerm.bvugt n, .func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool))⟩ :=
  .flipApp (.ofBase (.ofBvult n))

def LamWF.ofBvsge (n : Nat) : LamWF ltv ⟨lctx, LamTerm.bvsge n, .func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool))⟩ :=
  .flipApp (.ofBase (.ofBvsle n))

def LamWF.ofBvsgt (n : Nat) : LamWF ltv ⟨lctx, LamTerm.bvsgt n, .func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool))⟩ :=
  .flipApp (.ofBase (.ofBvslt n))

def LamWF.bvsmtHshl (n m : Nat) : LamWF ltv ⟨lctx, LamTerm.bvsmtHshl n m, .func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv n)))⟩ :=
  .ofLam _ (.ofLam _ (.ofApp _ (.ofApp _ (.ofBase (.ofBvshl _)) (.ofBVar 1)) (.ofApp _ (.ofBase (.ofBvtoNat _)) (.ofBVar 0))))

def LamWF.bvsmtHlshr (n m : Nat) : LamWF ltv ⟨lctx, LamTerm.bvsmtHlshr n m, .func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv n)))⟩ :=
  .ofLam _ (.ofLam _ (.ofApp _ (.ofApp _ (.ofBase (.ofBvlshr _)) (.ofBVar 1)) (.ofApp _ (.ofBase (.ofBvtoNat _)) (.ofBVar 0))))

def LamWF.bvsmtHashr (n m : Nat) : LamWF ltv ⟨lctx, LamTerm.bvsmtHashr n m, .func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv n)))⟩ :=
  .ofLam _ (.ofLam _ (.ofApp _ (.ofApp _ (.ofBase (.ofBvashr _)) (.ofBVar 1)) (.ofApp _ (.ofBase (.ofBvtoNat _)) (.ofBVar 0))))

def LamWF.mkNot {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, t, .base .prop⟩) : LamWF ltv ⟨lctx, .mkNot t, .base .prop⟩ :=
  LamWF.ofApp _ (.ofBase .ofNot) wft

def LamWF.mkAnd {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, .base .prop⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkAnd t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase .ofAnd) wft₁) wft₂

def LamWF.mkOr {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, .base .prop⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkOr t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase .ofOr) wft₁) wft₂

def LamWF.mkImp {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, .base .prop⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkImp t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase .ofImp) wft₁) wft₂

def LamWF.mkIff {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, .base .prop⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkIff t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase .ofIff) wft₁) wft₂

def LamWF.mkEq {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, s⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, s⟩) :
  LamWF ltv ⟨lctx, .mkEq s t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂

theorem LamWF.mkEq_sortEq (hwf : LamWF ltv ⟨lctx, .app s' (.app s'' (.base (.eq s)) t₁) t₂, rty⟩) :
  s' = s ∧ s'' = s ∧ rty = .base .prop :=
  match hwf with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) _) _ => And.intro rfl (And.intro rfl rfl)

def LamWF.mkForallE {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .func s (.base .prop)⟩) :
  LamWF ltv ⟨lctx, .mkForallE s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofForallE _)) wfp

def LamWF.mkForallEF {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtx s lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkForallEF s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ wfp)

def LamWF.fromMkForallEF {ltv : LamTyVal}
  (wf : LamWF ltv ⟨lctx, .mkForallEF s p, .base .prop⟩) :
  LamWF ltv ⟨pushLCtx s lctx, p, .base .prop⟩ := wf.getArg.getLam

def LamWF.mkExistE {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .func s (.base .prop)⟩) :
  LamWF ltv ⟨lctx, .mkExistE s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofExistE _)) wfp

def LamWF.mkExistEF {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtx s lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkExistEF s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofExistE _)) (.ofLam _ wfp)

def LamWF.fromMkExistEF {ltv : LamTyVal}
  (wf : LamWF ltv ⟨lctx, .mkExistEF s p, .base .prop⟩) :
  LamWF ltv ⟨pushLCtx s lctx, p, .base .prop⟩ := wf.getArg.getLam

def LamWF.mkIte {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .base .prop⟩)
  (wfx : LamWF ltv ⟨lctx, x, s⟩) (wfy : LamWF ltv ⟨lctx, y, s⟩) :
  LamWF ltv ⟨lctx, .mkIte s p x y, s⟩ := LamWF.ofApp _ (.ofApp _ (.ofApp _ (.ofBase (.ofIte _)) wfp) wfx) wfy

def LamWF.mkNatVal {ltv : LamTyVal} : LamWF ltv ⟨lctx, .mkNatVal n, .base .nat⟩ := .ofBase (.ofNatVal n)

def LamWF.mkNatBinOp {ltv : LamTyVal}
  (wfop : NatConst.LamWF binOp (.func (.base .nat) (.func (.base .nat) s)))
  (wfa : LamWF ltv ⟨lctx, a, .base .nat⟩) (wfb : LamWF ltv ⟨lctx, b, .base .nat⟩) :
  LamWF ltv ⟨lctx, .mkNatBinOp binOp a b, s⟩ :=
  .ofApp _ (.ofApp _ (.ofBase (.ofNcst wfop)) wfa) wfb

def LamWF.mkIOfNat {ltv : LamTyVal}
  (wfn : LamWF ltv ⟨lctx, n, .base .nat⟩) : LamWF ltv ⟨lctx, .mkIOfNat n, .base .int⟩ :=
  .ofApp _ (.ofBase .ofIOfNat) wfn

def LamWF.mkINegSucc {ltv : LamTyVal}
  (wfn : LamWF ltv ⟨lctx, n, .base .nat⟩) : LamWF ltv ⟨lctx, .mkINegSucc n, .base .int⟩ :=
  .ofApp _ (.ofBase .ofINegSucc) wfn

def LamWF.mkIntUOp {ltv : LamTyVal}
  (wfop : IntConst.LamWF uop (.func (.base .int) s))
  (wfa : LamWF ltv ⟨lctx, a, .base .int⟩) : LamWF ltv ⟨lctx, .mkIntUOp uop a, s⟩ :=
  .ofApp _ (.ofBase (.ofIcst wfop)) wfa

def LamWF.mkIntBinOp {ltv : LamTyVal}
  (wfop : IntConst.LamWF binOp (.func (.base .int) (.func (.base .int) s)))
  (wfa : LamWF ltv ⟨lctx, a, .base .int⟩) (wfb : LamWF ltv ⟨lctx, b, .base .int⟩) :
  LamWF ltv ⟨lctx, .mkIntBinOp binOp a b, s⟩ :=
  .ofApp _ (.ofApp _ (.ofBase (.ofIcst wfop)) wfa) wfb

def LamWF.mkBvofNat {ltv : LamTyVal}
  (wfi : LamWF ltv ⟨lctx, i, .base .nat⟩) : LamWF ltv ⟨lctx, .mkBvofNat n i, .base (.bv n)⟩ :=
  .ofApp _ (.ofBase (.ofBvofNat n)) wfi

def LamWF.mkBvofInt {ltv : LamTyVal}
  (wfi : LamWF ltv ⟨lctx, i, .base .int⟩) : LamWF ltv ⟨lctx, .mkBvofInt n i, .base (.bv n)⟩ :=
  .ofApp _ (.ofBase (.ofBvofInt n)) wfi

def LamWF.mkBvUOp {ltv : LamTyVal}
  (wfop : BitVecConst.LamWF uop (.func (.base (.bv n)) s))
  (wfa : LamWF ltv ⟨lctx, a, .base (.bv n)⟩) : LamWF ltv ⟨lctx, .mkBvUOp n uop a, s⟩ :=
  .ofApp _ (.ofBase (.ofBvcst wfop)) wfa

def LamWF.mkBvBinOp {ltv : LamTyVal}
  (wfop : BitVecConst.LamWF binOp (.func (.base (.bv n)) (.func (.base (.bv n)) s)))
  (wfa : LamWF ltv ⟨lctx, a, .base (.bv n)⟩) (wfb : LamWF ltv ⟨lctx, b, .base (.bv n)⟩) :
  LamWF ltv ⟨lctx, .mkBvBinOp n binOp a b, s⟩ :=
  .ofApp _ (.ofApp _ (.ofBase (.ofBvcst wfop)) wfa) wfb

def LamWF.mkBvNatBinOp {ltv : LamTyVal}
  (wfop : BitVecConst.LamWF binOp (.func (.base (.bv n)) (.func (.base .nat) s)))
  (wfa : LamWF ltv ⟨lctx, a, .base (.bv n)⟩) (wfb : LamWF ltv ⟨lctx, b, .base .nat⟩) :
  LamWF ltv ⟨lctx, .mkBvNatBinOp n binOp a b, s⟩ :=
  .ofApp _ (.ofApp _ (.ofBase (.ofBvcst wfop)) wfa) wfb

def LamWF.mkAppN {s : LamSort}
  (wfFn : LamWF ltv ⟨lctx, f, s.mkFuncs (args.map Prod.fst)⟩)
  (wfArgs : HList (fun (s, t) => LamWF ltv ⟨lctx, t, s⟩) args) :
  LamWF ltv ⟨lctx, f.mkAppN args, s⟩ :=
  match wfArgs with
  | .nil => wfFn
  | .cons (tys:=args) HArg HArgs =>
    LamWF.mkAppN (args:=args) (.ofApp _ wfFn HArg) HArgs

def LamWF.fnWFOfMkAppN
  (wfApp : LamWF ltv ⟨lctx, f.mkAppN args, s⟩) :
  LamWF ltv ⟨lctx, f, s.mkFuncs (args.map Prod.fst)⟩ :=
  match args with
  | .nil => wfApp
  | .cons _ args =>
    (LamWF.fnWFOfMkAppN (args:=args) wfApp).getFn

def LamWF.argsWFOfMkAppN {f : LamTerm}
  (wfApp : LamWF ltv ⟨lctx, f.mkAppN args, s⟩) :
  HList (fun (s, t) => LamWF ltv ⟨lctx, t, s⟩) args :=
  match args with
  | .nil => .nil
  | .cons _ args =>
    have HFn := LamWF.fnWFOfMkAppN (args:=args) wfApp
    have HArgs := LamWF.argsWFOfMkAppN (args:=args) wfApp
    .cons HFn.getArg HArgs

def LamWF.getAppFn (wft : LamWF ltv ⟨lctx, t, rty⟩) :
  (fnTy : LamSort) × LamWF ltv ⟨lctx, t.getAppFn, fnTy⟩ :=
  match wft with
  | .ofAtom n => ⟨_, .ofAtom n⟩
  | .ofEtom n => ⟨_, .ofEtom n⟩
  | .ofBase H => ⟨_, .ofBase H⟩
  | .ofBVar n => ⟨_, .ofBVar n⟩
  | .ofLam s body => ⟨_, .ofLam s body⟩
  | .ofApp argTy wfFn wfArg => by
    dsimp [LamTerm.getAppFn]
    exact LamWF.getAppFn wfFn

def LamWF.getAppArgs
  (wfApp : LamWF ltv ⟨lctx, f, s⟩) :
  HList (fun (s, t) => LamWF ltv ⟨lctx, t, s⟩) f.getAppArgs :=
  match wfApp with
  | .ofAtom n => .nil
  | .ofEtom n => .nil
  | .ofBase H => .nil
  | .ofBVar n => .nil
  | .ofLam _ body => .nil
  | .ofApp argTy wfFn wfArg => by
    rw [LamTerm.getAppArgs_app]; apply HList.append
    case xs => exact wfFn.getAppArgs
    case ys => apply HList.cons _ .nil; exact wfArg

def LamWF.mkLamFN {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtxs ls.reverse lctx, p, s⟩) :
  LamWF ltv ⟨lctx, .mkLamFN p ls, LamSort.mkFuncs s ls⟩ :=
  match ls with
  | .nil => wfp
  | .cons s ls => by
    dsimp [LamTerm.mkLamFN]
    rw [List.reverse_cons, pushLCtxs_append_singleton] at wfp
    apply LamWF.ofLam; apply LamWF.mkLamFN (ls:=ls) wfp

def LamWF.fromMkLamFN {ltv : LamTyVal}
  (wfLam : LamWF ltv ⟨lctx, .mkLamFN p ls, LamSort.mkFuncs s ls⟩) :
  LamWF ltv ⟨pushLCtxs ls.reverse lctx, p, s⟩ :=
  match ls with
  | .nil => wfLam
  | .cons s ls => by
    dsimp [LamTerm.mkLamFN] at wfLam;
    rw [List.reverse_cons, pushLCtxs_append_singleton]
    apply LamWF.fromMkLamFN (ls:=ls); apply wfLam.getLam

def LamWF.fromMkLamFN_s_eq_mkFuncs_reverse {ltv : LamTyVal}
  (wfLam : LamWF ltv ⟨lctx, .mkLamFN p ls, s⟩) :
  (s' : LamSort) ×' (s = LamSort.mkFuncs s' ls) :=
  match ls with
  | .nil => ⟨s, rfl⟩
  | .cons argTy ls => by
    dsimp [LamTerm.mkLamFN] at wfLam; cases wfLam
    case ofLam _ wfBody =>
      have ⟨s', seq⟩ := fromMkLamFN_s_eq_mkFuncs_reverse wfBody
      exists s'; cases seq; rfl

def LamWF.mkForallEFN {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtxs ls.reverse lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkForallEFN p ls, .base .prop⟩ :=
  match ls with
  | .nil => wfp
  | .cons s ls => by
    dsimp [LamTerm.mkForallEFN]
    rw [List.reverse_cons, pushLCtxs_append_singleton] at wfp
    apply LamWF.mkForallEF; apply LamWF.mkForallEFN (ls:=ls) wfp

def LamWF.fromMkForallEFN {ltv : LamTyVal}
  (wf : LamWF ltv ⟨lctx, .mkForallEFN p ls, .base .prop⟩) :
  LamWF ltv ⟨pushLCtxs ls.reverse lctx, p, .base .prop⟩ :=
  match ls with
  | .nil => wf
  | .cons s ls => by
    dsimp [LamTerm.mkForallEFN] at wf
    rw [List.reverse_cons, pushLCtxs_append_singleton]
    apply LamWF.fromMkForallEFN (ls:=ls); apply LamWF.fromMkForallEF wf

def LamWF.mkForallEFN' {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtxs ls lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkForallEFN p ls.reverse, .base .prop⟩ := by
  apply LamWF.mkForallEFN; rw [List.reverse_reverse]; exact wfp

def LamWF.fromMkForallEFN' {ltv : LamTyVal}
  (wf : LamWF ltv ⟨lctx, .mkForallEFN p ls.reverse, .base .prop⟩) :
  LamWF ltv ⟨pushLCtxs ls lctx, p, .base .prop⟩ := by
  rw [← List.reverse_reverse (as:=ls)]; apply LamWF.fromMkForallEFN wf

def LamWF.ofAtom' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : ltv.lamVarTy n = s) : LamWF ltv ⟨lctx, .atom n, s⟩ := by
  rw [← heq]; apply LamWF.ofAtom

def LamWF.ofEtom' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : ltv.lamEVarTy n = s) : LamWF ltv ⟨lctx, .etom n, s⟩ := by
  rw [← heq]; apply LamWF.ofEtom

def LamWF.ofBVar' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : lctx n = s) : LamWF ltv ⟨lctx, .bvar n, s⟩ := by
  rw [← heq]; apply LamWF.ofBVar

def LamWF.bvarApps
  (wft : LamWF ltv ⟨pushLCtxs (List.reverseAux ex lctx) lctx', t, LamSort.mkFuncsRev s lctx⟩) :
  LamWF ltv ⟨pushLCtxs (List.reverseAux ex lctx) lctx', t.bvarApps lctx ex.length, s⟩ :=
  match lctx with
  | .nil => wft
  | .cons ty lctx =>
    let lctxr := pushLCtxs (List.reverseAux ex (ty::lctx)) lctx'
    .ofApp _ (LamWF.bvarApps (ex:=ty::ex) wft) (by
      have tyeq : ty = lctxr ex.length := by
        have exlt : List.length ex < List.length (List.reverse (ty :: ex)) := by
          rw [List.length_reverse]; apply Nat.le_refl
        dsimp [lctxr]; rw [← List.reverseAux, List.reverseAux_eq]
        rw [pushLCtxs_lt (by rw [List.length_append]; apply Nat.le_trans exlt (Nat.le_add_right _ _))]
        rw [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left exlt];
        rw [List.getElem?_reverse (by dsimp [List.length]; apply Nat.le_refl _)]
        dsimp [List.length]; simp
      conv => enter [2, 3]; rw [tyeq]
      exact .ofBVar _)

def LamWF.bvarAppsRev_Aux :
  LamWF ltv ⟨pushLCtxs (List.reverse lctx) (pushLCtx ty lctx'), LamTerm.bvar (List.length lctx), ty⟩ := by
  have tyeq : ty = pushLCtxs lctx.reverse (pushLCtx ty lctx') lctx.length := by
    rw [pushLCtxs_ge] <;> rw [List.length_reverse]
    rw [Nat.sub_self]; apply Nat.le_refl
  conv => enter [2, 3]; rw [tyeq]
  exact .ofBVar _

def LamWF.bvarAppsRev
  (wft : LamWF ltv ⟨pushLCtxs lctx.reverse lctx', t, LamSort.mkFuncs s lctx⟩) :
  LamWF ltv ⟨pushLCtxs lctx.reverse lctx', t.bvarAppsRev lctx, s⟩ :=
  match lctx with
  | .nil => wft
  | .cons ty lctx => by
    dsimp [LamTerm.bvarAppsRev]
    revert wft; rw [List.reverse_cons, pushLCtxs_append, pushLCtxs_singleton]
    intro wft; apply bvarAppsRev (.ofApp _ wft _); apply LamWF.bvarAppsRev_Aux

def LamWF.fromBVarAppsRev
  (wfAp : LamWF ltv ⟨pushLCtxs lctx.reverse lctx', t.bvarAppsRev lctx, s⟩) :
  LamWF ltv ⟨pushLCtxs lctx.reverse lctx', t, LamSort.mkFuncs s lctx⟩ :=
  match lctx with
  | .nil => wfAp
  | .cons ty lctx => by
    dsimp [LamTerm.bvarAppsRev] at wfAp; revert wfAp
    rw [List.reverse_cons, pushLCtxs_append, pushLCtxs_singleton]
    intro wfAp; have wfAp' := fromBVarAppsRev wfAp; exact wfAp'.getFn

def LamWF.ofLamTerm {ltv : LamTyVal} :
  {lctx : Nat → LamSort} → (t : LamTerm) → Option ((rty : LamSort) × LamWF ltv ⟨lctx, t, rty⟩)
| _,    .atom n => .some ⟨ltv.lamVarTy n, .ofAtom n⟩
| _,    .etom n => .some ⟨ltv.lamEVarTy n, .ofEtom n⟩
| _,    .base b =>
  let bWF := LamBaseTerm.LamWF.ofLamBaseTerm ltv b
  .some ⟨bWF.fst, .ofBase bWF.snd⟩
| lctx, .bvar n => .some ⟨lctx n, .ofBVar n⟩
| lctx, .lam argTy body =>
  let bodyWf := @LamWF.ofLamTerm ltv (pushLCtx argTy lctx) body
  match bodyWf with
  | .some ⟨bodyTy, wf⟩ => .some ⟨.func argTy bodyTy, .ofLam bodyTy wf⟩
  | .none => .none
| lctx, .app s fn arg =>
  let fnWf := @LamWF.ofLamTerm ltv lctx fn
  let argWf := @LamWF.ofLamTerm ltv lctx arg
  match fnWf, argWf with
  | .some (⟨.func ty₁ ty₂, fnWf⟩), .some ⟨argTy, argWf⟩ =>
    match heq : ty₁.beq s, heqa : argTy.beq s with
    | true, true =>
      have tyEq := LamSort.eq_of_beq_eq_true heq
      have argTyEq := LamSort.eq_of_beq_eq_true heqa
      .some ⟨ty₂, .ofApp s (tyEq ▸ fnWf) (argTyEq ▸ argWf)⟩
    | _, _ => .none
  | _, _ => .none

-- Of course `ofLamTerm` is sound with respect to `LamWF`. So, we
--   only need to show that it's complete
theorem LamWF.complete {ltv : LamTyVal} :
  {j : LamJudge} → (wf : LamWF ltv j) → LamWF.ofLamTerm j.rterm = .some ⟨j.rty, wf⟩
| .(_), @LamWF.ofAtom _ lctx n => rfl
| .(_), @LamWF.ofEtom _ lctx n => rfl
| .(_), @LamWF.ofBase _ lctx b s h => by
  unfold ofLamTerm; rw [LamBaseTerm.lamWF_complete]
| .(_), @LamWF.ofBVar _ lctx n => rfl
| .(_), @LamWF.ofLam _ lctx argTy bodyTy body H => by
  unfold ofLamTerm;
  have IH := LamWF.complete H; simp at IH; rw [IH];
| .(_), @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg => by
  unfold ofLamTerm;
  have IHFn := LamWF.complete HFn
  have IHArg := LamWF.complete HArg
  simp at IHFn; simp at IHArg
  rw [IHFn]; rw [IHArg]; simp; rw [LamSort.beq_refl]

theorem LamTerm.lamCheck?_of_lamWF
  {ltv : LamTyVal} {lctx : Nat → LamSort} {t : LamTerm} {ty : LamSort} :
  LamWF ltv ⟨lctx, t, ty⟩ → t.lamCheck? ltv lctx = .some ty := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rty := ty : LamJudge} = Judge
  intro HWf; induction HWf generalizing lctx t ty <;>
    injection JudgeEq with lctx_eq rterm_eq rty_eq <;>
    rw [rterm_eq, rty_eq] <;> try rfl
  case ofBase lctx' b s H =>
    rw [lamCheck?]; rw [LamBaseTerm.lamCheck_of_LamWF H]
  case ofBVar lctx' n =>
    rw [lctx_eq]; rfl
  case ofLam lctx' argTy bodyTy body _ H_ih =>
    rw [lctx_eq];
    simp [lamCheck?]; rw [H_ih]; rfl
  case ofApp lctx' argTy resTy fn arg _ _ HFn_ih HArg_ih =>
    rw [lctx_eq]
    simp [lamCheck?];
    rw [@HFn_ih lctx' fn (LamSort.func argTy resTy)] <;> try rfl;
    rw [@HArg_ih lctx' arg argTy] <;> try rfl;
    simp [LamSort.beq_refl]

def LamWF.ofLamCheck? {ltv : LamTyVal} :
  {lctx : Nat → LamSort} → {t : LamTerm} → {ty : LamSort} →
  t.lamCheck? ltv lctx = .some ty → LamWF ltv ⟨lctx, t, ty⟩
| lctx, .atom n, ty, HCheck => by
  have HCheck' := Option.some.inj HCheck
  rw [← HCheck']; apply LamWF.ofAtom
| lctx, .etom n, ty, HCheck => by
  have HCheck' := Option.some.inj HCheck
  rw [← HCheck']; apply LamWF.ofEtom
| lctx, .base b, ty, HCheck => by
  simp [LamTerm.lamCheck?] at HCheck; exact LamWF.ofBase (LamBaseTerm.LamWF.ofCheck HCheck)
| lctx, .bvar n, ty, HCheck => by
  simp [LamTerm.lamCheck?] at HCheck; rw [← HCheck]; apply LamWF.ofBVar
| lctx, .lam argTy body, ty, HCheck => by
  dsimp [LamTerm.lamCheck?] at HCheck; revert HCheck
  cases CheckEq : LamTerm.lamCheck? ltv (pushLCtx argTy lctx) body
  case none => intro contra; cases contra
  case some bodyTy =>
    dsimp; intro tyEq; rw [← Option.some.inj tyEq]
    apply LamWF.ofLam; apply (ofLamCheck? CheckEq)
| lctx, .app s fn arg, ty, HCheck => by
  simp [LamTerm.lamCheck?] at HCheck; revert HCheck
  match CheckFnEq : LamTerm.lamCheck? ltv lctx fn, CheckArgEq : LamTerm.lamCheck? ltv lctx arg with
  | .some (LamSort.func ty₁ ty₂), .some argTy =>
    dsimp;
    cases heq : LamSort.beq ty₁ argTy <;> try (intro contra; cases contra)
    have heq' : ty₁ = argTy := LamSort.eq_of_beq_eq_true heq; cases heq'
    cases heqa : LamSort.beq ty₁ s <;> try (intro contra; cases contra)
    cases LamSort.eq_of_beq_eq_true heqa
    apply LamWF.ofApp (argTy:=s) (ofLamCheck? CheckFnEq) (ofLamCheck? CheckArgEq)
  | .some (LamSort.func _ _), .none => intro contra; cases contra
  | .some (LamSort.atom _), _ => intro contra; cases contra
  | .some (LamSort.base _), _ => intro contra; cases contra
  | .none, _ => intro contra; cases contra

@[irreducible] def LamWF.ofNonemptyLamWF (H : Nonempty (LamWF ltv ⟨lctx, t, s⟩)) :
  LamWF ltv ⟨lctx, t, s⟩ := by
  cases h₁ : LamTerm.lamCheck? ltv lctx t
  case none =>
    apply False.elim; have ⟨wf⟩ := H
    have hChk := LamTerm.lamCheck?_of_lamWF wf
    rw [h₁] at hChk; cases hChk
  case some s' =>
    cases h₂ : s'.beq s
    case false =>
      apply False.elim; have ⟨wf⟩ := H
      have hChk := LamTerm.lamCheck?_of_lamWF wf
      rw [h₁] at hChk; rw [Option.some.inj hChk] at h₂
      rw [LamSort.beq_refl] at h₂; cases h₂
    case true =>
      rw [LamSort.eq_of_beq_eq_true h₂] at h₁
      apply LamWF.ofLamCheck? h₁

end Auto.Embedding.Lam
