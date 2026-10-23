module

public import Auto.Embedding.LamBase.LamBaseTerm

@[expose] public section

/-! Terms `LamTerm` and operations on them -/

namespace Auto.Embedding.Lam

open ToExprExtra

inductive LamTerm
  | atom    : Nat → LamTerm
  -- Existential atoms. Supports definition and skolemization
  | etom    : Nat → LamTerm
  | base    : LamBaseTerm → LamTerm
  | bvar    : Nat → LamTerm
  | lam     : LamSort → LamTerm → LamTerm
  -- The `LamSort` is here so that both the type of
  --   the function and argument can be inferred directly
  --   when we know the type of the application
  | app     : LamSort → LamTerm → LamTerm → LamTerm
deriving Inhabited, Hashable, Lean.ToExpr

def LamTerm.isAtom : LamTerm → Bool
| .atom _ => true
| _ => false

def LamTerm.isEtom : LamTerm → Bool
| .etom _ => true
| _ => false

def LamTerm.isBase : LamTerm → Bool
| .base _ => true
| _ => false

def LamTerm.isbvar : LamTerm → Bool
| .bvar _ => true
| _ => false

def LamTerm.isLam : LamTerm → Bool
| .lam _ _ => true
| _ => false

def LamTerm.isApp : LamTerm → Bool
| .app _ _ _ => true
| _ => false

def LamTerm.isForallE : LamTerm → Bool
| .base (.forallE _) => true
| _ => false

def LamTerm.isExistE : LamTerm → Bool
| .base (.existE _) => true
| _ => false

def LamTerm.isEq : LamTerm → Bool
| .base (.eq _) => true
| _ => false

def LamTerm.isMkForallE : LamTerm → Bool
| .app _ (.base (.forallE _)) _ => true
| _ => false

def LamTerm.isMkExistE : LamTerm → Bool
| .app _ (.base (.existE _)) _ => true
| _ => false

def LamTerm.isMkEq : LamTerm → Bool
| .app _ (.app _ (.base (.eq _)) _) _ => true
| _ => false

def LamTerm.size : LamTerm → Nat
| .atom _ => 1
| .etom _ => 1
| .base _ => 1
| .bvar _ => 1
| .lam _ t => t.size + 1
| .app _ t₁ t₂ => t₁.size + t₂.size

theorem LamTerm.size_gt_zero : size t > 0 := by
  induction t <;> try (dsimp [size]; apply Nat.le_refl)
  case lam s body IH =>
    dsimp [size]; apply Nat.le_trans IH (Nat.le_succ _)
  case app s fn arg _ IHArg =>
    dsimp [size]; apply Nat.le_trans IHArg (Nat.le_add_left _ _)

theorem LamTerm.size_ne_zero : size t ≠ 0 := by
  cases h : size t
  case zero =>
    have contra := LamTerm.size_gt_zero (t:=t)
    rw [h] at contra; cases contra
  case succ _ => intro h; cases h

theorem LamTerm.size_lam_gt_size_body : size (.lam s t) > size t := Nat.le_refl _

theorem LamTerm.size_lam_ge_size_body : size (.lam s t) ≥ size t := Nat.le_succ _

theorem LamTerm.size_app_gt_size_fn : size (.app s fn arg) > size fn :=
  Nat.add_le_add_left size_gt_zero _

theorem LamTerm.size_app_ge_size_fn : size (.app s fn arg) ≥ size fn :=
  Nat.le_add_right _ _

theorem LamTerm.size_app_gt_size_arg : size (.app s fn arg) > size arg := by
  dsimp [size]; rw [Nat.add_comm]; apply Nat.add_le_add_left size_gt_zero

theorem LamTerm.size_app_ge_size_arg : size (.app s fn arg) ≥ size arg :=
  Nat.le_add_left _ _

/--
  Check whether the term contains loose bound variables `idx` levels
    above local context root
-/
def LamTerm.hasLooseBVarEq (idx : Nat) : LamTerm → Bool
| .atom _ => false
| .etom _ => false
| .base _ => false
| .bvar n => idx.beq n
| .lam _ t => t.hasLooseBVarEq (.succ idx)
| .app _ t₁ t₂ => t₁.hasLooseBVarEq idx || t₂.hasLooseBVarEq idx

/--
  Check whether the term contains loose bound variables greater
    or equal to `idx` levels above local context root
-/
def LamTerm.hasLooseBVarGe (idx : Nat) : LamTerm → Bool
| .atom _ => false
| .etom _ => false
| .base _ => false
| .bvar n => idx.ble n
| .lam _ t => t.hasLooseBVarGe (.succ idx)
| .app _ t₁ t₂ => t₁.hasLooseBVarGe idx || t₂.hasLooseBVarGe idx

-- Whether the term contains any loose bound variables
def LamTerm.hasLooseBVar := LamTerm.hasLooseBVarGe 0

def LamTerm.maxLooseBVarSucc : LamTerm → Nat
| .atom _ => 0
| .etom _ => 0
| .base _ => 0
| .bvar n => .succ n
| .lam _ t => .pred t.maxLooseBVarSucc
| .app _ t₁ t₂ => Nat.max t₁.maxLooseBVarSucc t₂.maxLooseBVarSucc

theorem LamTerm.maxLooseBVarSucc.spec (m : Nat) :
  (t : LamTerm) → t.hasLooseBVarGe m = true ↔ t.maxLooseBVarSucc > m
| .atom _ => by
  apply Iff.intro
  case mp => intro h; cases h
  case mpr => intro h; cases h
| .etom _ => by
  apply Iff.intro
  case mp => intro h; cases h
  case mpr => intro h; cases h
| .base _ => by
  apply Iff.intro
  case mp => intro h; cases h
  case mpr => intro h; cases h
| .bvar n => by
  dsimp [hasLooseBVarGe, maxLooseBVarSucc];
  apply Iff.intro <;> intro h
  case mp => exact Nat.succ_le_succ (Nat.le_of_ble_eq_true h)
  case mpr => exact Nat.ble_eq_true_of_le (Nat.le_of_succ_le_succ h)
| .lam _ t => by
  dsimp [hasLooseBVarGe, maxLooseBVarSucc];
  let IH := spec (Nat.succ m) t
  apply Iff.intro <;> intro h
  case mp =>
    let IH' := Nat.pred_le_pred (IH.mp h)
    rw [Nat.pred_succ] at IH'; exact IH'
  case mpr =>
    apply IH.mpr; apply Nat.lt_pred_iff.mp; exact h
| .app _ t₁ t₂ => by
  dsimp [hasLooseBVarGe, maxLooseBVarSucc];
  rw [Bool.or_eq_true]; rw [spec m t₁]; rw [spec m t₂];
  simp [Nat.max]
  omega

def LamTerm.maxEVarSucc : LamTerm → Nat
| .atom _ => 0
| .etom n => .succ n
| .base _ => 0
| .bvar _ => 0
| .lam _ t => t.maxEVarSucc
| .app _ t₁ t₂ => Nat.max t₁.maxEVarSucc t₂.maxEVarSucc

theorem LamTerm.maxEVarSucc_lam : (lam s t).maxEVarSucc = t.maxEVarSucc := rfl

theorem LamTerm.maxEVarSucc_app : (app s fn arg).maxEVarSucc = max fn.maxEVarSucc arg.maxEVarSucc := rfl

def LamTerm.flip (argTy₁ argTy₂ resTy : LamSort) : LamTerm :=
  .lam (.func argTy₁ (.func argTy₂ resTy)) (
    .lam argTy₂ (.lam argTy₁ (.app argTy₂ (.app argTy₁ (.bvar 2) (.bvar 0)) (.bvar 1)))
  )

theorem LamTerm.maxEVarSucc_flip : LamTerm.maxEVarSucc (flip argTy₁ argTy₂ resTy) = 0 := rfl

def LamTerm.flipApp (t : LamTerm) (argTy₁ argTy₂ resTy : LamSort) : LamTerm :=
  .app (.func argTy₁ (.func argTy₂ resTy)) (.flip argTy₁ argTy₂ resTy) t

theorem LamTerm.maxEVarSucc_flipApp : LamTerm.maxEVarSucc (flipApp t argTy₁ argTy₂ resTy) = t.maxEVarSucc := by
  dsimp [flipApp]; rw [maxEVarSucc_app, maxEVarSucc_flip, Nat.max_zero_left]

abbrev LamTerm.nmodeq : LamTerm :=
  .lam (.base .nat) (.lam (.base .nat) (.lam (.base .nat) (.app (.base .nat) (.app (.base .nat) (.base (.eq (.base .nat)))
    (.app (.base .nat) (.app (.base .nat) (.base .nmod) (.bvar 1)) (.bvar 2)))
    (.app (.base .nat) (.app (.base .nat) (.base .nmod) (.bvar 0)) (.bvar 2)))))

theorem LamTerm.maxEVarSucc_nmodeq : LamTerm.maxEVarSucc nmodeq = 0 := rfl

abbrev LamTerm.nge : LamTerm := .flipApp (.base .nle) (.base .nat) (.base .nat) (.base .prop)

abbrev LamTerm.ngt : LamTerm := .flipApp (.base .nlt) (.base .nat) (.base .nat) (.base .prop)

abbrev LamTerm.ige : LamTerm := .flipApp (.base .ile) (.base .int) (.base .int) (.base .prop)

abbrev LamTerm.igt : LamTerm := .flipApp (.base .ilt) (.base .int) (.base .int) (.base .prop)

abbrev LamTerm.imodeq : LamTerm :=
  .lam (.base .int) (.lam (.base .int) (.lam (.base .int) (.app (.base .int) (.app (.base .int) (.base (.eq (.base .int)))
    (.app (.base .int) (.app (.base .int) (.base .iemod) (.bvar 1)) (.bvar 2)))
    (.app (.base .int) (.app (.base .int) (.base .iemod) (.bvar 0)) (.bvar 2)))))

theorem LamTerm.maxEVarSucc_imodeq : LamTerm.maxEVarSucc imodeq = 0 := rfl

abbrev LamTerm.sge : LamTerm := .flipApp (.base .sle) (.base .string) (.base .string) (.base .prop)

abbrev LamTerm.sgt : LamTerm := .flipApp (.base .slt) (.base .string) (.base .string) (.base .prop)

abbrev LamTerm.bvuge (n : Nat) : LamTerm := .flipApp (.base (.bvule n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvugt (n : Nat) : LamTerm := .flipApp (.base (.bvult n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvsge (n : Nat) : LamTerm := .flipApp (.base (.bvsle n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvsgt (n : Nat) : LamTerm := .flipApp (.base (.bvslt n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvpropuge (n : Nat) : LamTerm := .flipApp (.base (.bvpropule n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvpropugt (n : Nat) : LamTerm := .flipApp (.base (.bvpropult n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvpropsge (n : Nat) : LamTerm := .flipApp (.base (.bvpropsle n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvpropsgt (n : Nat) : LamTerm := .flipApp (.base (.bvpropslt n)) (.base (.bv n)) (.base (.bv n)) (.base .bool)

abbrev LamTerm.bvsmtHshl (n m : Nat) : LamTerm :=
  .lam (.base (.bv n)) (.lam (.base (.bv m)) (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvshl n)) (.bvar 1)) (.app (.base (.bv m)) (.base (.bvtoNat m)) (.bvar 0))))

theorem LamTerm.maxEVarSucc_bvsmtHshl : maxEVarSucc (bvsmtHshl n m) = 0 := rfl

abbrev LamTerm.bvsmtHlshr (n m : Nat) : LamTerm :=
  .lam (.base (.bv n)) (.lam (.base (.bv m)) (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvlshr n)) (.bvar 1)) (.app (.base (.bv m)) (.base (.bvtoNat m)) (.bvar 0))))

theorem LamTerm.maxEVarSucc_bvsmtHlshr : maxEVarSucc (bvsmtHlshr n m) = 0 := rfl

abbrev LamTerm.bvsmtHashr (n m : Nat) : LamTerm :=
  .lam (.base (.bv n)) (.lam (.base (.bv m)) (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvashr n)) (.bvar 1)) (.app (.base (.bv m)) (.base (.bvtoNat m)) (.bvar 0))))

theorem LamTerm.maxEVarSucc_bvsmtHashr : maxEVarSucc (bvsmtHashr n m) = 0 := rfl

abbrev LamTerm.bvrotateLeft (n : Nat) : LamTerm :=
  .lam (.base (.bv n)) (.lam (.base .nat) (.app (.base (.bv n))
    (.app (.base (.bv n)) (.base (.bvor n))
      (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvshl n)) (.bvar 1)) (.app (.base .nat) (.app (.base .nat) (.base .nmod) (.bvar 0)) (.base (.natVal n)))))
    (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvlshr n)) (.bvar 1))
      (.app (.base .nat) (.app (.base .nat) (.base .nsub) (.base (.natVal n))) (.app (.base .nat) (.app (.base .nat) (.base .nmod) (.bvar 0)) (.base (.natVal n)))))))

abbrev LamTerm.bvrotateRight (n : Nat) : LamTerm :=
  .lam (.base (.bv n)) (.lam (.base .nat) (.app (.base (.bv n))
    (.app (.base (.bv n)) (.base (.bvor n))
      (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvlshr n)) (.bvar 1)) (.app (.base .nat) (.app (.base .nat) (.base .nmod) (.bvar 0)) (.base (.natVal n)))))
    (.app (.base .nat) (.app (.base (.bv n)) (.base (.bvshl n)) (.bvar 1))
      (.app (.base .nat) (.app (.base .nat) (.base .nsub) (.base (.natVal n))) (.app (.base .nat) (.app (.base .nat) (.base .nmod) (.bvar 0)) (.base (.natVal n)))))))

def LamTerm.mkNot (t : LamTerm) : LamTerm :=
  .app (.base .prop) (.base .not) t

theorem LamTerm.maxEVarSucc_mkNot :
  (mkNot t).maxEVarSucc = t.maxEVarSucc := by
  dsimp [mkNot, maxEVarSucc]; rw [Nat.max, Nat.max_zero_left]

def LamTerm.mkAnd (t₁ t₂ : LamTerm) : LamTerm :=
  .app (.base .prop) (.app (.base .prop) (.base .and) t₁) t₂

theorem LamTerm.maxEVarSucc_mkAnd :
  (mkAnd t₁ t₂).maxEVarSucc = max t₁.maxEVarSucc t₂.maxEVarSucc := by
  dsimp [mkAnd, maxEVarSucc]; rw [Nat.max, Nat.max, Nat.max_zero_left]

def LamTerm.mkOr (t₁ t₂ : LamTerm) : LamTerm :=
  .app (.base .prop) (.app (.base .prop) (.base .or) t₁) t₂

theorem LamTerm.maxEVarSucc_mkOr :
  (mkOr t₁ t₂).maxEVarSucc = max t₁.maxEVarSucc t₂.maxEVarSucc := by
  dsimp [mkOr, maxEVarSucc]; rw [Nat.max, Nat.max, Nat.max_zero_left]

def LamTerm.mkImp (t₁ t₂ : LamTerm) : LamTerm :=
  .app (.base .prop) (.app (.base .prop) (.base .imp) t₁) t₂

theorem LamTerm.maxEVarSucc_mkImp :
  (mkImp t₁ t₂).maxEVarSucc = max t₁.maxEVarSucc t₂.maxEVarSucc := by
  dsimp [mkImp, maxEVarSucc]; rw [Nat.max, Nat.max, Nat.max_zero_left]

def LamTerm.mkIff (t₁ t₂ : LamTerm) : LamTerm :=
  .app (.base .prop) (.app (.base .prop) (.base .iff) t₁) t₂

theorem LamTerm.maxEVarSucc_mkIff :
  (mkIff t₁ t₂).maxEVarSucc = max t₁.maxEVarSucc t₂.maxEVarSucc := by
  dsimp [mkIff, maxEVarSucc]; rw [Nat.max, Nat.max, Nat.max_zero_left]

def LamTerm.mkEq (s : LamSort) (t₁ t₂ : LamTerm) : LamTerm :=
  .app s (.app s (.base (.eq s)) t₁) t₂

theorem LamTerm.maxLooseBVarSucc_mkEq :
  (mkEq s t₁ t₂).maxLooseBVarSucc = max t₁.maxLooseBVarSucc t₂.maxLooseBVarSucc := by
  dsimp [mkEq, maxLooseBVarSucc, Nat.max]; rw [Nat.max_zero_left]

theorem LamTerm.maxEVarSucc_mkEq :
  (mkEq s t₁ t₂).maxEVarSucc = max t₁.maxEVarSucc t₂.maxEVarSucc := by
  dsimp [mkEq, maxEVarSucc, Nat.max]; rw [Nat.max_zero_left]

def LamTerm.mkForallE (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.forallE s)) p

theorem LamTerm.maxLooseBVarSucc_mkForallE :
  (mkForallE s p).maxLooseBVarSucc = p.maxLooseBVarSucc := by
  dsimp [mkForallE, maxLooseBVarSucc, Nat.max]; rw [Nat.max_zero_left]

theorem LamTerm.maxEVarSucc_mkForallE :
  (mkForallE s p).maxEVarSucc = p.maxEVarSucc := by
  dsimp [mkForallE, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkForallEF (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.forallE s)) (.lam s p)

theorem LamTerm.maxLooseBVarSucc_mkForallEF :
  (mkForallEF s p).maxLooseBVarSucc = p.maxLooseBVarSucc.pred := by
  dsimp [mkForallEF, maxLooseBVarSucc, Nat.max]; rw [Nat.max_zero_left]

theorem LamTerm.maxEVarSucc_mkForallEF :
  (mkForallEF s p).maxEVarSucc = p.maxEVarSucc := by
  dsimp [mkForallEF, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkExistE (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.existE s)) p

theorem LamTerm.maxLooseBVarSucc_mkExistE :
  (mkExistE s p).maxLooseBVarSucc = p.maxLooseBVarSucc := by
  dsimp [mkExistE, maxLooseBVarSucc, Nat.max]; rw [Nat.max_zero_left]

theorem LamTerm.maxEVarSucc_mkExistE :
  (mkExistE s p).maxEVarSucc = p.maxEVarSucc := by
  dsimp [mkExistE, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkExistEF (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.existE s)) (.lam s p)

theorem LamTerm.maxLooseBVarSucc_mkExistEF :
  (mkExistEF s p).maxLooseBVarSucc = p.maxLooseBVarSucc.pred := by
  dsimp [mkExistEF, maxLooseBVarSucc, Nat.max]; rw [Nat.max_zero_left]

theorem LamTerm.maxEVarSucc_mkExistEF :
  (mkExistEF s p).maxEVarSucc = p.maxEVarSucc := by
  dsimp [mkExistEF, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkIte (s : LamSort) (b x y : LamTerm) : LamTerm :=
  .app s (.app s (.app (.base .prop) (.base (.ite s)) b) x) y

theorem LamTerm.maxLooseBVarSucc_mkIte :
  (mkIte s b x y).maxLooseBVarSucc = max (max b.maxLooseBVarSucc x.maxLooseBVarSucc) y.maxLooseBVarSucc := by
  dsimp [mkIte, maxLooseBVarSucc, Nat.max]; rw [Nat.max_zero_left]

theorem LamTerm.maxEVarSucc_mkIte :
  (mkIte s b x y).maxEVarSucc = max (max b.maxEVarSucc x.maxEVarSucc) y.maxEVarSucc := by
  dsimp [mkIte, maxEVarSucc, Nat.max]; rw [Nat.max_zero_left]

def LamTerm.mkNatVal (n : Nat) : LamTerm := .base (.natVal n)

theorem LamTerm.maxEVarSucc_mkNatVal : (mkNatVal n).maxEVarSucc = 0 := rfl

def LamTerm.mkNatBinOp (binOp : NatConst) (a b : LamTerm) : LamTerm :=
  .app (.base .nat) (.app (.base .nat) (.base (.ncst binOp)) a) b

theorem LamTerm.maxEVarSucc_mkNatBinOp :
  (mkNatBinOp op a b).maxEVarSucc = max a.maxEVarSucc b.maxEVarSucc := by
  dsimp [mkNatBinOp, maxEVarSucc]; simp [Nat.max]

def LamTerm.mkIOfNat (n : LamTerm) : LamTerm :=
  .app (.base .nat) (.base .iofNat) n

theorem LamTerm.maxEVarSucc_mkIOfNat :
  (mkIOfNat n).maxEVarSucc = n.maxEVarSucc := by
  dsimp [mkIOfNat, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkINegSucc (n : LamTerm) : LamTerm :=
  .app (.base .nat) (.base .inegSucc) n

theorem LamTerm.maxEVarSucc_mkINegSucc :
  (mkINegSucc n).maxEVarSucc = n.maxEVarSucc := by
  dsimp [mkINegSucc, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkIntUOp (uop : IntConst) (a : LamTerm) : LamTerm :=
  .app (.base .int) (.base (.icst uop)) a

theorem LamTerm.maxEVarSucc_mkIntUOp :
  (mkIntUOp uop n).maxEVarSucc = n.maxEVarSucc := by
  dsimp [mkIntUOp, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkIntBinOp (binOp : IntConst) (a b : LamTerm) : LamTerm :=
  .app (.base .int) (.app (.base .int) (.base (.icst binOp)) a) b

theorem LamTerm.maxEVarSucc_mkIntBinOp :
  (mkIntBinOp op a b).maxEVarSucc = max a.maxEVarSucc b.maxEVarSucc := by
  dsimp [mkIntBinOp, maxEVarSucc]; simp [Nat.max]

/-- Make `BitVec.ofNat n i` -/
def LamTerm.mkBvofNat (n : Nat) (i : LamTerm) : LamTerm :=
  .app (.base .nat) (.base (.bvofNat n)) i

theorem LamTerm.maxEVarSucc_mkBvofNat :
  (mkBvofNat n i).maxEVarSucc = i.maxEVarSucc := by
  dsimp [mkBvofNat, maxEVarSucc]; apply Nat.max_zero_left

/-- Make `BitVec.ofInt n i` -/
def LamTerm.mkBvofInt (n : Nat) (i : LamTerm) : LamTerm :=
  .app (.base .int) (.base (.bvofInt n)) i

theorem LamTerm.maxEVarSucc_mkBvofInt :
  (mkBvofInt n i).maxEVarSucc = i.maxEVarSucc := by
  dsimp [mkBvofInt, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkBvUOp (n : Nat) (uop : BitVecConst) (a : LamTerm) : LamTerm :=
  .app (.base (.bv n)) (.base (.bvcst uop)) a

theorem LamTerm.maxEVarSucc_mkBvUOp :
  (mkBvUOp n uop a).maxEVarSucc = a.maxEVarSucc := by
  dsimp [mkBvUOp, maxEVarSucc]; apply Nat.max_zero_left

def LamTerm.mkBvBinOp (n : Nat) (binOp : BitVecConst) (a b : LamTerm) : LamTerm :=
  .app (.base (.bv n)) (.app (.base (.bv n)) (.base (.bvcst binOp)) a) b

theorem LamTerm.maxEVarSucc_mkBvBinOp :
  (mkBvBinOp n binOp a b).maxEVarSucc = max a.maxEVarSucc b.maxEVarSucc := by
  dsimp [mkBvBinOp, maxEVarSucc]; simp [Nat.max]

def LamTerm.mkBvNatBinOp (n : Nat) (binOp : BitVecConst) (a b : LamTerm) : LamTerm :=
  .app (.base .nat) (.app (.base (.bv n)) (.base (.bvcst binOp)) a) b

theorem LamTerm.maxEVarSucc_mkBvNatBinOp :
  (mkBvNatBinOp n binOp a b).maxEVarSucc = max a.maxEVarSucc b.maxEVarSucc := by
  dsimp [mkBvNatBinOp, maxEVarSucc]; simp [Nat.max]

def LamTerm.mkAppN (t : LamTerm) : List (LamSort × LamTerm) → LamTerm
| .nil => t
| .cons (s, arg) args => (LamTerm.app s t arg).mkAppN args

theorem LamTerm.maxEVarSucc_mkAppN
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  (LamTerm.mkAppN t args).maxEVarSucc ≤ n := by
  induction hs generalizing t
  case nil => exact ht
  case cons head tail IH =>
    dsimp [mkAppN]; apply IH; dsimp [maxEVarSucc]
    rw [Nat.max_le]; exact And.intro ht head

-- Given `t` and `[s₀, s₁, ⋯, sᵢ₋₁]`, return `λ (? : s₀) ⋯ (? : sᵢ₋₁), t`
def LamTerm.mkLamFN (t : LamTerm) : List LamSort → LamTerm
| .nil => t
| .cons s lctx => LamTerm.lam s (t.mkLamFN lctx)

theorem LamTerm.mkLamFN_append :
  mkLamFN t (l₁ ++ l₂) = mkLamFN (mkLamFN t l₂) l₁ := by
  induction l₁ generalizing t
  case nil => rfl
  case cons s l₁ IH =>
    rw [List.cons_append]; dsimp [mkLamFN]; rw [IH]

theorem LamTerm.mkLamFN_append_singleton :
  mkLamFN t (l₁ ++ [s]) = mkLamFN (.lam s t) l₁ := by
  rw [mkLamFN_append]; rfl

theorem LamTerm.maxEVarSucc_mkLamFN {t : LamTerm} :
  (t.mkLamFN lctx).maxEVarSucc = t.maxEVarSucc := by
  induction lctx generalizing t
  case nil => rfl
  case cons s lctx IH =>
    dsimp [mkLamFN, maxEVarSucc]; rw [IH]

-- Given `t` and `[s₀, s₁, ⋯, sᵢ₋₁]`, return `∀ (? : sᵢ₋₁) ⋯ (? : s₀), t`
def LamTerm.mkForallEFN (t : LamTerm) : List LamSort → LamTerm
| .nil => t
| .cons s lctx => LamTerm.mkForallEF s (t.mkForallEFN lctx)

theorem LamTerm.maxEVarSucc_mkForallEFN {t : LamTerm} :
  (t.mkForallEFN lctx).maxEVarSucc = t.maxEVarSucc := by
  induction lctx generalizing t
  case nil => rfl
  case cons s lctx IH =>
    dsimp [mkForallEF, mkForallEFN, maxEVarSucc]; rw [IH]
    rw [Nat.max, Nat.max_zero_left]

theorem LamTerm.mkForallEFN_append :
  mkForallEFN t (l₁ ++ l₂) = mkForallEFN (mkForallEFN t l₂) l₁ := by
  induction l₁ generalizing t
  case nil => rfl
  case cons s l₁ IH =>
    dsimp [mkForallEFN]; rw [IH]

theorem LamTerm.mkForallEFN_append_singleton :
  mkForallEFN t (l₁ ++ [s]) = mkForallEFN (mkForallEF s t) l₁ := by
  rw [mkForallEFN_append]; rfl

/-- Given `λ (_ : ty₀) ⋯ (_ : tyᵢ₋₁), body`, return `body` -/
def LamTerm.getLamBody : LamTerm → LamTerm
| .lam _ body => getLamBody body
| t => t

theorem LamTerm.maxEVarSucc_getLamBody : (LamTerm.getLamBody t).maxEVarSucc = t.maxEVarSucc := by
  induction t <;> try rfl
  case lam s body IH => dsimp [getLamBody]; apply IH

/-- Given `λ (_ : ty₀) ⋯ (_ : tyᵢ₋₁), _`, return `[ty₀, ⋯, tyᵢ₋₁]` -/
def LamTerm.getLamTys : LamTerm → List LamSort
| .lam argTy body => argTy :: getLamTys body
| _ => []

theorem LamTerm.lamBody_lamTys_eq (t : LamTerm) : t = LamTerm.mkLamFN t.getLamBody t.getLamTys := by
  induction t <;> try rfl
  case lam s body IH =>
    dsimp [getLamBody, getLamTys]; dsimp [mkLamFN]; rw [← IH]

def LamTerm.getLamBodyN (n : Nat) (t : LamTerm) : Option LamTerm :=
  match n with
  | .zero => t
  | .succ n' =>
    match t with
    | .lam _ body => getLamBodyN n' body
    | _ => .none

theorem LamTerm.maxEVarSucc_getLamBodyN
  (heq : LamTerm.getLamBodyN n t = .some t') :
  t'.maxEVarSucc = t.maxEVarSucc := by
  induction n generalizing t t'
  case zero => cases heq; rfl
  case succ n IH =>
    cases t <;> try cases heq
    case lam s body =>
      dsimp [getLamBodyN] at heq; dsimp [maxEVarSucc]; apply IH heq

theorem LamTerm.getLamBodyN_mkLamFN_length_eq
  (h : l.length = n) : getLamBodyN n (mkLamFN t l) = .some t := by
  induction n generalizing l t
  case zero => cases l <;> cases h; rfl
  case succ n IH =>
    cases l <;> cases h
    case refl s' l =>
      dsimp [mkLamFN, getLamBodyN]
      apply IH; rfl

def LamTerm.getLamTysN (n : Nat) (t : LamTerm) : Option (List LamSort) :=
  match n with
  | .zero => .some []
  | .succ n' =>
    match t with
    | .lam argTy body => (getLamTysN n' body).bind (List.cons argTy ·)
    | _ => .none

theorem LamTerm.getLamTysN_getLamBodyN_eq_some :
  (getLamTysN n t).isSome = (getLamBodyN n t).isSome := by
  induction n generalizing t
  case zero => rfl
  case succ n IH =>
    dsimp [getLamTysN, getLamBodyN]; cases t <;> try rfl
    case lam s body => dsimp; rw [← IH]; cases getLamTysN n body <;> rfl

theorem LamTerm.getLamTysN_eq_some_of_getLamBodyN_eq_some
  (heq : getLamBodyN n t = .some body) : ∃ l, getLamTysN n t = .some l := by
  apply Option.isSome_iff_exists.mp; rw [getLamTysN_getLamBodyN_eq_some]
  apply Option.isSome_iff_exists.mpr; exists body

theorem LamTerm.getLamBodyN_eq_some_of_getLamTysN_eq_some
  (heq : getLamTysN n t = .some l) : ∃ body, getLamBodyN n t = .some body := by
  apply Option.isSome_iff_exists.mp; rw [← getLamTysN_getLamBodyN_eq_some]
  apply Option.isSome_iff_exists.mpr; exists l

theorem LamTerm.getLamTysN_getLamBodyN_eq_none :
  (getLamTysN n t).isNone = (getLamBodyN n t).isNone := by
  rw [Option.isNone_eq_not_isSome, Option.isNone_eq_not_isSome]
  rw [getLamTysN_getLamBodyN_eq_some]

theorem LamTerm.getLamTysN_getLamBodyN_eq
  (hTys : getLamTysN n t = .some l) (hBody : getLamBodyN n t = .some body) :
  t = body.mkLamFN l := by
  induction n generalizing t body l
  case zero => cases hTys; cases hBody; rfl
  case succ n IH =>
    cases t <;> try cases hTys
    case lam s body' =>
      dsimp [getLamTysN] at hTys; dsimp [getLamBodyN] at hBody
      cases h₁ : getLamTysN n body' <;> rw [h₁] at hTys <;> cases hTys
      case refl l' =>
        dsimp [mkLamFN]; rw [← IH h₁ hBody]

theorem LamTerm.getLamTysN_mkLamFN_eq_l_iff :
  getLamTysN n (mkLamFN t l) = .some l ↔ l.length = n := by
  induction n generalizing t l
  case zero =>
    dsimp [getLamTysN]; apply Iff.intro
    case mp => intro h; cases l <;> cases h; rfl
    case mpr => intro h; cases l <;> cases h; rfl
  case succ n IH =>
    dsimp [getLamTysN]; cases l
    case nil =>
      dsimp [mkLamFN]; apply Iff.intro
      case mp =>
        cases t <;> intro h <;> try cases h
        case lam s body =>
          dsimp at h; cases h₁ : getLamTysN n body <;> rw [h₁] at h <;> cases h
      case mpr =>
        intro h; cases h
    case cons s' l =>
      dsimp [mkLamFN]; cases h₁ : getLamTysN n (mkLamFN t l)
      case none => simp; intro h; rw [IH.mpr h] at h₁; cases h₁
      case some l' =>
        simp; apply Iff.intro
        case mp => intro h; cases h; apply IH.mp h₁
        case mpr => intro h; have h₂ := (IH (t:=t)).mpr h; rw [h₁] at h₂; cases h₂; rfl

def LamTerm.getAppFn : LamTerm → LamTerm
| .app _ fn _ => getAppFn fn
| t           => t

theorem LamTerm.maxEVarSucc_getAppFn : (LamTerm.getAppFn t).maxEVarSucc ≤ t.maxEVarSucc := by
  induction t <;> try apply Nat.le_refl
  case app s fn arg IHFn _ =>
    dsimp [getAppFn]; apply Nat.le_trans IHFn; apply Nat.le_max_left

def LamTerm.isHeadBetaTarget (t : LamTerm) :=
  t.isApp && t.getAppFn.isLam

def LamTerm.getAppArgsAux (args : List (LamSort × LamTerm)) : LamTerm → List (LamSort × LamTerm)
| .app s fn arg => getAppArgsAux ((s, arg) :: args) fn
| _             => args

theorem LamTerm.getAppArgsAux_eq : getAppArgsAux args t = getAppArgsAux [] t ++ args := by
  induction t generalizing args <;> try rfl
  case app s fn arg IHFn _ =>
    dsimp [getAppArgsAux]; rw [IHFn (args:=(s, arg) :: args), IHFn (args:=[(s, arg)])]
    rw [List.append_assoc]; rfl

@[irreducible] noncomputable def LamTerm.maxEVarSucc_getAppArgsAux
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  HList (fun (_, arg) => arg.maxEVarSucc ≤ n) (LamTerm.getAppArgsAux args t) := by
  induction t generalizing args <;> try exact hs
  case app s fn arg IHFn IHArg =>
    dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
    exact IHFn (.cons ht.right hs) ht.left

def LamTerm.getAppArgs := getAppArgsAux []

theorem LamTerm.getAppArgs_app : getAppArgs (.app s fn arg) = getAppArgs fn ++ [(s, arg)] := by
  dsimp [getAppArgs, getAppArgsAux]; rw [getAppArgsAux_eq]

@[irreducible] noncomputable def LamTerm.maxEVarSucc_getAppArgs :
  HList (fun (_, arg) => arg.maxEVarSucc ≤ t.maxEVarSucc) (LamTerm.getAppArgs t) :=
  LamTerm.maxEVarSucc_getAppArgsAux .nil (Nat.le_refl _)

theorem LamTerm.appFn_appArg_eqAux (args : List (LamSort × LamTerm)) (t : LamTerm) :
  LamTerm.mkAppN t args = LamTerm.mkAppN t.getAppFn (t.getAppArgsAux args) := by
  induction t generalizing args <;> try rfl
  case app s _ arg IHFn _ => apply IHFn ((s, arg) :: args)

theorem LamTerm.appFn_appArg_eq (t : LamTerm) : t = LamTerm.mkAppN t.getAppFn t.getAppArgs := appFn_appArg_eqAux [] t

def LamTerm.getAppFnN (n : Nat) (t : LamTerm) : Option LamTerm :=
  match n with
  | .zero => t
  | .succ n =>
    match t with
    | .app _ fn _ => getAppFnN n fn
    | _ => .none

theorem LamTerm.getAppFnN_add : getAppFnN (n + m) t = (getAppFnN n t).bind (getAppFnN m) := by
  induction n generalizing m t
  case zero => rw [Nat.zero_add]; rfl
  case succ n IH =>
    rw [Nat.succ_add]; cases t <;> try rfl
    case app s fn arg => dsimp [getAppFnN]; rw [IH]

theorem LamTerm.getAppFnN_succ' : getAppFnN (.succ n) t = (getAppFnN n t).bind (getAppFnN 1) := by
  rw [Nat.succ_eq_add_one]; rw [getAppFnN_add]

theorem LamTerm.maxEVarSucc_getAppFnN (heq : LamTerm.getAppFnN n t = .some t') :
  t'.maxEVarSucc ≤ t.maxEVarSucc := by
  induction n generalizing t t'
  case zero => cases heq; apply Nat.le_refl
  case succ n IH =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [getAppFnN] at heq; dsimp [maxEVarSucc]; apply Nat.le_trans _ (Nat.le_max_left _ _)
      apply IH heq

def LamTerm.getAppArgsNAux (n : Nat) (args : List (LamSort × LamTerm)) (t : LamTerm) : Option (List (LamSort × LamTerm)) :=
  match n with
  | .zero => args
  | .succ n =>
    match t with
    | .app s fn arg => getAppArgsNAux n ((s, arg) :: args) fn
    | _ => .none

theorem LamTerm.getAppArgsNAux_eq : getAppArgsNAux n args t = (getAppArgsNAux n [] t).bind (· ++ args) := by
  induction n generalizing t args
  case zero => rfl
  case succ n IH =>
    cases t <;> try rfl
    case app s fn arg =>
      dsimp [getAppArgsNAux]; rw [IH (args:=(s, arg) :: args), IH (args:=[(s, arg)])]
      cases getAppArgsNAux n [] fn <;> dsimp
      rw [List.append_assoc]; rfl

@[irreducible] def LamTerm.maxEVarSucc_getAppArgsNAux
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ m) args) (ht : t.maxEVarSucc ≤ m)
  (heq : LamTerm.getAppArgsNAux n args t = .some args') :
  HList (fun (_, arg) => arg.maxEVarSucc ≤ m) args' := by
  induction n generalizing t args args'
  case zero => cases heq; exact hs
  case succ n IH =>
    cases t <;> try cases heq
    case app s fn arg =>
      dsimp [getAppArgsNAux] at heq; dsimp [maxEVarSucc]; dsimp [maxEVarSucc] at ht
      rw [Nat.max_le] at ht; apply IH (.cons _ hs) ht.left heq; apply ht.right

def LamTerm.getAppArgsN n := getAppArgsNAux n []

@[irreducible] def LamTerm.maxEVarSucc_getAppArgsN
  (heq : LamTerm.getAppArgsN n t = .some l) :
  HList (fun (_, arg) => arg.maxEVarSucc ≤ t.maxEVarSucc) l :=
  LamTerm.maxEVarSucc_getAppArgsNAux .nil (Nat.le_refl _) heq

theorem LamTerm.getAppArgsN_zero : LamTerm.getAppArgsN 0 = fun _ => .some [] := rfl

theorem LamTerm.getAppArgsN_succ_app :
  LamTerm.getAppArgsN (.succ n) (.app s fn arg) = (getAppArgsN n fn).bind (· ++ [(s, arg)]) := by
  dsimp [getAppArgsN, getAppArgsNAux]; rw [getAppArgsNAux_eq]

def LamTerm.bvarApps (t : LamTerm) (lctx : List LamSort) (idx : Nat) :=
  match lctx with
  | .nil => t
  | s :: lctx => .app s (bvarApps t lctx (.succ idx)) (.bvar idx)

theorem LamTerm.maxEVarSucc_bvarApps : (LamTerm.bvarApps t lctx idx).maxEVarSucc = t.maxEVarSucc := by
  induction lctx generalizing idx
  case nil => rfl
  case cons ty tys IH =>
    dsimp [bvarApps, maxEVarSucc]; rw [IH]; rw [Nat.max, Nat.max_comm, Nat.max_def]; simp

theorem LamTerm.maxLooseBVarSucc_bvarApps : (LamTerm.bvarApps t lctx idx).maxLooseBVarSucc ≤ max t.maxLooseBVarSucc (lctx.length + idx) := by
  induction lctx generalizing idx
  case nil => apply Nat.le_max_left
  case cons ty tys IH =>
    dsimp [bvarApps, maxLooseBVarSucc]; rw [Nat.max, Nat.max_le]; apply And.intro
    case left =>
      apply Nat.le_trans IH; rw [Nat.max_le]; apply And.intro (Nat.le_max_left _ _)
      apply Nat.le_trans _ (Nat.le_max_right _ _); rw [Nat.succ_add]; apply Nat.le_refl
    case right =>
      apply Nat.le_trans _ (Nat.le_max_right _ _); rw [Nat.succ_add]
      rw [Nat.succ_le_succ_iff]; apply Nat.le_add_left

def LamTerm.bvarAppsRev (t : LamTerm) (lctx : List LamSort) :=
  match lctx with
  | .nil => t
  | s :: lctx => bvarAppsRev (.app s t (.bvar lctx.length)) lctx

theorem LamTerm.maxEVarSucc_bvarAppsRev : (LamTerm.bvarAppsRev t lctx).maxEVarSucc = t.maxEVarSucc := by
  induction lctx generalizing t
  case nil => rfl
  case cons ty tys IH =>
    dsimp [maxEVarSucc, bvarAppsRev]; rw [IH]
    dsimp [maxEVarSucc]; rw [Nat.max, Nat.max_zero_right]

theorem LamTerm.maxLooseBVarSucc_bvarAppsRev : (LamTerm.bvarAppsRev t lctx).maxLooseBVarSucc = max t.maxLooseBVarSucc lctx.length := by
  induction lctx generalizing t
  case nil => apply Eq.symm; apply Nat.max_zero_right
  case cons ty tys IH =>
    dsimp [bvarAppsRev, maxLooseBVarSucc]; rw [IH]
    dsimp [maxLooseBVarSucc]; rw [Nat.max, ← Nat.max_assoc]
    rw [Nat.max_eq_left (b:=tys.length)]; apply Nat.le_succ

theorem LamTerm.getAppFnN_bvarAppsRev_length_eq
  (heq : l.length = n) : getAppFnN n (bvarAppsRev t l) = t := by
  induction n generalizing l t
  case zero => cases l <;> cases heq; rfl
  case succ n IH =>
    cases l <;> cases heq
    case refl s' l =>
      rw [getAppFnN_succ']; dsimp [bvarAppsRev]
      rw [IH rfl]; rfl

def LamTerm.getForallEFBody (t : LamTerm) : LamTerm :=
  match t with
  | .app _ (.base (.forallE _)) (.lam _ body) => getForallEFBody body
  | _ => t

theorem LamTerm.maxEVarSucc_getForallEFBody : (LamTerm.getForallEFBody t).maxEVarSucc = t.maxEVarSucc := by
  generalize hsize' : t.size = n
  have hsize : t.size ≤ n := by cases hsize'; apply Nat.le_refl
  clear hsize'; induction n generalizing t
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
            dsimp [getForallEFBody, maxEVarSucc]
            rw [IH, Nat.max, Nat.max_zero_left]
            have hsize' := Nat.le_trans size_app_gt_size_arg hsize
            apply Nat.le_of_succ_le_succ (Nat.le_of_succ_le hsize')

def LamTerm.getForallEFTys (t : LamTerm) : List LamSort :=
  match t with
  | .app _ (.base (.forallE s)) (.lam _ body) => s :: getForallEFTys body
  | _ => []

def LamTerm.reprPrec (t : LamTerm) (n : Nat) :=
  let s :=
    match t with
    | .atom m      => f!"atom {m}"
    | .etom m      => f!"etom {m}"
    | .base b      => f!"base {LamBaseTerm.reprPrec b 1}"
    | .bvar m      => f!"bvar {m}"
    | .lam s t     => f!"lam {LamSort.reprPrec s 1} {LamTerm.reprPrec t 1}"
    | .app s t₁ t₂ => f!"app {LamSort.reprPrec s 1} {LamTerm.reprPrec t₁ 1} {LamTerm.reprPrec t₂ 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamTerm." ++ s
  else
    f!"(.{s})"

instance : Repr LamTerm where
  reprPrec f n := LamTerm.reprPrec f n

def LamTerm.beq : LamTerm → LamTerm → Bool
| .atom n₁, .atom n₂ => n₁.beq n₂
| .etom n₁, .etom n₂ => n₁.beq n₂
| .base b₁, .base b₂ => b₁.beq b₂
| .bvar n₁, .bvar n₂ => n₁.beq n₂
| .lam s₁ t₁, .lam s₂ t₂ => s₁.beq s₂ && t₁.beq t₂
| .app s₁ fn₁ arg₁, .app s₂ fn₂ arg₂ => s₁.beq s₂ && fn₁.beq fn₂ && arg₁.beq arg₂
| _, _ => false

instance : BEq LamTerm where
  beq := LamTerm.beq

theorem LamTerm.beq_def {x y : LamTerm} : (x == y) = x.beq y := rfl

theorem LamTerm.beq_refl {t : LamTerm} : (t.beq t = true) := by
  induction t <;> dsimp [beq] <;> try apply Nat.beq_refl
  case base b => apply LamBaseTerm.beq_refl
  case lam s t IH => rw [LamSort.beq_refl, IH]; rfl
  case app s fn arg IHFn IHArg =>
    rw [LamSort.beq_refl, IHFn, IHArg]; rfl

theorem LamTerm.eq_of_beq_eq_true {t₁ t₂ : LamTerm} : (t₁.beq t₂ = true) → t₁ = t₂ := by
  induction t₁ generalizing t₂ <;> intro H <;> cases t₂ <;> try cases H
  case atom.atom n₁ n₂ => apply congrArg _ (Nat.eq_of_beq_eq_true H)
  case etom.etom n₁ n₂ => apply congrArg _ (Nat.eq_of_beq_eq_true H)
  case base.base b₁ b₂ => apply congrArg _ (LamBaseTerm.eq_of_beq_eq_true H)
  case bvar.bvar n₁ n₂ => apply congrArg _ (Nat.eq_of_beq_eq_true H)
  case lam.lam s₁ t₁ IH s₂ t₂ =>
    dsimp [beq] at H; rw [Bool.and_eq_true] at H
    have seq := LamSort.eq_of_beq_eq_true H.left
    have teq := IH H.right
    rw [seq, teq]
  case app.app s₁ fn₁ arg₁ IHFn IHArg s₂ fn₂ arg₂ =>
    dsimp [beq] at H; rw [Bool.and_eq_true] at H; rw [Bool.and_eq_true] at H
    let seq := LamSort.eq_of_beq_eq_true H.left.left
    let fneq := IHFn H.left.right
    let argeq := IHArg H.right
    rw [seq, fneq, argeq]

instance : LawfulBEq LamTerm where
  eq_of_beq := LamTerm.eq_of_beq_eq_true
  rfl := LamTerm.beq_refl

/--
  `LamTerm.containsSort` has a nice property :
  · Let `s` be a non-function type. If a term `t` satisfies
    `LamWF ltv ⟨lctx, t, s'⟩`, and `s` occurs in neither `t`
    nor `s'`, then for all atoms occurring in `t`, `s` does
    not occur in the atom's type.
  To see this, notice that the argument type is recorded
    in `.app`, and the binder type is recorded in `.lam`
-/
def LamTerm.containsSort (t : LamTerm) (s : LamSort) :=
  match t with
  | .atom _ => false
  | .etom _ => false
  | .base b => b.containsSort s
  | .bvar _ => false
  | .lam s' body => s'.contains s || body.containsSort s
  | .app s' fn arg => s'.contains s || fn.containsSort s || arg.containsSort s

end Auto.Embedding.Lam
