module

public import Auto.Embedding.LamBase.Sort

@[expose] public section

/-!
  Constants associated with later-declared types (`LaterType`), and their valuations.
  Unlike the constants in `LamBase/Const.lean`, the interpretations of these
  constants are not fixed: they are supplied by a `LaterVal`
-/

namespace Auto.Embedding.Lam

/-- Constants associated with `LaterType.real` -/
inductive RealConst
  | add | sub | mul | div
deriving Inhabited, Hashable, Lean.ToExpr

def RealConst.reprAux : RealConst → String
| .add => "add"
| .sub => "sub"
| .mul => "mul"
| .div => "div"

def RealConst.reprPrec (c : RealConst) (n : Nat) : Std.Format :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.RealConst.{c.reprAux}"
  | _ + 1 => f!"(.{c.reprAux})"

instance : Repr RealConst where
  reprPrec := RealConst.reprPrec

def RealConst.toString : RealConst → String
| .add => "+"
| .sub => "-"
| .mul => "*"
| .div => "/"

instance : ToString RealConst where
  toString := RealConst.toString

def RealConst.beq : RealConst → RealConst → Bool
| .add, .add => true
| .sub, .sub => true
| .mul, .mul => true
| .div, .div => true
| _,    _    => false

instance : BEq RealConst where
  beq := RealConst.beq

theorem RealConst.beq_def {x y : RealConst} : (x == y) = x.beq y := rfl

theorem RealConst.beq_refl {c : RealConst} : (c.beq c) = true := by
  cases c <;> rfl

theorem RealConst.eq_of_beq_eq_true {c₁ c₂ : RealConst} (H : c₁.beq c₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> first | rfl | contradiction

instance : LawfulBEq RealConst where
  eq_of_beq := RealConst.eq_of_beq_eq_true
  rfl := RealConst.beq_refl

def RealConst.lamCheck : RealConst → LamSort
| .add => .func (.base .real) (.func (.base .real) (.base .real))
| .sub => .func (.base .real) (.func (.base .real) (.base .real))
| .mul => .func (.base .real) (.func (.base .real) (.base .real))
| .div => .func (.base .real) (.func (.base .real) (.base .real))

inductive RealConst.LamWF : RealConst → LamSort → Type
  | ofAdd : LamWF .add (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofSub : LamWF .sub (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofMul : LamWF .mul (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofDiv : LamWF .div (.func (.base .real) (.func (.base .real) (.base .real)))

theorem RealConst.LamWF.unique {c : RealConst} {s₁ s₂ : LamSort}
  (rcwf₁ : LamWF c s₁) (rcwf₂ : LamWF c s₂) : s₁ = s₂ ∧ HEq rcwf₁ rcwf₂ := by
  cases rcwf₁ <;> cases rcwf₂ <;> trivial

def RealConst.LamWF.ofRealConst : (c : RealConst) → (s : LamSort) × RealConst.LamWF c s
| .add => ⟨_, .ofAdd⟩
| .sub => ⟨_, .ofSub⟩
| .mul => ⟨_, .ofMul⟩
| .div => ⟨_, .ofDiv⟩

theorem RealConst.lamWF_complete (wf : LamWF c s) : LamWF.ofRealConst c = ⟨s, wf⟩ := by
  cases wf <;> rfl

theorem RealConst.lamCheck_of_LamWF (H : LamWF c s) : c.lamCheck = s := by
  cases H <;> rfl

def RealConst.LamWF.ofCheck (H : c.lamCheck = s) : LamWF c s := by
  cases H; cases c <;> constructor

/-- Un-lifted interpretation of the constants associated with `LaterType.real` -/
structure RealInterpUnlifted (R : Type) where
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  div : R → R → R

/-- Interpretation of the constants associated with `LaterType.real` -/
structure RealInterp (R : Type u) where
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  div : R → R → R

def RealInterpUnlifted.toRealInterp.{u} (ri : RealInterpUnlifted R) : RealInterp (GLift.{1, u} R) where
  add x y := GLift.up (ri.add x.down y.down)
  sub x y := GLift.up (ri.sub x.down y.down)
  mul x y := GLift.up (ri.mul x.down y.down)
  div x y := GLift.up (ri.div x.down y.down)

def RealInterp.default (R : Type u) : RealInterp R :=
  ⟨fun x _ => x, fun x _ => x, fun x _ => x, fun x _ => x⟩

def RealConst.interp (tyVal : TyVal.{u}) (ri : RealInterp (tyVal.later .real)) :
  (c : RealConst) → c.lamCheck.interp tyVal
| .add => ri.add
| .sub => ri.sub
| .mul => ri.mul
| .div => ri.div

def RealConst.LamWF.interp (tyVal : TyVal.{u}) (ri : RealInterp (tyVal.later .real)) :
  (lwf : LamWF c s) → s.interp tyVal
| .ofAdd => ri.add
| .ofSub => ri.sub
| .ofMul => ri.mul
| .ofDiv => ri.div

theorem RealConst.interp_equiv (tyVal : TyVal.{u}) (ri : RealInterp (tyVal.later .real))
  (rcwf : LamWF c s) : HEq (LamWF.interp tyVal ri rcwf) (interp tyVal ri c) := by
  cases rcwf <;> rfl

theorem RealConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : TyVal.{u})
  (ri₁ : RealInterp (tyVal₁.later .real)) (ri₂ : RealInterp (tyVal₂.later .real))
  (rcwf₁ : LamWF c₁ s₁) (rcwf₂ : LamWF c₂ s₂)
  (HBeq : c₁ = c₂) (hTyVal : tyVal₁ = tyVal₂) (hRi : HEq ri₁ ri₂) :
  HEq (rcwf₁.interp tyVal₁ ri₁) (rcwf₂.interp tyVal₂ ri₂) := by
  cases HBeq; cases hTyVal; cases hRi
  rcases RealConst.LamWF.unique rcwf₁ rcwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

/-- Constants associated with later-declared types, one branch for each `LaterType` -/
inductive LaterConst
  | real : RealConst → LaterConst
deriving Inhabited, Hashable, Lean.ToExpr

def LaterConst.reprPrec (l : LaterConst) (n : Nat) :=
  let s :=
    match l with
    | .real rc => f!"real {RealConst.reprPrec rc 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LaterConst." ++ s
  else
    f!"(.{s})"

instance : Repr LaterConst where
  reprPrec := LaterConst.reprPrec

def LaterConst.toString : LaterConst → String
| .real rc => s!"{rc}"

instance : ToString LaterConst where
  toString := LaterConst.toString

def LaterConst.beq : LaterConst → LaterConst → Bool
| .real rc₁, .real rc₂ => rc₁.beq rc₂

instance : BEq LaterConst where
  beq := LaterConst.beq

theorem LaterConst.beq_def {x y : LaterConst} : (x == y) = x.beq y := rfl

theorem LaterConst.beq_refl {l : LaterConst} : (l.beq l) = true := by
  cases l; apply RealConst.beq_refl

theorem LaterConst.eq_of_beq_eq_true {l₁ l₂ : LaterConst} (H : l₁.beq l₂) : l₁ = l₂ := by
  cases l₁ <;> cases l₂ <;> first | contradiction | rw [RealConst.eq_of_beq_eq_true H]

instance : LawfulBEq LaterConst where
  eq_of_beq := LaterConst.eq_of_beq_eq_true
  rfl := LaterConst.beq_refl

def LaterConst.lamCheck : LaterConst → LamSort
| .real rc => rc.lamCheck

inductive LaterConst.LamWF : LaterConst → LamSort → Type
  | ofReal : (rcwf : RealConst.LamWF rc s) → LamWF (.real rc) s

theorem LaterConst.LamWF.unique {l : LaterConst} {s₁ s₂ : LamSort}
  (lcwf₁ : LamWF l s₁) (lcwf₂ : LamWF l s₂) : s₁ = s₂ ∧ HEq lcwf₁ lcwf₂ := by
  cases lcwf₁ <;> cases lcwf₂
  case ofReal.ofReal wf₁ wf₂ =>
    rcases RealConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial

def LaterConst.LamWF.ofLaterConst : (l : LaterConst) → (s : LamSort) × LaterConst.LamWF l s
| .real rc => have ⟨s, wf⟩ := RealConst.LamWF.ofRealConst rc; ⟨s, .ofReal wf⟩

theorem LaterConst.lamWF_complete (wf : LamWF l s) : LamWF.ofLaterConst l = ⟨s, wf⟩ := by
  cases wf
  case ofReal rc wf => dsimp [LamWF.ofLaterConst]; rw [RealConst.lamWF_complete wf]

theorem LaterConst.lamCheck_of_LamWF (H : LamWF l s) : l.lamCheck = s := by
  cases H
  case ofReal rc wf => apply RealConst.lamCheck_of_LamWF wf

def LaterConst.LamWF.ofCheck (H : l.lamCheck = s) : LamWF l s := by
  cases H; cases l
  case real rc => apply LamWF.ofReal; apply RealConst.LamWF.ofCheck; rfl

/-- Interpretation of the constants associated with each later-declared type -/
structure LaterVal (later : LaterType → Type u) where
  real : RealInterp (later .real)

def LaterVal.default (later : LaterType → Type u) : LaterVal later :=
  ⟨RealInterp.default _⟩

def LaterConst.interp (tyVal : TyVal.{u}) (lv : LaterVal tyVal.later) :
  (l : LaterConst) → l.lamCheck.interp tyVal
| .real rc => rc.interp tyVal lv.real

def LaterConst.LamWF.interp (tyVal : TyVal.{u}) (lv : LaterVal tyVal.later) :
  (lwf : LamWF l s) → s.interp tyVal
| .ofReal rcwf => rcwf.interp tyVal lv.real

theorem LaterConst.interp_equiv (tyVal : TyVal.{u}) (lv : LaterVal tyVal.later)
  (lcwf : LamWF l s) : HEq (LamWF.interp tyVal lv lcwf) (interp tyVal lv l) := by
  cases lcwf
  case ofReal rc wf => apply RealConst.interp_equiv

theorem LaterConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : TyVal.{u})
  (lv₁ : LaterVal tyVal₁.later) (lv₂ : LaterVal tyVal₂.later)
  (lcwf₁ : LamWF l₁ s₁) (lcwf₂ : LamWF l₂ s₂)
  (HBeq : l₁ = l₂) (hTyVal : tyVal₁ = tyVal₂) (hLv : HEq lv₁ lv₂) :
  HEq (lcwf₁.interp tyVal₁ lv₁) (lcwf₂.interp tyVal₂ lv₂) := by
  cases HBeq; cases hTyVal; cases hLv
  rcases LaterConst.LamWF.unique lcwf₁ lcwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

end Auto.Embedding.Lam
