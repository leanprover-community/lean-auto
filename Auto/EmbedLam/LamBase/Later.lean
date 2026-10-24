module

public import Auto.EmbedLam.LamBase.Sort

@[expose] public section

/-!
  Constants associated with later-declared types (`LaterType`), and their valuations.
  Unlike the constants in `LamBase/Const.lean`, the interpretations of these
  constants are not fixed: they are supplied by a `LaterVal`
-/

namespace Auto.Embedding.Lam

/-- Constants associated with `LaterType.real` -/
inductive RealConst
  | zero | one | add | sub | mul | div | neg | inv | ofNat | ofInt
  | le | lt | max | min | abs | ofScientific | floor | ceil
  | pow | sqrt | ofRat
deriving Inhabited, Hashable, Lean.ToExpr

def RealConst.reprAux : RealConst → String
| .zero => "zero"
| .one => "one"
| .add => "add"
| .sub => "sub"
| .mul => "mul"
| .div => "div"
| .neg => "neg"
| .inv => "inv"
| .ofNat => "ofNat"
| .ofInt => "ofInt"
| .le => "le"
| .lt => "lt"
| .max => "max"
| .min => "min"
| .abs => "abs"
| .ofScientific => "ofScientific"
| .floor => "floor"
| .ceil => "ceil"
| .pow => "pow"
| .sqrt => "sqrt"
| .ofRat => "ofRat"

def RealConst.reprPrec (c : RealConst) (n : Nat) : Std.Format :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.RealConst.{c.reprAux}"
  | _ + 1 => f!"(.{c.reprAux})"

instance : Repr RealConst where
  reprPrec := RealConst.reprPrec

def RealConst.toString : RealConst → String
| .zero => "0 : Real"
| .one => "1 : Real"
| .add => "+"
| .sub => "-"
| .mul => "*"
| .div => "/"
| .neg => "-"
| .inv => "inv"
| .ofNat => "rofNat"
| .ofInt => "rofInt"
| .le => "≤"
| .lt => "<"
| .max => "max"
| .min => "min"
| .abs => "abs"
| .ofScientific => "ofScientific"
| .floor => "floor"
| .ceil => "ceil"
| .pow => "^"
| .sqrt => "sqrt"
| .ofRat => "rofRat"

instance : ToString RealConst where
  toString := RealConst.toString

def RealConst.beq : RealConst → RealConst → Bool
| .zero, .zero => true
| .one, .one => true
| .add, .add => true
| .sub, .sub => true
| .mul, .mul => true
| .div, .div => true
| .neg, .neg => true
| .inv, .inv => true
| .ofNat, .ofNat => true
| .ofInt, .ofInt => true
| .le, .le => true
| .lt, .lt => true
| .max, .max => true
| .min, .min => true
| .abs, .abs => true
| .ofScientific, .ofScientific => true
| .floor, .floor => true
| .ceil, .ceil => true
| .pow, .pow => true
| .sqrt, .sqrt => true
| .ofRat, .ofRat => true
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
| .zero => .base .real
| .one => .base .real
| .add => .func (.base .real) (.func (.base .real) (.base .real))
| .sub => .func (.base .real) (.func (.base .real) (.base .real))
| .mul => .func (.base .real) (.func (.base .real) (.base .real))
| .div => .func (.base .real) (.func (.base .real) (.base .real))
| .neg => .func (.base .real) (.base .real)
| .inv => .func (.base .real) (.base .real)
| .ofNat => .func (.base .nat) (.base .real)
| .ofInt => .func (.base .int) (.base .real)
| .le => (.func (.base .real) (.func (.base .real) (.base .prop)))
| .lt => (.func (.base .real) (.func (.base .real) (.base .prop)))
| .max => (.func (.base .real) (.func (.base .real) (.base .real)))
| .min => (.func (.base .real) (.func (.base .real) (.base .real)))
| .abs => (.func (.base .real) (.base .real))
| .ofScientific => (.func (.base .nat) (.func (.base .bool) (.func (.base .nat) (.base .real))))
| .floor => (.func (.base .real) (.base .int))
| .ceil => (.func (.base .real) (.base .int))
| .pow => (.func (.base .real) (.func (.base .nat) (.base .real)))
| .sqrt => (.func (.base .real) (.base .real))
| .ofRat => (.func (.base .rat) (.base .real))

inductive RealConst.LamWF : RealConst → LamSort → Type
  | ofZero : LamWF .zero (.base .real)
  | ofOne : LamWF .one (.base .real)
  | ofAdd : LamWF .add (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofSub : LamWF .sub (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofMul : LamWF .mul (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofDiv : LamWF .div (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofNeg : LamWF .neg (.func (.base .real) (.base .real))
  | ofInv : LamWF .inv (.func (.base .real) (.base .real))
  | ofOfNat : LamWF .ofNat (.func (.base .nat) (.base .real))
  | ofOfInt : LamWF .ofInt (.func (.base .int) (.base .real))
  | ofLe : LamWF .le (.func (.base .real) (.func (.base .real) (.base .prop)))
  | ofLt : LamWF .lt (.func (.base .real) (.func (.base .real) (.base .prop)))
  | ofMax : LamWF .max (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofMin : LamWF .min (.func (.base .real) (.func (.base .real) (.base .real)))
  | ofAbs : LamWF .abs (.func (.base .real) (.base .real))
  | ofOfScientific : LamWF .ofScientific (.func (.base .nat) (.func (.base .bool) (.func (.base .nat) (.base .real))))
  | ofFloor : LamWF .floor (.func (.base .real) (.base .int))
  | ofCeil : LamWF .ceil (.func (.base .real) (.base .int))
  | ofPow : LamWF .pow (.func (.base .real) (.func (.base .nat) (.base .real)))
  | ofSqrt : LamWF .sqrt (.func (.base .real) (.base .real))
  | ofOfRat : LamWF .ofRat (.func (.base .rat) (.base .real))

theorem RealConst.LamWF.unique {c : RealConst} {s₁ s₂ : LamSort}
  (rcwf₁ : LamWF c s₁) (rcwf₂ : LamWF c s₂) : s₁ = s₂ ∧ HEq rcwf₁ rcwf₂ := by
  cases rcwf₁ <;> cases rcwf₂ <;> trivial

def RealConst.LamWF.ofRealConst : (c : RealConst) → (s : LamSort) × RealConst.LamWF c s
| .zero => ⟨_, .ofZero⟩
| .one => ⟨_, .ofOne⟩
| .add => ⟨_, .ofAdd⟩
| .sub => ⟨_, .ofSub⟩
| .mul => ⟨_, .ofMul⟩
| .div => ⟨_, .ofDiv⟩
| .neg => ⟨_, .ofNeg⟩
| .inv => ⟨_, .ofInv⟩
| .ofNat => ⟨_, .ofOfNat⟩
| .ofInt => ⟨_, .ofOfInt⟩
| .le => ⟨_, .ofLe⟩
| .lt => ⟨_, .ofLt⟩
| .max => ⟨_, .ofMax⟩
| .min => ⟨_, .ofMin⟩
| .abs => ⟨_, .ofAbs⟩
| .ofScientific => ⟨_, .ofOfScientific⟩
| .floor => ⟨_, .ofFloor⟩
| .ceil => ⟨_, .ofCeil⟩
| .pow => ⟨_, .ofPow⟩
| .sqrt => ⟨_, .ofSqrt⟩
| .ofRat => ⟨_, .ofOfRat⟩

theorem RealConst.lamWF_complete (wf : LamWF c s) : LamWF.ofRealConst c = ⟨s, wf⟩ := by
  cases wf <;> rfl

theorem RealConst.lamCheck_of_LamWF (H : LamWF c s) : c.lamCheck = s := by
  cases H <;> rfl

def RealConst.LamWF.ofCheck (H : c.lamCheck = s) : LamWF c s := by
  cases H; cases c <;> constructor

/-- Un-lifted interpretation of the constants associated with `LaterType.real` -/
structure RealInterpUnlifted (R : Type) where
  zero : R
  one : R
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  div : R → R → R
  neg : R → R
  inv : R → R
  ofNat : Nat → R
  ofInt : Int → R
  le : R → R → Prop
  lt : R → R → Prop
  max : R → R → R
  min : R → R → R
  abs : R → R
  ofScientific : Nat → Bool → Nat → R
  floor : R → Int
  ceil : R → Int
  pow : R → Nat → R
  sqrt : R → R
  ofRat : Rat → R

/-- Interpretation of the constants associated with `LaterType.real` -/
structure RealInterp (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  div : R → R → R
  neg : R → R
  inv : R → R
  ofNat : GLift.{1, u} Nat → R
  ofInt : GLift.{1, u} Int → R
  le : R → R → GLift.{1, u} Prop
  lt : R → R → GLift.{1, u} Prop
  max : R → R → R
  min : R → R → R
  abs : R → R
  ofScientific : GLift.{1, u} Nat → GLift.{1, u} Bool → GLift.{1, u} Nat → R
  floor : R → GLift.{1, u} Int
  ceil : R → GLift.{1, u} Int
  pow : R → GLift.{1, u} Nat → R
  sqrt : R → R
  ofRat : GLift.{1, u} Rat → R

def RealInterpUnlifted.toRealInterp.{u} (ri : RealInterpUnlifted R) : RealInterp (GLift.{1, u} R) where
  zero := GLift.up ri.zero
  one := GLift.up ri.one
  add x y := GLift.up (ri.add x.down y.down)
  sub x y := GLift.up (ri.sub x.down y.down)
  mul x y := GLift.up (ri.mul x.down y.down)
  div x y := GLift.up (ri.div x.down y.down)
  neg x := GLift.up (ri.neg x.down)
  inv x := GLift.up (ri.inv x.down)
  ofNat n := GLift.up (ri.ofNat n.down)
  ofInt n := GLift.up (ri.ofInt n.down)
  le x y := GLift.up (ri.le x.down y.down)
  lt x y := GLift.up (ri.lt x.down y.down)
  max x y := GLift.up (ri.max x.down y.down)
  min x y := GLift.up (ri.min x.down y.down)
  abs x := GLift.up (ri.abs x.down)
  ofScientific m s e := GLift.up (ri.ofScientific m.down s.down e.down)
  floor x := GLift.up (ri.floor x.down)
  ceil x := GLift.up (ri.ceil x.down)
  pow x n := GLift.up (ri.pow x.down n.down)
  sqrt x := GLift.up (ri.sqrt x.down)
  ofRat q := GLift.up (ri.ofRat q.down)

/-- Interpretation of the constants associated with `LaterType.real` when `Real` is interpreted as `PUnit` -/
def RealInterp.default : RealInterp PUnit.{u + 1} :=
  ⟨.unit, .unit, fun _ _ => .unit, fun _ _ => .unit, fun _ _ => .unit, fun _ _ => .unit,
   fun _ => .unit, fun _ => .unit, fun _ => .unit, fun _ => .unit,
   fun _ _ => GLift.up True, fun _ _ => GLift.up True, fun _ _ => .unit, fun _ _ => .unit,
   fun _ => .unit, fun _ _ _ => .unit, fun _ => GLift.up 0, fun _ => GLift.up 0,
   fun _ _ => .unit, fun _ => .unit, fun _ => .unit⟩

def RealConst.interp (tyVal : TyVal.{u}) (ri : RealInterp (tyVal.later .real)) :
  (c : RealConst) → c.lamCheck.interp tyVal
| .zero => ri.zero
| .one => ri.one
| .add => ri.add
| .sub => ri.sub
| .mul => ri.mul
| .div => ri.div
| .neg => ri.neg
| .inv => ri.inv
| .ofNat => ri.ofNat
| .ofInt => ri.ofInt
| .le => ri.le
| .lt => ri.lt
| .max => ri.max
| .min => ri.min
| .abs => ri.abs
| .ofScientific => ri.ofScientific
| .floor => ri.floor
| .ceil => ri.ceil
| .pow => ri.pow
| .sqrt => ri.sqrt
| .ofRat => ri.ofRat

def RealConst.LamWF.interp (tyVal : TyVal.{u}) (ri : RealInterp (tyVal.later .real)) :
  (lwf : LamWF c s) → s.interp tyVal
| .ofZero => ri.zero
| .ofOne => ri.one
| .ofAdd => ri.add
| .ofSub => ri.sub
| .ofMul => ri.mul
| .ofDiv => ri.div
| .ofNeg => ri.neg
| .ofInv => ri.inv
| .ofOfNat => ri.ofNat
| .ofOfInt => ri.ofInt
| .ofLe => ri.le
| .ofLt => ri.lt
| .ofMax => ri.max
| .ofMin => ri.min
| .ofAbs => ri.abs
| .ofOfScientific => ri.ofScientific
| .ofFloor => ri.floor
| .ofCeil => ri.ceil
| .ofPow => ri.pow
| .ofSqrt => ri.sqrt
| .ofOfRat => ri.ofRat

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

/-- Constants associated with `LaterType.complex` -/
inductive ComplexConst
  | zero | one | I | add | sub | mul | div | neg | inv | ofNat | ofInt
  | ofReal | re | im | mk
  | normSq | conj | norm | pow | ofRat
deriving Inhabited, Hashable, Lean.ToExpr

def ComplexConst.reprAux : ComplexConst → String
| .zero => "zero"
| .one => "one"
| .I => "I"
| .add => "add"
| .sub => "sub"
| .mul => "mul"
| .div => "div"
| .neg => "neg"
| .inv => "inv"
| .ofNat => "ofNat"
| .ofInt => "ofInt"
| .ofReal => "ofReal"
| .re => "re"
| .im => "im"
| .mk => "mk"
| .normSq => "normSq"
| .conj => "conj"
| .norm => "norm"
| .pow => "pow"
| .ofRat => "ofRat"

def ComplexConst.reprPrec (c : ComplexConst) (n : Nat) : Std.Format :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.ComplexConst.{c.reprAux}"
  | _ + 1 => f!"(.{c.reprAux})"

instance : Repr ComplexConst where
  reprPrec := ComplexConst.reprPrec

def ComplexConst.toString : ComplexConst → String
| .zero => "0 : Complex"
| .one => "1 : Complex"
| .I => "I"
| .add => "+"
| .sub => "-"
| .mul => "*"
| .div => "/"
| .neg => "-"
| .inv => "inv"
| .ofNat => "cofNat"
| .ofInt => "cofInt"
| .ofReal => "ofReal"
| .re => "re"
| .im => "im"
| .mk => "mk"
| .normSq => "normSq"
| .conj => "conj"
| .norm => "norm"
| .pow => "^"
| .ofRat => "cofRat"

instance : ToString ComplexConst where
  toString := ComplexConst.toString

def ComplexConst.beq : ComplexConst → ComplexConst → Bool
| .zero, .zero => true
| .one, .one => true
| .I, .I => true
| .add, .add => true
| .sub, .sub => true
| .mul, .mul => true
| .div, .div => true
| .neg, .neg => true
| .inv, .inv => true
| .ofNat, .ofNat => true
| .ofInt, .ofInt => true
| .ofReal, .ofReal => true
| .re, .re => true
| .im, .im => true
| .mk, .mk => true
| .normSq, .normSq => true
| .conj, .conj => true
| .norm, .norm => true
| .pow, .pow => true
| .ofRat, .ofRat => true
| _, _ => false

instance : BEq ComplexConst where
  beq := ComplexConst.beq

theorem ComplexConst.beq_def {x y : ComplexConst} : (x == y) = x.beq y := rfl

theorem ComplexConst.beq_refl {c : ComplexConst} : (c.beq c) = true := by
  cases c <;> rfl

theorem ComplexConst.eq_of_beq_eq_true {c₁ c₂ : ComplexConst} (H : c₁.beq c₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> first | rfl | contradiction

instance : LawfulBEq ComplexConst where
  eq_of_beq := ComplexConst.eq_of_beq_eq_true
  rfl := ComplexConst.beq_refl

def ComplexConst.lamCheck : ComplexConst → LamSort
| .zero => (.base .complex)
| .one => (.base .complex)
| .I => (.base .complex)
| .add => (.func (.base .complex) (.func (.base .complex) (.base .complex)))
| .sub => (.func (.base .complex) (.func (.base .complex) (.base .complex)))
| .mul => (.func (.base .complex) (.func (.base .complex) (.base .complex)))
| .div => (.func (.base .complex) (.func (.base .complex) (.base .complex)))
| .neg => (.func (.base .complex) (.base .complex))
| .inv => (.func (.base .complex) (.base .complex))
| .ofNat => (.func (.base .nat) (.base .complex))
| .ofInt => (.func (.base .int) (.base .complex))
| .ofReal => (.func (.base .real) (.base .complex))
| .re => (.func (.base .complex) (.base .real))
| .im => (.func (.base .complex) (.base .real))
| .mk => (.func (.base .real) (.func (.base .real) (.base .complex)))
| .normSq => (.func (.base .complex) (.base .real))
| .conj => (.func (.base .complex) (.base .complex))
| .norm => (.func (.base .complex) (.base .real))
| .pow => (.func (.base .complex) (.func (.base .nat) (.base .complex)))
| .ofRat => (.func (.base .rat) (.base .complex))

inductive ComplexConst.LamWF : ComplexConst → LamSort → Type
  | ofZero : LamWF .zero (.base .complex)
  | ofOne : LamWF .one (.base .complex)
  | ofI : LamWF .I (.base .complex)
  | ofAdd : LamWF .add (.func (.base .complex) (.func (.base .complex) (.base .complex)))
  | ofSub : LamWF .sub (.func (.base .complex) (.func (.base .complex) (.base .complex)))
  | ofMul : LamWF .mul (.func (.base .complex) (.func (.base .complex) (.base .complex)))
  | ofDiv : LamWF .div (.func (.base .complex) (.func (.base .complex) (.base .complex)))
  | ofNeg : LamWF .neg (.func (.base .complex) (.base .complex))
  | ofInv : LamWF .inv (.func (.base .complex) (.base .complex))
  | ofOfNat : LamWF .ofNat (.func (.base .nat) (.base .complex))
  | ofOfInt : LamWF .ofInt (.func (.base .int) (.base .complex))
  | ofOfReal : LamWF .ofReal (.func (.base .real) (.base .complex))
  | ofRe : LamWF .re (.func (.base .complex) (.base .real))
  | ofIm : LamWF .im (.func (.base .complex) (.base .real))
  | ofMk : LamWF .mk (.func (.base .real) (.func (.base .real) (.base .complex)))
  | ofNormSq : LamWF .normSq (.func (.base .complex) (.base .real))
  | ofConj : LamWF .conj (.func (.base .complex) (.base .complex))
  | ofNorm : LamWF .norm (.func (.base .complex) (.base .real))
  | ofPow : LamWF .pow (.func (.base .complex) (.func (.base .nat) (.base .complex)))
  | ofOfRat : LamWF .ofRat (.func (.base .rat) (.base .complex))

theorem ComplexConst.LamWF.unique {c : ComplexConst} {s₁ s₂ : LamSort}
  (ccwf₁ : LamWF c s₁) (ccwf₂ : LamWF c s₂) : s₁ = s₂ ∧ HEq ccwf₁ ccwf₂ := by
  cases ccwf₁ <;> cases ccwf₂ <;> trivial

def ComplexConst.LamWF.ofComplexConst : (c : ComplexConst) → (s : LamSort) × ComplexConst.LamWF c s
| .zero => ⟨_, .ofZero⟩
| .one => ⟨_, .ofOne⟩
| .I => ⟨_, .ofI⟩
| .add => ⟨_, .ofAdd⟩
| .sub => ⟨_, .ofSub⟩
| .mul => ⟨_, .ofMul⟩
| .div => ⟨_, .ofDiv⟩
| .neg => ⟨_, .ofNeg⟩
| .inv => ⟨_, .ofInv⟩
| .ofNat => ⟨_, .ofOfNat⟩
| .ofInt => ⟨_, .ofOfInt⟩
| .ofReal => ⟨_, .ofOfReal⟩
| .re => ⟨_, .ofRe⟩
| .im => ⟨_, .ofIm⟩
| .mk => ⟨_, .ofMk⟩
| .normSq => ⟨_, .ofNormSq⟩
| .conj => ⟨_, .ofConj⟩
| .norm => ⟨_, .ofNorm⟩
| .pow => ⟨_, .ofPow⟩
| .ofRat => ⟨_, .ofOfRat⟩

theorem ComplexConst.lamWF_complete (wf : LamWF c s) : LamWF.ofComplexConst c = ⟨s, wf⟩ := by
  cases wf <;> rfl

theorem ComplexConst.lamCheck_of_LamWF (H : LamWF c s) : c.lamCheck = s := by
  cases H <;> rfl

def ComplexConst.LamWF.ofCheck (H : c.lamCheck = s) : LamWF c s := by
  cases H; cases c <;> constructor

/-- Un-lifted interpretation of the constants associated with `LaterType.complex` -/
structure ComplexInterpUnlifted (R C : Type) where intro ::
  zero : C
  one : C
  I : C
  add : C → C → C
  sub : C → C → C
  mul : C → C → C
  div : C → C → C
  neg : C → C
  inv : C → C
  ofNat : Nat → C
  ofInt : Int → C
  ofReal : R → C
  re : C → R
  im : C → R
  mk : R → R → C
  normSq : C → R
  conj : C → C
  norm : C → R
  pow : C → Nat → C
  ofRat : Rat → C

/-- Interpretation of the constants associated with `LaterType.complex` -/
structure ComplexInterp (R C : Type u) where intro ::
  zero : C
  one : C
  I : C
  add : C → C → C
  sub : C → C → C
  mul : C → C → C
  div : C → C → C
  neg : C → C
  inv : C → C
  ofNat : GLift.{1, u} Nat → C
  ofInt : GLift.{1, u} Int → C
  ofReal : R → C
  re : C → R
  im : C → R
  mk : R → R → C
  normSq : C → R
  conj : C → C
  norm : C → R
  pow : C → GLift.{1, u} Nat → C
  ofRat : GLift.{1, u} Rat → C

def ComplexInterpUnlifted.toComplexInterp.{u} (ci : ComplexInterpUnlifted R C) :
  ComplexInterp (GLift.{1, u} R) (GLift.{1, u} C) where
  zero := GLift.up ci.zero
  one := GLift.up ci.one
  I := GLift.up ci.I
  add x y := GLift.up (ci.add x.down y.down)
  sub x y := GLift.up (ci.sub x.down y.down)
  mul x y := GLift.up (ci.mul x.down y.down)
  div x y := GLift.up (ci.div x.down y.down)
  neg x := GLift.up (ci.neg x.down)
  inv x := GLift.up (ci.inv x.down)
  ofNat n := GLift.up (ci.ofNat n.down)
  ofInt n := GLift.up (ci.ofInt n.down)
  ofReal x := GLift.up (ci.ofReal x.down)
  re z := GLift.up (ci.re z.down)
  im z := GLift.up (ci.im z.down)
  mk x y := GLift.up (ci.mk x.down y.down)
  normSq z := GLift.up (ci.normSq z.down)
  conj z := GLift.up (ci.conj z.down)
  norm z := GLift.up (ci.norm z.down)
  pow z n := GLift.up (ci.pow z.down n.down)
  ofRat q := GLift.up (ci.ofRat q.down)

/--
  Interpretation of the constants associated with `LaterType.complex` when `Complex`
    is interpreted as `PUnit`. `r` is an arbitrary element of the interpretation of `Real`
-/
def ComplexInterp.default {R : Type u} (r : R) : ComplexInterp R PUnit.{u + 1} :=
  ⟨.unit, .unit, .unit, fun _ _ => .unit, fun _ _ => .unit, fun _ _ => .unit, fun _ _ => .unit,
   fun _ => .unit, fun _ => .unit, fun _ => .unit, fun _ => .unit,
   fun _ => .unit, fun _ => r, fun _ => r, fun _ _ => .unit,
   fun _ => r, fun _ => .unit, fun _ => r, fun _ _ => .unit, fun _ => .unit⟩

def ComplexConst.interp (tyVal : TyVal.{u})
  (ci : ComplexInterp (tyVal.later .real) (tyVal.later .complex)) :
  (c : ComplexConst) → c.lamCheck.interp tyVal
| .zero => ci.zero
| .one => ci.one
| .I => ci.I
| .add => ci.add
| .sub => ci.sub
| .mul => ci.mul
| .div => ci.div
| .neg => ci.neg
| .inv => ci.inv
| .ofNat => ci.ofNat
| .ofInt => ci.ofInt
| .ofReal => ci.ofReal
| .re => ci.re
| .im => ci.im
| .mk => ci.mk
| .normSq => ci.normSq
| .conj => ci.conj
| .norm => ci.norm
| .pow => ci.pow
| .ofRat => ci.ofRat

def ComplexConst.LamWF.interp (tyVal : TyVal.{u})
  (ci : ComplexInterp (tyVal.later .real) (tyVal.later .complex)) :
  (lwf : LamWF c s) → s.interp tyVal
| .ofZero => ci.zero
| .ofOne => ci.one
| .ofI => ci.I
| .ofAdd => ci.add
| .ofSub => ci.sub
| .ofMul => ci.mul
| .ofDiv => ci.div
| .ofNeg => ci.neg
| .ofInv => ci.inv
| .ofOfNat => ci.ofNat
| .ofOfInt => ci.ofInt
| .ofOfReal => ci.ofReal
| .ofRe => ci.re
| .ofIm => ci.im
| .ofMk => ci.mk
| .ofNormSq => ci.normSq
| .ofConj => ci.conj
| .ofNorm => ci.norm
| .ofPow => ci.pow
| .ofOfRat => ci.ofRat

theorem ComplexConst.interp_equiv (tyVal : TyVal.{u})
  (ci : ComplexInterp (tyVal.later .real) (tyVal.later .complex))
  (ccwf : LamWF c s) : HEq (LamWF.interp tyVal ci ccwf) (interp tyVal ci c) := by
  cases ccwf <;> rfl

theorem ComplexConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : TyVal.{u})
  (ci₁ : ComplexInterp (tyVal₁.later .real) (tyVal₁.later .complex))
  (ci₂ : ComplexInterp (tyVal₂.later .real) (tyVal₂.later .complex))
  (ccwf₁ : LamWF c₁ s₁) (ccwf₂ : LamWF c₂ s₂)
  (HBeq : c₁ = c₂) (hTyVal : tyVal₁ = tyVal₂) (hCi : HEq ci₁ ci₂) :
  HEq (ccwf₁.interp tyVal₁ ci₁) (ccwf₂.interp tyVal₂ ci₂) := by
  cases HBeq; cases hTyVal; cases hCi
  rcases ComplexConst.LamWF.unique ccwf₁ ccwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

/-- Constants associated with later-declared types, one branch for each `LaterType` -/
inductive LaterConst
  | real    : RealConst → LaterConst
  | complex : ComplexConst → LaterConst
deriving Inhabited, Hashable, Lean.ToExpr

def LaterConst.reprPrec (l : LaterConst) (n : Nat) :=
  let s :=
    match l with
    | .real rc => f!"real {RealConst.reprPrec rc 1}"
    | .complex cc => f!"complex {ComplexConst.reprPrec cc 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LaterConst." ++ s
  else
    f!"(.{s})"

instance : Repr LaterConst where
  reprPrec := LaterConst.reprPrec

def LaterConst.toString : LaterConst → String
| .real rc => s!"{rc}"
| .complex cc => s!"{cc}"

instance : ToString LaterConst where
  toString := LaterConst.toString

def LaterConst.beq : LaterConst → LaterConst → Bool
| .real rc₁,    .real rc₂    => rc₁.beq rc₂
| .complex cc₁, .complex cc₂ => cc₁.beq cc₂
| _,            _            => false

instance : BEq LaterConst where
  beq := LaterConst.beq

theorem LaterConst.beq_def {x y : LaterConst} : (x == y) = x.beq y := rfl

theorem LaterConst.beq_refl {l : LaterConst} : (l.beq l) = true := by
  cases l
  case real => apply RealConst.beq_refl
  case complex => apply ComplexConst.beq_refl

theorem LaterConst.eq_of_beq_eq_true {l₁ l₂ : LaterConst} (H : l₁.beq l₂) : l₁ = l₂ := by
  cases l₁ <;> cases l₂ <;> first
    | contradiction | rw [RealConst.eq_of_beq_eq_true H] | rw [ComplexConst.eq_of_beq_eq_true H]

instance : LawfulBEq LaterConst where
  eq_of_beq := LaterConst.eq_of_beq_eq_true
  rfl := LaterConst.beq_refl

def LaterConst.lamCheck : LaterConst → LamSort
| .real rc => rc.lamCheck
| .complex cc => cc.lamCheck

inductive LaterConst.LamWF : LaterConst → LamSort → Type
  | ofReal    : (rcwf : RealConst.LamWF rc s) → LamWF (.real rc) s
  | ofComplex : (ccwf : ComplexConst.LamWF cc s) → LamWF (.complex cc) s

theorem LaterConst.LamWF.unique {l : LaterConst} {s₁ s₂ : LamSort}
  (lcwf₁ : LamWF l s₁) (lcwf₂ : LamWF l s₂) : s₁ = s₂ ∧ HEq lcwf₁ lcwf₂ := by
  cases lcwf₁ <;> cases lcwf₂
  case ofReal.ofReal wf₁ wf₂ =>
    rcases RealConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofComplex.ofComplex wf₁ wf₂ =>
    rcases ComplexConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial

def LaterConst.LamWF.ofLaterConst : (l : LaterConst) → (s : LamSort) × LaterConst.LamWF l s
| .real rc => have ⟨s, wf⟩ := RealConst.LamWF.ofRealConst rc; ⟨s, .ofReal wf⟩
| .complex cc => have ⟨s, wf⟩ := ComplexConst.LamWF.ofComplexConst cc; ⟨s, .ofComplex wf⟩

theorem LaterConst.lamWF_complete (wf : LamWF l s) : LamWF.ofLaterConst l = ⟨s, wf⟩ := by
  cases wf
  case ofReal rc wf => dsimp [LamWF.ofLaterConst]; rw [RealConst.lamWF_complete wf]
  case ofComplex cc wf => dsimp [LamWF.ofLaterConst]; rw [ComplexConst.lamWF_complete wf]

theorem LaterConst.lamCheck_of_LamWF (H : LamWF l s) : l.lamCheck = s := by
  cases H
  case ofReal rc wf => apply RealConst.lamCheck_of_LamWF wf
  case ofComplex cc wf => apply ComplexConst.lamCheck_of_LamWF wf

def LaterConst.LamWF.ofCheck (H : l.lamCheck = s) : LamWF l s := by
  cases H; cases l
  case real rc => apply LamWF.ofReal; apply RealConst.LamWF.ofCheck; rfl
  case complex cc => apply LamWF.ofComplex; apply ComplexConst.LamWF.ofCheck; rfl

/-- Interpretation of later-declared types (`TyVal.later`), given the interpretation of each of them -/
@[reducible] def LaterType.interp (real complex : Type u) : LaterType → Type u
| .real    => real
| .complex => complex

/-- Interpretation of the constants associated with each later-declared type -/
structure LaterVal (later : LaterType → Type u) where
  real    : RealInterp (later .real)
  complex : ComplexInterp (later .real) (later .complex)

def LaterConst.interp (tyVal : TyVal.{u}) (lv : LaterVal tyVal.later) :
  (l : LaterConst) → l.lamCheck.interp tyVal
| .real rc => rc.interp tyVal lv.real
| .complex cc => cc.interp tyVal lv.complex

def LaterConst.LamWF.interp (tyVal : TyVal.{u}) (lv : LaterVal tyVal.later) :
  (lwf : LamWF l s) → s.interp tyVal
| .ofReal rcwf => rcwf.interp tyVal lv.real
| .ofComplex ccwf => ccwf.interp tyVal lv.complex

theorem LaterConst.interp_equiv (tyVal : TyVal.{u}) (lv : LaterVal tyVal.later)
  (lcwf : LamWF l s) : HEq (LamWF.interp tyVal lv lcwf) (interp tyVal lv l) := by
  cases lcwf
  case ofReal rc wf => apply RealConst.interp_equiv
  case ofComplex cc wf => apply ComplexConst.interp_equiv

theorem LaterConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : TyVal.{u})
  (lv₁ : LaterVal tyVal₁.later) (lv₂ : LaterVal tyVal₂.later)
  (lcwf₁ : LamWF l₁ s₁) (lcwf₂ : LamWF l₂ s₂)
  (HBeq : l₁ = l₂) (hTyVal : tyVal₁ = tyVal₂) (hLv : HEq lv₁ lv₂) :
  HEq (lcwf₁.interp tyVal₁ lv₁) (lcwf₂.interp tyVal₂ lv₂) := by
  cases HBeq; cases hTyVal; cases hLv
  rcases LaterConst.LamWF.unique lcwf₁ lcwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

end Auto.Embedding.Lam
