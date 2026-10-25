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
structure RealInterpUnlifted (R : Type u) where
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

/--
  An arbitrary un-lifted interpretation of the constants associated with `LaterType.real`,
    used for the constants that are not recognized. `r` is an arbitrary element of `R`
-/
def RealInterpUnlifted.default (R : Type u) (r : R) : RealInterpUnlifted R :=
  ⟨r, r, fun _ _ => r, fun _ _ => r, fun _ _ => r, fun _ _ => r,
   fun _ => r, fun _ => r, fun _ => r, fun _ => r,
   fun _ _ => True, fun _ _ => True, fun _ _ => r, fun _ _ => r,
   fun _ => r, fun _ _ _ => r, fun _ => 0, fun _ => 0,
   fun _ _ => r, fun _ => r, fun _ => r⟩

/--
  The core constants `zero, one, add, neg, mul, inv, le` of `ri` form a complete ordered
    field (with `inv zero = zero`), which characterizes `Real` up to unique isomorphism
-/
structure RealInterpUnlifted.CoreSpec (ri : RealInterpUnlifted R) : Prop where
  add_assoc : ∀ x y z, ri.add (ri.add x y) z = ri.add x (ri.add y z)
  add_comm : ∀ x y, ri.add x y = ri.add y x
  zero_add : ∀ x, ri.add ri.zero x = x
  add_neg_cancel : ∀ x, ri.add x (ri.neg x) = ri.zero
  mul_assoc : ∀ x y z, ri.mul (ri.mul x y) z = ri.mul x (ri.mul y z)
  mul_comm : ∀ x y, ri.mul x y = ri.mul y x
  one_mul : ∀ x, ri.mul ri.one x = x
  mul_add : ∀ x y z, ri.mul x (ri.add y z) = ri.add (ri.mul x y) (ri.mul x z)
  zero_ne_one : ri.zero ≠ ri.one
  mul_inv_cancel : ∀ x, x ≠ ri.zero → ri.mul x (ri.inv x) = ri.one
  inv_zero : ri.inv ri.zero = ri.zero
  le_refl : ∀ x, ri.le x x
  le_trans : ∀ x y z, ri.le x y → ri.le y z → ri.le x z
  le_antisymm : ∀ x y, ri.le x y → ri.le y x → x = y
  le_total : ∀ x y, ri.le x y ∨ ri.le y x
  add_le_add_left : ∀ x y z, ri.le x y → ri.le (ri.add z x) (ri.add z y)
  mul_nonneg : ∀ x y, ri.le ri.zero x → ri.le ri.zero y → ri.le ri.zero (ri.mul x y)
  complete : ∀ S : R → Prop, (∃ x, S x) → (∃ b, ∀ x, S x → ri.le x b) →
    ∃ s, (∀ x, S x → ri.le x s) ∧ ∀ b, (∀ x, S x → ri.le x b) → ri.le s b

/-- All constants associated with `LaterType.real` -/
def RealConst.all : List RealConst :=
  [.zero, .one, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt,
   .le, .lt, .max, .min, .abs, .ofScientific, .floor, .ceil, .pow, .sqrt, .ofRat]

/--
  Characterization of each constant of `ri` other than the core constants (see `CoreSpec`).
    It determines the constant from the core constants, except that `floor` and `ceil`
    also use `ofInt` and `lt`, and `ofScientific` also uses `ofRat`. The core constants
    are characterized by `CoreSpec` instead
-/
def RealInterpUnlifted.extProp (ri : RealInterpUnlifted R) : RealConst → Prop
| .sub => ∀ x y, ri.sub x y = ri.add x (ri.neg y)
| .div => ∀ x y, ri.div x y = ri.mul x (ri.inv y)
| .ofNat => ri.ofNat 0 = ri.zero ∧ ∀ n, ri.ofNat (n + 1) = ri.add (ri.ofNat n) ri.one
| .ofInt => ri.ofInt 1 = ri.one ∧ ∀ m n, ri.ofInt (m + n) = ri.add (ri.ofInt m) (ri.ofInt n)
| .lt => ∀ x y, ri.lt x y ↔ ri.le x y ∧ ¬ ri.le y x
| .max => (∀ x y, ri.le y x → ri.max x y = x) ∧ ∀ x y, ri.le x y → ri.max x y = y
| .min => (∀ x y, ri.le x y → ri.min x y = x) ∧ ∀ x y, ri.le y x → ri.min x y = y
| .abs => (∀ x, ri.le ri.zero x → ri.abs x = x) ∧ ∀ x, ri.le x ri.zero → ri.abs x = ri.neg x
| .ofScientific => ∀ m s e, ri.ofScientific m s e = ri.ofRat (Rat.ofScientific m s e)
| .floor => (∀ x, ri.le (ri.ofInt (ri.floor x)) x) ∧ ∀ x, ri.lt x (ri.add (ri.ofInt (ri.floor x)) ri.one)
| .ceil => (∀ x, ri.le x (ri.ofInt (ri.ceil x))) ∧ ∀ x, ri.lt (ri.ofInt (ri.ceil x)) (ri.add x ri.one)
| .pow => (∀ x, ri.pow x 0 = ri.one) ∧ ∀ x n, ri.pow x (n + 1) = ri.mul (ri.pow x n) x
| .sqrt => (∀ x, ri.le ri.zero (ri.sqrt x)) ∧
  (∀ x, ri.le ri.zero x → ri.mul (ri.sqrt x) (ri.sqrt x) = x) ∧ ∀ x, ri.le x ri.zero → ri.sqrt x = ri.zero
| .ofRat => ri.ofRat 1 = ri.one ∧ (∀ p q, ri.ofRat (p + q) = ri.add (ri.ofRat p) (ri.ofRat q)) ∧
  ∀ p q, ri.ofRat (p * q) = ri.mul (ri.ofRat p) (ri.ofRat q)
| .zero | .one | .add | .neg | .mul | .inv | .le => True

/--
  Characterizations of the constants of `ri` other than the core constants (see `extProp`),
    one optional proof per constant. Each field is named after its constant
-/
structure RealInterpUnlifted.ExtSpec (ri : RealInterpUnlifted R) : Type where
  sub : Option (PLift (ri.extProp .sub))
  div : Option (PLift (ri.extProp .div))
  ofNat : Option (PLift (ri.extProp .ofNat))
  ofInt : Option (PLift (ri.extProp .ofInt))
  lt : Option (PLift (ri.extProp .lt))
  max : Option (PLift (ri.extProp .max))
  min : Option (PLift (ri.extProp .min))
  abs : Option (PLift (ri.extProp .abs))
  ofScientific : Option (PLift (ri.extProp .ofScientific))
  floor : Option (PLift (ri.extProp .floor))
  ceil : Option (PLift (ri.extProp .ceil))
  pow : Option (PLift (ri.extProp .pow))
  sqrt : Option (PLift (ri.extProp .sqrt))
  ofRat : Option (PLift (ri.extProp .ofRat))

/-- The characterization of `rc` in `e`, if available. Core constants have none -/
def RealInterpUnlifted.ExtSpec.get? {ri : RealInterpUnlifted R} (e : ri.ExtSpec) : (rc : RealConst) → Option (PLift (ri.extProp rc))
| .sub => e.sub
| .div => e.div
| .ofNat => e.ofNat
| .ofInt => e.ofInt
| .lt => e.lt
| .max => e.max
| .min => e.min
| .abs => e.abs
| .ofScientific => e.ofScientific
| .floor => e.floor
| .ceil => e.ceil
| .pow => e.pow
| .sqrt => e.sqrt
| .ofRat => e.ofRat
| .zero | .one | .add | .neg | .mul | .inv | .le => .none

/-- The constants whose characterizations are available in `e`, in the order of `RealConst.all` -/
def RealInterpUnlifted.ExtSpec.avail {ri : RealInterpUnlifted R} (e : ri.ExtSpec) : List RealConst :=
  RealConst.all.filter fun rc => (e.get? rc).isSome

theorem RealInterpUnlifted.ExtSpec.isSome_of_mem_avail {ri : RealInterpUnlifted R} {e : ri.ExtSpec} (h : rc ∈ e.avail) :
  (e.get? rc).isSome := (List.mem_filter.mp h).right

/-- No characterization is available -/
def RealInterpUnlifted.ExtSpec.none (ri : RealInterpUnlifted R) : ri.ExtSpec :=
  ⟨.none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none⟩

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

def RealInterpUnlifted.toRealInterp.{u} {R : Type} (ri : RealInterpUnlifted R) : RealInterp (GLift.{1, u} R) where
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

/--
  `ri` with the propositions and the values of builtin types un-lifted, so that the
    characterizations `CoreSpec` and `ExtSpec` apply to it
-/
def RealInterp.lower (ri : RealInterp R) : RealInterpUnlifted R where
  zero := ri.zero
  one := ri.one
  add := ri.add
  sub := ri.sub
  mul := ri.mul
  div := ri.div
  neg := ri.neg
  inv := ri.inv
  ofNat n := ri.ofNat (GLift.up n)
  ofInt n := ri.ofInt (GLift.up n)
  le x y := (ri.le x y).down
  lt x y := (ri.lt x y).down
  max := ri.max
  min := ri.min
  abs := ri.abs
  ofScientific m s e := ri.ofScientific (GLift.up m) (GLift.up s) (GLift.up e)
  floor x := (ri.floor x).down
  ceil x := (ri.ceil x).down
  pow x n := ri.pow x (GLift.up n)
  sqrt := ri.sqrt
  ofRat q := ri.ofRat (GLift.up q)

theorem RealInterpUnlifted.CoreSpec.toRealInterp {R : Type} {ri : RealInterpUnlifted R}
  (h : ri.CoreSpec) : (ri.toRealInterp.{u}).lower.CoreSpec where
  add_assoc x y z := congrArg GLift.up (h.add_assoc x.down y.down z.down)
  add_comm x y := congrArg GLift.up (h.add_comm x.down y.down)
  zero_add x := congrArg GLift.up (h.zero_add x.down)
  add_neg_cancel x := congrArg GLift.up (h.add_neg_cancel x.down)
  mul_assoc x y z := congrArg GLift.up (h.mul_assoc x.down y.down z.down)
  mul_comm x y := congrArg GLift.up (h.mul_comm x.down y.down)
  one_mul x := congrArg GLift.up (h.one_mul x.down)
  mul_add x y z := congrArg GLift.up (h.mul_add x.down y.down z.down)
  zero_ne_one heq := h.zero_ne_one (congrArg GLift.down heq)
  mul_inv_cancel x hx := congrArg GLift.up (h.mul_inv_cancel x.down fun heq => hx (congrArg GLift.up heq))
  inv_zero := congrArg GLift.up h.inv_zero
  le_refl x := h.le_refl x.down
  le_trans x y z := h.le_trans x.down y.down z.down
  le_antisymm x y hxy hyx := congrArg GLift.up (h.le_antisymm x.down y.down hxy hyx)
  le_total x y := h.le_total x.down y.down
  add_le_add_left x y z := h.add_le_add_left x.down y.down z.down
  mul_nonneg x y := h.mul_nonneg x.down y.down
  complete S hne hbdd :=
    have ⟨x, hx⟩ := hne
    have ⟨b, hb⟩ := hbdd
    have ⟨s, hs₁, hs₂⟩ := h.complete (fun r => S (GLift.up r)) ⟨x.down, hx⟩ ⟨b.down, fun r hr => hb (GLift.up r) hr⟩
    ⟨GLift.up s, fun y hy => hs₁ y.down hy, fun b' hb' => hs₂ b'.down fun r hr => hb' (GLift.up r) hr⟩

theorem RealInterpUnlifted.extProp_toRealInterp {R : Type} {ri : RealInterpUnlifted R} :
  (rc : RealConst) → ri.extProp rc → (ri.toRealInterp.{u}).lower.extProp rc
| .sub, h => fun x y => congrArg GLift.up (h x.down y.down)
| .div, h => fun x y => congrArg GLift.up (h x.down y.down)
| .ofNat, h => ⟨congrArg GLift.up h.left, fun n => congrArg GLift.up (h.right n)⟩
| .ofInt, h => ⟨congrArg GLift.up h.left, fun m n => congrArg GLift.up (h.right m n)⟩
| .lt, h => fun x y => h x.down y.down
| .max, h => ⟨fun x y hyx => congrArg GLift.up (h.left x.down y.down hyx),
              fun x y hxy => congrArg GLift.up (h.right x.down y.down hxy)⟩
| .min, h => ⟨fun x y hxy => congrArg GLift.up (h.left x.down y.down hxy),
              fun x y hyx => congrArg GLift.up (h.right x.down y.down hyx)⟩
| .abs, h => ⟨fun x hx => congrArg GLift.up (h.left x.down hx), fun x hx => congrArg GLift.up (h.right x.down hx)⟩
| .ofScientific, h => fun m s e => congrArg GLift.up (h m s e)
| .floor, h => ⟨fun x => h.left x.down, fun x => h.right x.down⟩
| .ceil, h => ⟨fun x => h.left x.down, fun x => h.right x.down⟩
| .pow, h => ⟨fun x => congrArg GLift.up (h.left x.down), fun x n => congrArg GLift.up (h.right x.down n)⟩
| .sqrt, h => ⟨fun x => h.left x.down, fun x hx => congrArg GLift.up (h.right.left x.down hx),
               fun x hx => congrArg GLift.up (h.right.right x.down hx)⟩
| .ofRat, h => ⟨congrArg GLift.up h.left, fun p q => congrArg GLift.up (h.right.left p q),
               fun p q => congrArg GLift.up (h.right.right p q)⟩
| .zero, h | .one, h | .add, h | .neg, h | .mul, h | .inv, h | .le, h => h

def RealInterpUnlifted.ExtSpec.toRealInterp {R : Type} {ri : RealInterpUnlifted R}
  (e : ri.ExtSpec) : (ri.toRealInterp.{u}).lower.ExtSpec :=
  let lift (rc : RealConst) (h? : Option (PLift (ri.extProp rc))) :=
    h?.map fun h => PLift.up (extProp_toRealInterp rc h.down)
  ⟨lift .sub e.sub, lift .div e.div, lift .ofNat e.ofNat, lift .ofInt e.ofInt, lift .lt e.lt,
   lift .max e.max, lift .min e.min, lift .abs e.abs, lift .ofScientific e.ofScientific,
   lift .floor e.floor, lift .ceil e.ceil, lift .pow e.pow, lift .sqrt e.sqrt, lift .ofRat e.ofRat⟩

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
structure ComplexInterpUnlifted (R C : Type u) where intro ::
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

/--
  An arbitrary un-lifted interpretation of the constants associated with `LaterType.complex`,
    used for the constants that are not recognized. `r` and `c` are arbitrary elements of `R` and `C`
-/
def ComplexInterpUnlifted.default (R C : Type u) (r : R) (c : C) : ComplexInterpUnlifted R C :=
  ⟨c, c, c, fun _ _ => c, fun _ _ => c, fun _ _ => c, fun _ _ => c,
   fun _ => c, fun _ => c, fun _ => c, fun _ => c,
   fun _ => c, fun _ => r, fun _ => r, fun _ _ => c,
   fun _ => r, fun _ => c, fun _ => r, fun _ _ => c, fun _ => c⟩

/-- All constants associated with `LaterType.complex` -/
def ComplexConst.all : List ComplexConst :=
  [.zero, .one, .I, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt,
   .ofReal, .re, .im, .mk, .normSq, .conj, .norm, .pow, .ofRat]

/--
  The core constants `re, im, mk` of `ci` form a bijection between `C` and `R × R`.
    Together with the characterization of `R` (see `RealInterpUnlifted.CoreSpec`)
    and of the other constants of `ci` (see `ComplexInterpUnlifted.extProp`),
    this characterizes `Complex` up to unique isomorphism
-/
structure ComplexInterpUnlifted.CoreSpec (ci : ComplexInterpUnlifted R C) : Prop where
  re_mk : ∀ x y, ci.re (ci.mk x y) = x
  im_mk : ∀ x y, ci.im (ci.mk x y) = y
  mk_re_im : ∀ z, ci.mk (ci.re z) (ci.im z) = z

/--
  Characterization of each constant of `ci` other than the core constants (see `CoreSpec`),
    by its real and imaginary parts or in terms of other constants, where `ri` interprets the
    constants of `R`. It uses the constants of `ri`, and the constants of `ci` as follows:
    `inv` and `norm` use `normSq`, `div` uses `mul` and `inv`, and `pow` uses `one` and `mul`.
    The core constants are characterized by `CoreSpec` instead
-/
def ComplexInterpUnlifted.extProp (ri : RealInterpUnlifted R) (ci : ComplexInterpUnlifted R C) :
  ComplexConst → Prop
| .zero => ci.re ci.zero = ri.zero ∧ ci.im ci.zero = ri.zero
| .one => ci.re ci.one = ri.one ∧ ci.im ci.one = ri.zero
| .I => ci.re ci.I = ri.zero ∧ ci.im ci.I = ri.one
| .add => (∀ z w, ci.re (ci.add z w) = ri.add (ci.re z) (ci.re w)) ∧
  ∀ z w, ci.im (ci.add z w) = ri.add (ci.im z) (ci.im w)
| .sub => (∀ z w, ci.re (ci.sub z w) = ri.sub (ci.re z) (ci.re w)) ∧
  ∀ z w, ci.im (ci.sub z w) = ri.sub (ci.im z) (ci.im w)
| .mul => (∀ z w, ci.re (ci.mul z w) = ri.sub (ri.mul (ci.re z) (ci.re w)) (ri.mul (ci.im z) (ci.im w))) ∧
  ∀ z w, ci.im (ci.mul z w) = ri.add (ri.mul (ci.re z) (ci.im w)) (ri.mul (ci.im z) (ci.re w))
| .div => ∀ z w, ci.div z w = ci.mul z (ci.inv w)
| .neg => (∀ z, ci.re (ci.neg z) = ri.neg (ci.re z)) ∧ ∀ z, ci.im (ci.neg z) = ri.neg (ci.im z)
| .inv => (∀ z, ci.re (ci.inv z) = ri.div (ci.re z) (ci.normSq z)) ∧
  ∀ z, ci.im (ci.inv z) = ri.div (ri.neg (ci.im z)) (ci.normSq z)
| .ofNat => (∀ n, ci.re (ci.ofNat n) = ri.ofNat n) ∧ ∀ n, ci.im (ci.ofNat n) = ri.zero
| .ofInt => (∀ n, ci.re (ci.ofInt n) = ri.ofInt n) ∧ ∀ n, ci.im (ci.ofInt n) = ri.zero
| .ofReal => (∀ x, ci.re (ci.ofReal x) = x) ∧ ∀ x, ci.im (ci.ofReal x) = ri.zero
| .normSq => ∀ z, ci.normSq z = ri.add (ri.mul (ci.re z) (ci.re z)) (ri.mul (ci.im z) (ci.im z))
| .conj => (∀ z, ci.re (ci.conj z) = ci.re z) ∧ ∀ z, ci.im (ci.conj z) = ri.neg (ci.im z)
| .norm => ∀ z, ci.norm z = ri.sqrt (ci.normSq z)
| .pow => (∀ z, ci.pow z 0 = ci.one) ∧ ∀ z n, ci.pow z (n + 1) = ci.mul (ci.pow z n) z
| .ofRat => (∀ q, ci.re (ci.ofRat q) = ri.ofRat q) ∧ ∀ q, ci.im (ci.ofRat q) = ri.zero
| .re | .im | .mk => True

/--
  Characterizations of the constants of `ci` other than the core constants (see `extProp`),
    one optional proof per constant. Each field is named after its constant
-/
structure ComplexInterpUnlifted.ExtSpec (ri : RealInterpUnlifted R) (ci : ComplexInterpUnlifted R C) : Type where
  zero : Option (PLift (extProp ri ci .zero))
  one : Option (PLift (extProp ri ci .one))
  I : Option (PLift (extProp ri ci .I))
  add : Option (PLift (extProp ri ci .add))
  sub : Option (PLift (extProp ri ci .sub))
  mul : Option (PLift (extProp ri ci .mul))
  div : Option (PLift (extProp ri ci .div))
  neg : Option (PLift (extProp ri ci .neg))
  inv : Option (PLift (extProp ri ci .inv))
  ofNat : Option (PLift (extProp ri ci .ofNat))
  ofInt : Option (PLift (extProp ri ci .ofInt))
  ofReal : Option (PLift (extProp ri ci .ofReal))
  normSq : Option (PLift (extProp ri ci .normSq))
  conj : Option (PLift (extProp ri ci .conj))
  norm : Option (PLift (extProp ri ci .norm))
  pow : Option (PLift (extProp ri ci .pow))
  ofRat : Option (PLift (extProp ri ci .ofRat))

/-- The characterization of `cc` in `e`, if available. Core constants have none -/
def ComplexInterpUnlifted.ExtSpec.get? {ri : RealInterpUnlifted R} {ci : ComplexInterpUnlifted R C}
  (e : ExtSpec ri ci) : (cc : ComplexConst) → Option (PLift (extProp ri ci cc))
| .zero => e.zero
| .one => e.one
| .I => e.I
| .add => e.add
| .sub => e.sub
| .mul => e.mul
| .div => e.div
| .neg => e.neg
| .inv => e.inv
| .ofNat => e.ofNat
| .ofInt => e.ofInt
| .ofReal => e.ofReal
| .normSq => e.normSq
| .conj => e.conj
| .norm => e.norm
| .pow => e.pow
| .ofRat => e.ofRat
| .re | .im | .mk => .none

/-- The constants whose characterizations are available in `e`, in the order of `ComplexConst.all` -/
def ComplexInterpUnlifted.ExtSpec.avail {ri : RealInterpUnlifted R} {ci : ComplexInterpUnlifted R C}
  (e : ExtSpec ri ci) : List ComplexConst :=
  ComplexConst.all.filter fun cc => (e.get? cc).isSome

theorem ComplexInterpUnlifted.ExtSpec.isSome_of_mem_avail {ri : RealInterpUnlifted R}
  {ci : ComplexInterpUnlifted R C} {e : ExtSpec ri ci} (h : cc ∈ e.avail) :
  (e.get? cc).isSome := (List.mem_filter.mp h).right

/-- No characterization is available -/
def ComplexInterpUnlifted.ExtSpec.none (ri : RealInterpUnlifted R) (ci : ComplexInterpUnlifted R C) :
  ExtSpec ri ci :=
  ⟨.none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none,
   .none, .none, .none⟩

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

def ComplexInterpUnlifted.toComplexInterp.{u} {R C : Type} (ci : ComplexInterpUnlifted R C) :
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

/--
  `ci` with the values of builtin types un-lifted, so that the characterizations
    `CoreSpec` and `ExtSpec` apply to it
-/
def ComplexInterp.lower (ci : ComplexInterp R C) : ComplexInterpUnlifted R C where
  zero := ci.zero
  one := ci.one
  I := ci.I
  add := ci.add
  sub := ci.sub
  mul := ci.mul
  div := ci.div
  neg := ci.neg
  inv := ci.inv
  ofNat n := ci.ofNat (GLift.up n)
  ofInt n := ci.ofInt (GLift.up n)
  ofReal := ci.ofReal
  re := ci.re
  im := ci.im
  mk := ci.mk
  normSq := ci.normSq
  conj := ci.conj
  norm := ci.norm
  pow z n := ci.pow z (GLift.up n)
  ofRat q := ci.ofRat (GLift.up q)

theorem ComplexInterpUnlifted.CoreSpec.toComplexInterp {R C : Type} {ci : ComplexInterpUnlifted R C}
  (h : ci.CoreSpec) : (ci.toComplexInterp.{u}).lower.CoreSpec where
  re_mk x y := congrArg GLift.up (h.re_mk x.down y.down)
  im_mk x y := congrArg GLift.up (h.im_mk x.down y.down)
  mk_re_im z := congrArg GLift.up (h.mk_re_im z.down)

theorem ComplexInterpUnlifted.extProp_toComplexInterp {R C : Type} {ri : RealInterpUnlifted R}
  {ci : ComplexInterpUnlifted R C} :
  (cc : ComplexConst) → extProp ri ci cc →
    extProp (ri.toRealInterp.{u}).lower (ci.toComplexInterp.{u}).lower cc
| .zero, h | .one, h | .I, h => ⟨congrArg GLift.up h.left, congrArg GLift.up h.right⟩
| .add, h | .sub, h | .mul, h =>
  ⟨fun z w => congrArg GLift.up (h.left z.down w.down), fun z w => congrArg GLift.up (h.right z.down w.down)⟩
| .div, h => fun z w => congrArg GLift.up (h z.down w.down)
| .neg, h | .inv, h | .ofReal, h | .conj, h =>
  ⟨fun z => congrArg GLift.up (h.left z.down), fun z => congrArg GLift.up (h.right z.down)⟩
| .ofNat, h | .ofInt, h | .ofRat, h =>
  ⟨fun n => congrArg GLift.up (h.left n), fun n => congrArg GLift.up (h.right n)⟩
| .normSq, h | .norm, h => fun z => congrArg GLift.up (h z.down)
| .pow, h => ⟨fun z => congrArg GLift.up (h.left z.down), fun z n => congrArg GLift.up (h.right z.down n)⟩
| .re, h | .im, h | .mk, h => h

def ComplexInterpUnlifted.ExtSpec.toComplexInterp {R C : Type} {ri : RealInterpUnlifted R}
  {ci : ComplexInterpUnlifted R C} (e : ExtSpec ri ci) :
  ExtSpec (ri.toRealInterp.{u}).lower (ci.toComplexInterp.{u}).lower :=
  let lift (cc : ComplexConst) (h? : Option (PLift (extProp ri ci cc))) :=
    h?.map fun h => PLift.up (extProp_toComplexInterp cc h.down)
  ⟨lift .zero e.zero, lift .one e.one, lift .I e.I, lift .add e.add, lift .sub e.sub, lift .mul e.mul,
   lift .div e.div, lift .neg e.neg, lift .inv e.inv, lift .ofNat e.ofNat, lift .ofInt e.ofInt,
   lift .ofReal e.ofReal, lift .normSq e.normSq, lift .conj e.conj, lift .norm e.norm, lift .pow e.pow,
   lift .ofRat e.ofRat⟩

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

/--
  Interpretation of the constants associated with each later-declared type, with the
    available characterizations of the constants (see `RealInterpUnlifted.CoreSpec`
    and `RealInterpUnlifted.ExtSpec`)
-/
structure LaterVal (later : LaterType → Type u) where
  real     : RealInterp (later .real)
  complex  : ComplexInterp (later .real) (later .complex)
  /-- Characterization of the core constants of `real`, if available -/
  realCore : Option (PLift real.lower.CoreSpec)
  /-- Characterizations of the other constants of `real`, each if available -/
  realExt  : real.lower.ExtSpec
  /-- Characterization of the core constants of `complex`, if available -/
  complexCore : Option (PLift complex.lower.CoreSpec)
  /-- Characterizations of the other constants of `complex`, each if available -/
  complexExt  : ComplexInterpUnlifted.ExtSpec real.lower complex.lower

/--
  The characterizations available in a `LaterVal`, as data that the checker
    can compute with (the checker cannot inspect the `LaterVal` itself)
-/
structure LaterSpecAvail where
  realCore    : Bool
  realExt     : List RealConst
  complexCore : Bool
  complexExt  : List ComplexConst
deriving Inhabited, Lean.ToExpr

def LaterVal.specAvail (lv : LaterVal later) : LaterSpecAvail :=
  ⟨lv.realCore.isSome, lv.realExt.avail, lv.complexCore.isSome, lv.complexExt.avail⟩

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
