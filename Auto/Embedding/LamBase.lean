import Auto.Embedding.Lift
import Auto.Embedding.LCtx
import Auto.Util.ExprExtra
import Auto.Lib.HEqExtra
import Std.Data.List.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec.Defs
import Mathlib.Data.Int.Basic

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.Embedding.Lam

-- Interpreted sorts
inductive LamBaseSort
  | prop : LamBaseSort             -- GLift `prop`
  | int  : LamBaseSort             -- GLift `int`
  | real : LamBaseSort             -- GLift `real`
  | bv   : (n : Nat) → LamBaseSort -- GLift `bv n`
deriving BEq, Hashable, Inhabited

def LamBaseSort.reprPrec (b : LamBaseSort) (n : Nat) :=
  let str :=
    match b with
    | .prop => ".prop"
    | .int  => ".int"
    | .real => ".real"
    | .bv n => s!".bv {n}"
  if n == 0 then
    f!"LamBaseSort." ++ str
  else
    f!"({str})"

instance : Repr LamBaseSort where
  reprPrec s n := s.reprPrec n

def LamBaseSort.beq : LamBaseSort → LamBaseSort → Bool
| .prop, .prop => true
| .int,  .int  => true
| .real, .real => true
| .bv n, .bv m => n == m
| _,     _     => false

-- A version of `Nat.beq_refl` that reduces to `Eq.refl`
private def Nat.beq_refl' : (a : Nat) → (a.beq a) = true
| 0 => rfl
| n + 1 => Nat.beq_refl' n

def LamBaseSort.beq_refl : (b : LamBaseSort) → (b.beq b) = true
| .prop => rfl
| .int  => rfl
| .real => rfl
| .bv n => Nat.beq_refl' n

def LamBaseSort.beq_eq (b₁ b₂ : LamBaseSort) : b₁.beq b₂ → b₁ = b₂ :=
  match b₁, b₂ with
  | .prop, .prop => fun _ => rfl
  | .int,  .int  => fun _ => rfl
  | .real, .real => fun _ => rfl
  | .bv n, .bv m => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .prop, .int  => fun H => by cases H
  | .prop, .real => fun H => by cases H
  | .prop, .bv m => fun H => by cases H
  | .int,  .prop => fun H => by cases H
  | .int,  .real => fun H => by cases H
  | .int,  .bv m => fun H => by cases H
  | .real, .prop => fun H => by cases H
  | .real, .int  => fun H => by cases H
  | .real, .bv m => fun H => by cases H
  | .bv n, .prop => fun H => by cases H
  | .bv n, .int  => fun H => by cases H
  | .bv n, .real => fun H => by cases H

@[reducible] def LamBaseSort.interp.{u} : LamBaseSort → Type u
| .prop   => GLift Prop
| .int    => GLift Int
| .real   => GLift Real
| .bv n   => GLift (Bitvec n)

inductive LamSort
| atom : Nat → LamSort
| base : LamBaseSort → LamSort
| func : LamSort → LamSort → LamSort
deriving Inhabited, Hashable

def LamSort.reprPrec (s : LamSort) (n : Nat) :=
  let str :=
    match s with
    | .atom n     => f!".atom {n}"
    | .base b     => f!".base {LamBaseSort.reprPrec b 1}"
    | .func s1 s2 => f!".func {LamSort.reprPrec s1 1} {LamSort.reprPrec s2 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamSort" ++ str
  else
    f!"({str})"

instance : Repr LamSort where
  reprPrec s n := s.reprPrec n 

def LamSort.beq : LamSort → LamSort → Bool
| .atom m,     .atom n     => m == n
| .base m,     .base n     => m.beq n
| .func m₁ n₁, .func m₂ n₂ => LamSort.beq m₁ m₂ && LamSort.beq n₁ n₂
| _,           _           => false

instance : BEq LamSort where
  beq := LamSort.beq

def LamSort.beq_refl : (a : LamSort) → (a.beq a) = true
| .atom m => Nat.beq_refl' m
| .base b => LamBaseSort.beq_refl b
| .func m₁ n₁ => by rw [beq]; rw [LamSort.beq_refl m₁]; rw [LamSort.beq_refl n₁]; rfl

def LamSort.beq_eq (a b : LamSort) : (a.beq b = true) → a = b :=
  match a, b with
  | .atom m,     .atom n     => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .base m,     .base n     => fun H => LamBaseSort.beq_eq _ _ H ▸ rfl
  | .func m₁ n₁, .func m₂ n₂ => fun H => by
    unfold beq at H; revert H;
    match h₁ : beq m₁ m₂, h₂ : beq n₁ n₂ with
    | true,  true  =>
      intro _;
      let eq₁ := LamSort.beq_eq _ _ h₁
      let eq₂ := LamSort.beq_eq _ _ h₂
      rw [eq₁, eq₂]
    | true,  false => intro H; cases H
    | false, _     => intro H; cases H
  | .atom m,     .base n     => fun H => by cases H
  | .atom m,     .func m₁ n₁ => fun H => by cases H
  | .base m,     .atom n     => fun H => by cases H
  | .base m,     .func m₁ n₁ => fun H => by cases H
  | .func m₁ n₁, .atom n     => fun H => by cases H
  | .func m₁ n₁, .base n     => fun H => by cases H

theorem LamSort.beq_eq_true_eq (a b : LamSort) : (a.beq b = true) = (a = b) :=
  propext <| Iff.intro (beq_eq a b) (fun h => by subst h; apply beq_refl)

@[reducible] def LamSort.interp.{u} (val : Nat → Type u) : LamSort → Type u
| .atom n => val n
| .base b => b.interp
| .func dom cod => interp val dom → interp val cod

-- Representable real numbers
inductive CstrReal
  | zero    : CstrReal
  | one     : CstrReal
deriving Inhabited, Hashable

def CstrReal.reprPrec (c : CstrReal) (n : Nat) :=
  let s :=
    match c with
    | .zero => f!".zero"
    | .one  => f!".one"
  if n == 0 then
    f!"Auto.Embedding.Lam.CstrReal." ++ s
  else
    f!"({s})"

instance : Repr CstrReal where
  reprPrec := CstrReal.reprPrec

def CstrReal.interp : (c : CstrReal) → Real
| zero => 0
| one  => 1

-- Interpreted constants
-- Note that `eq`, `forallE`, `existE` have `(eq/forall/exist)(Val/LamVal)`
--   associated with them. During proof reconstruction, we should collect
--   the sort arguments of all `eq, forallE, existE` that occurs in the
--   proof into `eqLamVal, forallLamVal` and `existLamVal`, respectively.
-- For `eqVal, forallVal` and `existVal`, we need to use `EqLift.ofEqLift`,
--   `ForallLift.ofForallLift` and `ExistLift.ofExistLift` to construct
--   `EqLift/ForallLift/ExistLift` structures for the assumptions.
--   For any other `eq, forall, exist` that occurs in the proof, use
--   `(EqLift/ForallLift/ExistLift).default` instead. The idea is that
--   we want the interpretation of reified assumptions to be definitionally
--   equal to the assumption (or `GLift.up` applied to the assumption, to
--   be precise), so we'll have to use the specially designed
--   `of(Eq/Forall/Exist)Lift` function. However, at the end of the proof,
--   we'll have a `LamTerm.base .falseE`, no `=, ∀, ∃` left,
--   so whatever `(Eq/Forall/Exist)Lift` structure are within the
--   `(eq/forall/lam)Val`, the final result will always interpret to
--   `GLift.up False`.
-- The correctness theorem of the checker existentially quantify over
--   over `eqVal, forallVal` and `lamVal` to reduce kernel overhead
--   while performing proof checking, but the speedup would probably
--   be insignificant.
inductive LamBaseTerm
  | trueE    : LamBaseTerm -- Propositional `true`
  | falseE   : LamBaseTerm -- Propositional `false`
  | not      : LamBaseTerm -- Propositional `not`
  | and      : LamBaseTerm -- Propositional `and`
  | or       : LamBaseTerm -- Propositional `or`
  | imp      : LamBaseTerm -- Propositional `imp`
  | iff      : LamBaseTerm -- Propositional `iff`
  | intVal   : Int → LamBaseTerm
  | realVal  : CstrReal → LamBaseTerm
  | bvVal    : List Bool → LamBaseTerm
  -- Versions of `eq, ∀, ∃` when we're importing external facts
  -- Note that the [import versions] of `eq, ∀, ∃` should only be used when
  --   we're importing external facts. When facts are imported, we call
  --   `resolveImport` on them and these [import versions] are turned into
  --   [non-import versions]
  | eqI      : Nat → LamBaseTerm
  | forallEI : Nat → LamBaseTerm
  | existEI  : Nat → LamBaseTerm
  -- Non-import versions of `eq, ∀, ∃`
  | eq       : LamSort → LamBaseTerm
  | forallE  : LamSort → LamBaseTerm
  | existE   : LamSort → LamBaseTerm
deriving Inhabited, Hashable

def LamBaseTerm.reprPrec (l : LamBaseTerm) (n : Nat) :=
  let s :=
    match l with
    | .trueE      => f!".trueE"
    | .falseE     => f!".falseE"
    | .not        => f!".not"
    | .and        => f!".and"
    | .or         => f!".or"
    | .imp        => f!".imp"
    | .iff        => f!".iff"
    | .intVal n   => f!".intVal {n}"
    | .realVal cr => f!".realVal {CstrReal.reprPrec cr 1}"
    | .bvVal l    => f!".bvVal {l}"
    | .eqI n      => f!".eqI {n}"
    | .forallEI n => f!".forallEI {n}"
    | .existEI n  => f!".existEI {n}"
    | .eq s       => f!".eq {LamSort.reprPrec s 1}"
    | .forallE s  => f!".forallE {LamSort.reprPrec s 1}}"
    | .existE s   => f!".existE {LamSort.reprPrec s 1}}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamBaseTerm" ++ s
  else
    f!"({s})"

instance : Repr LamBaseTerm where
  reprPrec := LamBaseTerm.reprPrec

structure LamTyVal where
  lamVarTy     : Nat → LamSort
  eqLamVal     : Nat → LamSort
  forallLamVal : Nat → LamSort
  existLamVal  : Nat → LamSort

instance : Inhabited LamTyVal where
  default := let func := fun _ => .atom 0; ⟨func, func, func, func⟩

def LamBaseTerm.lamCheck (ltv : LamTyVal) : LamBaseTerm → LamSort
| .trueE      => .base .prop
| .falseE     => .base .prop
| .not        => .func (.base .prop) (.base .prop)
| .and        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .or         => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .imp        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .iff        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .intVal _   => .base .int
| .realVal _  => .base .real
| .bvVal ls   => .base (.bv ls.length)
| .eqI n      =>
  let s := ltv.eqLamVal n
  .func s (.func s (.base .prop))
| .forallEI n =>
  let s := ltv.forallLamVal n
  .func (.func s (.base .prop)) (.base .prop)
| .existEI n  =>
  let s := ltv.existLamVal n
  .func (.func s (.base .prop)) (.base .prop)
| .eq s       => .func s (.func s (.base .prop))
| .forallE s  => .func (.func s (.base .prop)) (.base .prop)
| .existE s   => .func (.func s (.base .prop)) (.base .prop)

inductive LamBaseTerm.LamWF (ltv : LamTyVal) : LamBaseTerm → LamSort → Type
  | ofTrueE      : LamWF ltv .trueE (.base .prop)
  | ofFalseE     : LamWF ltv .falseE (.base .prop)
  | ofNot        : LamWF ltv .not (.func (.base .prop) (.base .prop))
  | ofAnd        : LamWF ltv .and (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofOr         : LamWF ltv .or (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofImp        : LamWF ltv .imp (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofIff        : LamWF ltv .iff (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofIntVal n   : LamWF ltv (.intVal n) (.base .int)
  | ofRealVal cr : LamWF ltv (.realVal cr) (.base .real)
  | ofBvVal ls   : LamWF ltv (.bvVal ls) (.base (.bv ls.length))
  | ofEqI n      : LamWF ltv (.eqI n) (.func (ltv.eqLamVal n) (.func (ltv.eqLamVal n) (.base .prop)))
  | ofForallEI n : LamWF ltv (.forallEI n) (.func (.func (ltv.forallLamVal n) (.base .prop)) (.base .prop))
  | ofExistEI n  : LamWF ltv (.existEI n) (.func (.func (ltv.existLamVal n) (.base .prop)) (.base .prop))
  | ofEq s       : LamWF ltv (.eq s) (.func s (.func s (.base .prop)))
  | ofForallE s  : LamWF ltv (.forallE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofExistE s   : LamWF ltv (.existE s) (.func (.func s (.base .prop)) (.base .prop))

def LamBaseTerm.LamWF.unique {ltv : LamTyVal} {b : LamBaseTerm} {s₁ s₂ : LamSort}
  (lbwf₁ : LamWF ltv b s₁) (lbwf₂ : LamWF ltv b s₂) : s₁ = s₂ ∧ HEq lbwf₁ lbwf₂ := by
  cases lbwf₁ <;> cases lbwf₂ <;> trivial

def LamBaseTerm.LamWF.reprPrec (wf : LamWF ltv s t) (n : Nat) :=
  let s :=
    match wf with
    | .ofTrueE      => f!".ofTrueE"
    | .ofFalseE     => f!".ofFalseE"
    | .ofNot        => f!".ofNot"
    | .ofAnd        => f!".ofAnd"
    | .ofOr         => f!".ofOr"
    | .ofImp        => f!".ofImp"
    | .ofIff        => f!".ofIff"
    | .ofIntVal n   => f!".ofIntVal {n}"
    | .ofRealVal cr => f!".ofRealVal {CstrReal.reprPrec cr 1}"
    | .ofBvVal ls   => f!".ofBvVal {ls}"
    | .ofEqI n      => f!".ofEqI {n}"
    | .ofForallEI n => f!".ofForallEI {n}"
    | .ofExistEI n  => f!".ofExistEI {n}"
    | .ofEq s       => f!".ofEq {LamSort.reprPrec s 1}"
    | .ofForallE s  => f!".ofForallE {LamSort.reprPrec s 1}"
    | .ofExistE s   => f!".ofExistE {LamSort.reprPrec s 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamBaseTerm.LamWF" ++ s
  else
    f!"({s})"

def LamBaseTerm.LamWF.ofLamBaseTerm (ltv : LamTyVal) : (b : LamBaseTerm) → (s : LamSort) × LamBaseTerm.LamWF ltv b s
| .trueE      => ⟨.base .prop, .ofTrueE⟩
| .falseE     => ⟨.base .prop, .ofFalseE⟩
| .not        => ⟨.func (.base .prop) (.base .prop), .ofNot⟩
| .and        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofAnd⟩
| .or         => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofOr⟩
| .imp        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofImp⟩
| .iff        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofIff⟩
| .intVal n   => ⟨.base .int, .ofIntVal n⟩
| .realVal cr => ⟨.base .real, .ofRealVal cr⟩
| .bvVal ls   => ⟨.base (.bv ls.length), .ofBvVal ls⟩
| .eqI n      => ⟨.func _ (.func _ (.base .prop)), .ofEqI n⟩
| .forallEI n => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallEI n⟩
| .existEI n  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistEI n⟩
| .eq s       => ⟨.func _ (.func _ (.base .prop)), .ofEq s⟩
| .forallE s  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallE s⟩
| .existE s   => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistE s⟩

def LamBaseTerm.wf_complete (wf : LamWF ltv b s) : LamWF.ofLamBaseTerm ltv b = ⟨s, wf⟩ := by
  cases wf <;> rfl

def LamBaseTerm.lamCheck_of_LamWF (H : LamWF ltv b s) : b.lamCheck ltv = s := by
  cases H <;> rfl

def LamBaseTerm.LamWF.ofCheck (H : b.lamCheck ltv = s) : LamWF ltv b s := by
  cases H; cases b <;> constructor

structure ILValuation extends LamTyVal where
  tyVal     : Nat → Type u
  eqVal     : ∀ (n : Nat), EqLift.{u + 1, u} ((eqLamVal n).interp tyVal)
  forallVal : ∀ (n : Nat), ForallLift.{u + 1, u, 0, 0} ((forallLamVal n).interp tyVal)
  existVal  : ∀ (n : Nat), ExistLift.{u + 1, u} ((existLamVal n).interp tyVal)

def eqVal.default (eqLamVal : Nat → LamSort) (tyVal : Nat → Type u) :
  ∀ (n : Nat), EqLift.{u + 1, u} ((eqLamVal n).interp tyVal) :=
  fun n => EqLift.default ((eqLamVal n).interp tyVal)

def forallVal.default (forallLamVal : Nat → LamSort) (tyVal : Nat → Type u) :
  ∀ (n : Nat), ForallLift.{u + 1, u, 0, 0} ((forallLamVal n).interp tyVal) :=
  fun n => ForallLift.default ((forallLamVal n).interp tyVal)

def LamBaseTerm.interp (ilVal : ILValuation.{u}) : (b : LamBaseTerm) → (b.lamCheck ilVal.toLamTyVal).interp ilVal.tyVal
| .trueE      => GLift.up True
| .falseE     => GLift.up False
| .not        => notLift
| .and        => andLift
| .or         => orLift
| .imp        => impLift
| .iff        => iffLift
| .intVal n   => GLift.up n
| .realVal cr => GLift.up cr.interp
| .bvVal ls   => GLift.up ⟨ls, rfl⟩
| .eqI n      => (ilVal.eqVal n).eqF
| .forallEI n => (ilVal.forallVal n).forallF
| .existEI n  => (ilVal.existVal n).existF
| .eq s       => @eqLiftFn (s.interp ilVal.tyVal)
| .forallE s  => @forallLiftFn (s.interp ilVal.tyVal)
| .existE s   => @existLiftFn (s.interp ilVal.tyVal)

def LamBaseTerm.LamWF.interp (ilVal : ILValuation.{u}) : (lwf : LamWF ilVal.toLamTyVal b s) → s.interp ilVal.tyVal
| .ofTrueE      => GLift.up True
| .ofFalseE     => GLift.up False
| .ofNot        => notLift
| .ofAnd        => andLift
| .ofOr         => orLift
| .ofImp        => impLift
| .ofIff        => iffLift
| .ofIntVal n   => GLift.up n
| .ofRealVal cr => GLift.up cr.interp
| .ofBvVal ls   => GLift.up ⟨ls, rfl⟩
| .ofEqI n      => (ilVal.eqVal n).eqF
| .ofForallEI n => (ilVal.forallVal n).forallF
| .ofExistEI n  => (ilVal.existVal n).existF
| .ofEq s       => @eqLiftFn (s.interp ilVal.tyVal)
| .ofForallE s  => @forallLiftFn (s.interp ilVal.tyVal)
| .ofExistE s   => @existLiftFn (s.interp ilVal.tyVal)

theorem LamBaseTerm.LamWF.interp.heq (ilVal : ILValuation.{u})
  (lwf₁ : LamWF ilVal.toLamTyVal b₁ s₁)
  (lwf₂ : LamWF ilVal.toLamTyVal b₂ s₂)
  (HBeq : b₁ = b₂) : HEq (LamWF.interp ilVal lwf₁) (LamWF.interp ilVal lwf₂) := by
  cases HBeq;
  cases LamWF.unique lwf₁ lwf₂
  case intro seq lweq =>
    cases seq; cases lweq; apply HEq.rfl

def LamBaseTerm.interp.equiv (ilVal : ILValuation.{u})
  (lwf : LamWF ilVal.toLamTyVal b s) :
  HEq (LamWF.interp ilVal lwf) (interp ilVal b) := by
  cases lwf <;> rfl

-- Judgement, `rterm ≝ mterm : ty`
structure LamBaseTerm.Judgement.{u} where
  -- A base term
  rterm : LamBaseTerm
  -- Type of `mterm`
  ty    : Type u
  -- The CIC term that `rterm` translates into
  mterm : ty

-- Base valuation
structure BaseValuation.{u} where
  -- Valuation of free type variables to constants in COC
  tyVal       : Nat → Type u
  -- Valuation of eqs' sorts
  eqTyVal     : Nat → Type u
  -- Valuation of foralls' sorts
  forallTyVal : Nat → Type u
  -- Valuation of exist' sorts
  existTyVal  : Nat → Type u
  eqVal       : ∀ (n : Nat), EqLift.{u + 1, u} (eqTyVal n)
  forallVal   : ∀ (n : Nat), ForallLift.{u + 1, u, 0, 0} (forallTyVal n)
  existVal    : ∀ (n : Nat), ExistLift.{u + 1, u} (existTyVal n)

def BaseValuation.ofILValuation.{u} : ILValuation.{u} → BaseValuation.{u} :=
  fun {lamVarTy, eqLamVal, forallLamVal, existLamVal, tyVal, eqVal, forallVal, existVal} =>
    ⟨tyVal,
     fun (n : Nat) => (eqLamVal n).interp tyVal,
     fun (n : Nat) => (forallLamVal n).interp tyVal,
     fun (n : Nat) => (existLamVal n).interp tyVal,
     eqVal,
     forallVal,
     existVal
    ⟩

def LamBaseTerm.check.{u} (baseVal : BaseValuation.{u}) : LamBaseTerm → Type u
| .trueE      => GLift.{1, u} Prop
| .falseE     => GLift.{1, u} Prop
| .not        => GLift.{1, u} Prop → GLift.{1, u} Prop
| .and        => GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop
| .or         => GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop
| .imp        => GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop
| .iff        => GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop
| .intVal _   => GLift.{1, u} Int
| .realVal _  => GLift.{1, u} Real
| .bvVal ls   => GLift.{1, u} (Bitvec ls.length)
| .eqI n      => baseVal.eqTyVal n → baseVal.eqTyVal n → GLift.{1, u} Prop
| .forallEI n => (baseVal.forallTyVal n → GLift.{1, u} Prop) → GLift.{1, u} Prop
| .existEI n  => (baseVal.existTyVal n → GLift.{1, u} Prop) → GLift.{1, u} Prop
| .eq s       => s.interp baseVal.tyVal → s.interp baseVal.tyVal → GLift.{1, u} Prop
| .forallE s  => (s.interp baseVal.tyVal → GLift.{1, u} Prop) → GLift.{1, u} Prop
| .existE s   => (s.interp baseVal.tyVal → GLift.{1, u} Prop) → GLift.{1, u} Prop

def LamBaseTerm.check_of_LamWF
  (ilVal : ILValuation) (H : LamWF ilVal.toLamTyVal b s) :
  check (.ofILValuation ilVal) b = s.interp ilVal.tyVal := by
  cases H <;> rfl

inductive LamBaseTerm.WF.{u} (baseVal : BaseValuation.{u}) : Judgement.{u} → Type u
  | ofTrueE      : WF baseVal ⟨.trueE, GLift.{1, u} Prop, GLift.up True⟩
  | ofFalseE     : WF baseVal ⟨.falseE, GLift.{1, u} Prop, GLift.up False⟩
  | ofNot        : WF baseVal ⟨.not, GLift.{1, u} Prop → GLift.{1, u} Prop, notLift.{u}⟩
  | ofAnd        : WF baseVal ⟨.and, GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop, andLift⟩
  | ofOr         : WF baseVal ⟨.or, GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop, orLift⟩
  | ofImp        : WF baseVal ⟨.imp, GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop, impLift⟩
  | ofIff        : WF baseVal ⟨.iff, GLift.{1, u} Prop → GLift.{1, u} Prop → GLift.{1, u} Prop, iffLift⟩
  | ofIntVal n   : WF baseVal ⟨.intVal n, GLift.{1, u} Int, GLift.up n⟩
  | ofRealVal cr : WF baseVal ⟨.realVal cr, GLift.{1, u} Real, GLift.up cr.interp⟩
  | ofBvVal ls   : WF baseVal ⟨.bvVal ls, GLift.{1, u} (Bitvec ls.length), GLift.up ⟨ls, rfl⟩⟩
  | ofEqI n      : WF baseVal ⟨.eqI n, baseVal.eqTyVal n → baseVal.eqTyVal n → GLift.{1, u} Prop, (baseVal.eqVal n).eqF⟩
  | ofForallEI n : WF baseVal ⟨.forallEI n, (baseVal.forallTyVal n → GLift.{1, u} Prop) → GLift.{1, u} Prop, (baseVal.forallVal n).forallF⟩
  | ofExistEI n  : WF baseVal ⟨.existEI n, (baseVal.existTyVal n → GLift.{1, u} Prop) → GLift.{1, u} Prop, (baseVal.existVal n).existF⟩
  | ofEq s       : WF baseVal ⟨.eq s, s.interp baseVal.tyVal → s.interp baseVal.tyVal → GLift.{1, u} Prop,
                               @eqLiftFn.{u} (s.interp baseVal.tyVal)⟩
  | ofForallE s  : WF baseVal ⟨.forallE s, (s.interp baseVal.tyVal → GLift.{1, u} Prop) → GLift.{1, u} Prop,
                               @forallLiftFn.{u} (s.interp baseVal.tyVal)⟩
  | ofExistE s   : WF baseVal ⟨.existE s, (s.interp baseVal.tyVal → GLift.{1, u} Prop) → GLift.{1, u} Prop,
                               @existLiftFn.{u} (s.interp baseVal.tyVal)⟩

def LamBaseTerm.WF.unique.{u} (baseVal : BaseValuation.{u})
  (bwf₁ : WF baseVal ⟨t, ty₁, val₁⟩)
  (bwf₂ : WF baseVal ⟨t, ty₂, val₂⟩)
  : ty₁ = ty₂ ∧ HEq val₁ val₂ ∧ HEq bwf₁ bwf₂ := by
  cases bwf₁ <;> cases bwf₂ <;> trivial

def LamBaseTerm.wf_of_lamWF.{u} (ilVal : ILValuation.{u})
  : (lwf : LamWF ilVal.toLamTyVal b s) →
     WF (.ofILValuation ilVal) ⟨b, s.interp ilVal.tyVal, LamWF.interp ilVal lwf⟩
| .ofTrueE      => .ofTrueE (baseVal:=.ofILValuation ilVal)
| .ofFalseE     => .ofFalseE (baseVal:=.ofILValuation ilVal)
| .ofNot        => .ofNot (baseVal:=.ofILValuation ilVal)
| .ofAnd        => .ofAnd (baseVal:=.ofILValuation ilVal)
| .ofOr         => .ofOr (baseVal:=.ofILValuation ilVal)
| .ofImp        => .ofImp (baseVal:=.ofILValuation ilVal)
| .ofIff        => .ofIff (baseVal:=.ofILValuation ilVal)
| .ofIntVal n   => .ofIntVal (baseVal:=.ofILValuation ilVal) n
| .ofRealVal cr => .ofRealVal (baseVal:=.ofILValuation ilVal) cr
| .ofBvVal ls   => .ofBvVal (baseVal:=.ofILValuation ilVal) ls
| .ofEqI n      => .ofEqI (baseVal:=.ofILValuation ilVal) n
| .ofForallEI n => .ofForallEI (baseVal:=.ofILValuation ilVal) n
| .ofExistEI n  => .ofExistEI (baseVal:=.ofILValuation ilVal) n
| .ofEq s       => .ofEq (baseVal:=.ofILValuation ilVal) s
| .ofForallE s  => .ofForallE (baseVal:=.ofILValuation ilVal) s
| .ofExistE s   => .ofExistE (baseVal:=.ofILValuation ilVal) s

inductive LamTerm
  | atom    : Nat → LamTerm
  | base    : LamBaseTerm → LamTerm
  | bvar    : Nat → LamTerm
  | lam     : LamSort → LamTerm → LamTerm
  -- The `LamSort` is here so that both the type of
  --   the function and argument can be inferred directly
  --   when we know the type of the application
  | app     : LamSort → LamTerm → LamTerm → LamTerm
deriving Inhabited, Hashable

def LamTerm.mkEq (s : LamSort) (t₁ t₂ : LamTerm) : LamTerm :=
  .app s (.app s (.base (.eq s)) t₁) t₂

def LamTerm.mkForallE (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.forallE s)) p

def LamTerm.mkExistE (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.existE s)) p

-- Check whether the term contains loose bound variables `idx` levels
--   above local context root
def LamTerm.hasLooseBVarEq (idx : Nat) : LamTerm → Bool
| .atom _ => false
| .base _ => false
| .bvar n => idx.beq n
| .lam _ t => t.hasLooseBVarEq (.succ idx)
| .app _ t₁ t₂ => t₁.hasLooseBVarEq idx || t₂.hasLooseBVarEq idx

-- Check whether the term contains loose bound variables greater
--   or equal to `idx` levels above local context root
def LamTerm.hasLooseBVarGe (idx : Nat) : LamTerm → Bool
| .atom _ => false
| .base _ => false
| .bvar n => idx.ble n
| .lam _ t => t.hasLooseBVarGe (.succ idx)
| .app _ t₁ t₂ => t₁.hasLooseBVarGe idx || t₂.hasLooseBVarGe idx

-- Whether the term contains any loose bound variables
def LamTerm.hasLooseBVar := LamTerm.hasLooseBVarGe 0

def LamTerm.maxLooseBVarSucc : LamTerm → Nat
| .atom _ => 0
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
    let h' := Nat.succ_le_succ h
    apply IH.mpr; rw [Nat.succ_pred] at h'; exact h'
    revert h; cases (maxLooseBVarSucc t)
    case zero => intro h; cases h
    case succ _ => intro _; simp
| .app _ t₁ t₂ => by
  dsimp [hasLooseBVarGe, maxLooseBVarSucc];
  rw [Bool.or_eq_true]; simp; rw [spec m t₁]; rw [spec m t₂]

def LamTerm.reprPrec (t : LamTerm) (n : Nat) :=
  let s :=
    match t with
    | .atom m => f!".atom {m}"
    | .base b => f!".base {LamBaseTerm.reprPrec b 1}"
    | .bvar m => f!".bvar {m}"
    | .lam s t => f!".lam {LamSort.reprPrec s 1} {LamTerm.reprPrec t 1}"
    | .app s t₁ t₂ => f!".app {LamSort.reprPrec s 1} {LamTerm.reprPrec t₁ 1} {LamTerm.reprPrec t₂ 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamTerm" ++ s
  else
    f!"({s})"

instance : Repr LamTerm where
  reprPrec f n := LamTerm.reprPrec f n

-- Typecheck. `ltv, lctx ⊢ term : type?`
-- `ltv`          : LamTyVal
-- `Nat → LamSort` : Local Context
def LamTerm.lamCheck? (ltv : LamTyVal) :
  (Nat → LamSort) → LamTerm → Option LamSort
| _,    .atom n  => ltv.lamVarTy n
| _,    .base b  => b.lamCheck ltv
| lctx, .bvar n  => lctx n
| lctx, .lam s t =>
  match t.lamCheck? ltv (pushLCtx s lctx) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app s fn arg =>
  match fn.lamCheck? ltv lctx, arg.lamCheck? ltv lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    match ty₁.beq s, argTy.beq s with
    | true, true => .some ty₂ 
    | _,    _    => none
  | _, _ => .none

theorem LamTerm.lamCheck?_irrelevence
  {ltv : LamTyVal} {lctx₁ lctx₂ : Nat → LamSort} {t : LamTerm}
  (hirr : ∀ n, n < t.maxLooseBVarSucc → lctx₁ n = lctx₂ n) :
  LamTerm.lamCheck? ltv lctx₁ t = LamTerm.lamCheck? ltv lctx₂ t := by
  revert lctx₁ lctx₂; induction t <;> intros lctx₁ lctx₂ hirr <;>
    dsimp [LamTerm.lamCheck?]
  case bvar n =>
    apply congrArg; apply hirr; exact .refl
  case lam s t IHt =>
    rw [IHt]; intros n hlt; cases n
    case zero => rfl
    case succ n =>
      dsimp [pushLCtx]; rw [hirr]; dsimp [maxLooseBVarSucc]
      apply Nat.le_pred_of_succ_le _ hlt;
      apply Nat.not_eq_zero_of_lt hlt
  case app s fn arg IHFn IHArg =>
    rw [IHFn]; rw [IHArg];
    intros n hlt; rw [hirr n (Nat.le_trans hlt (Nat.le_max_right _ _))]
    intros n hlt; rw [hirr n (Nat.le_trans hlt (Nat.le_max_left _ _))]

def LamTerm.lamCheck! (default : LamSort) (ltv : LamTyVal) :
  (Nat → LamSort) → LamTerm → LamSort
| _,    .atom n  => ltv.lamVarTy n
| _,    .base b  => b.lamCheck ltv
| lctx, .bvar n  => lctx n
| lctx, .lam s t => .func s (t.lamCheck! default ltv (pushLCtx s lctx))
| lctx, .app s fn arg =>
  match fn.lamCheck! default ltv lctx, arg.lamCheck! default ltv lctx with
  | .func ty₁ ty₂, argTy =>
    match ty₁.beq s, argTy.beq s with
    | true, true => ty₂
    | _, _ => default
  | _, _ => default

def LamTerm.lamCheck.equiv (default : LamSort) {ltv : LamTyVal} {lctx : Nat → LamSort} :
  {t : LamTerm} → {res : LamSort} → LamTerm.lamCheck? ltv lctx t = .some res →
  LamTerm.lamCheck! default ltv lctx t = res
| .atom n, _, H => Option.some.inj H
| .base b, _, H => Option.some.inj H
| .bvar n, _, H => Option.some.inj H
| .lam s t, res, H => by
  dsimp [lamCheck?] at H; revert H
  cases hCheck : (lamCheck? ltv (pushLCtx s lctx) t)
  case none => intro contra; cases contra
  case some res' =>
    intro heq;
    have heq' := Option.some.inj heq; rw [← heq']
    dsimp [lamCheck!]; congr
    apply LamTerm.lamCheck.equiv default (lctx:=pushLCtx s lctx) hCheck    
| .app s fn arg, res, H => by
  dsimp [lamCheck?] at H; revert H
  match hCheckFn : lamCheck? ltv lctx fn, hCheckArg : lamCheck? ltv lctx arg with
  | .some resFn, .some resArg =>
    dsimp [lamCheck!];
    rw [LamTerm.lamCheck.equiv default hCheckFn]
    rw [LamTerm.lamCheck.equiv default hCheckArg]
    match resFn with
    | .atom _ => intro contra; cases contra
    | .base _ => intro contra; cases contra
    | .func argTy resTy =>
      dsimp;
      match LamSort.beq argTy s, LamSort.beq resArg s with
      | true, true   => intro H; exact Option.some.inj H
      | true, false  => intro contra; cases contra
      | false, true  => intro contra; cases contra
      | false, false => intro contra; cases contra
  | .some resFn, none =>
    cases resFn <;> intro contra <;> cases contra
  | .none, _ => intro contra; cases contra

-- Judgement. `lamVarTy, lctx ⊢ term : type?`
structure LamJudge where
  lctx   : Nat → LamSort
  rterm  : LamTerm
  rty    : LamSort
deriving Inhabited

inductive LamWF (ltv : LamTyVal) : LamJudge → Type
  | ofAtom
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF ltv ⟨lctx, .atom n, ltv.lamVarTy n⟩
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

def LamWF.unique {ltv : LamTyVal} :
  (lwf₁ : LamWF ltv ⟨lctx, t, s₁⟩) → (lwf₂ : LamWF ltv ⟨lctx, t, s₂⟩) →
  s₁ = s₂ ∧ HEq lwf₁ lwf₂
| .ofAtom _,  .ofAtom _  => And.intro rfl HEq.rfl
| .ofBase H₁, .ofBase H₂ => by
  have heq := LamBaseTerm.LamWF.unique H₁ H₂
  cases heq; case intro left right =>
    cases left; cases right; apply And.intro; rfl; rfl
| .ofBVar _,  .ofBVar _  => And.intro rfl HEq.rfl
| .ofLam bodyTy H₁, .ofLam _ H₂ => by
  have heq := LamWF.unique H₁ H₂
  cases heq; case intro left right =>
    cases left; cases right; apply And.intro; rfl; rfl
| .ofApp argTy₁ HFn₁ HArg₁, .ofApp _ HFn₂ HArg₂ => by
  have heqFn := LamWF.unique HFn₁ HFn₂
  have heqArg := LamWF.unique HArg₁ HArg₂
  cases heqFn;
    case intro fnLeft fnRight =>
    cases fnLeft; cases fnRight
    cases heqArg;
    case intro argLeft argRight =>
      cases argLeft; cases argRight
      apply And.intro; rfl; rfl

def LamWF.mkEq {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, s⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, s⟩) :
  LamWF ltv ⟨lctx, .mkEq s t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂

def LamWF.mkForallE {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .func s (.base .prop)⟩) :
  LamWF ltv ⟨lctx, .mkForallE s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofForallE _)) wfp

def LamWF.mkExistE {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .func s (.base .prop)⟩) :
  LamWF ltv ⟨lctx, .mkExistE s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofExistE _)) wfp

def LamWF.ofAtom' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : ltv.lamVarTy n = s) : LamWF ltv ⟨lctx, .atom n, s⟩ := by
  rw [← heq]; apply LamWF.ofAtom

def LamWF.ofBVar' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : lctx n = s) : LamWF ltv ⟨lctx, .bvar n, s⟩ := by
  rw [← heq]; apply LamWF.ofBVar

def LamWF.reprPrec (wf : LamWF f judge) (n : Nat) (lctxDep : Nat) :=
  let rec formatLCtxAux prec : (lctx : List LamSort) → Lean.Format
    | .nil => f!""
    | .cons a as => ", " ++ a.reprPrec prec ++ formatLCtxAux prec as
  let pre := "fun n => "
  let trail := ".getD n (.atom 0)"
  let formatLCtx prec (lctx : Nat → LamSort) : (lctxDep : Nat) → Lean.Format
    | 0 => pre ++ f!"[]" ++ trail
    | n + 1 => pre ++ f!"[" ++ (lctx 0).reprPrec prec ++
               formatLCtxAux prec ((List.range n).map (fun i => lctx (i + 1))) ++ f!"]" ++
               trail
  match wf with
  | @LamWF.ofAtom _ lctx m =>
    if n == 0 then
      f!"Auto.Embedding.Lam.LamWF.ofAtom (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofAtom {m})"
  | @LamWF.ofBase _ lctx _ _ H =>
    if n == 0 then
      f!"Auto.Embedding.Lam.LamWF.ofBase (lctx := {formatLCtx 1 lctx lctxDep}) {H.reprPrec 1}"
    else
      f!"(.ofBase {H.reprPrec 1})"
  | @LamWF.ofBVar _ lctx m =>
    if n == 0 then
      f!"Auto.Embedding.Lam.LamWF.ofBVar (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofBVar {m})"
  | @LamWF.ofLam _ lctx argTy bodyTy body H =>
    if n == 0 then
      f!"Auto.Embedding.Lam.LamWF.ofLam (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"(body := {body.reprPrec 1}) {LamWF.reprPrec H 1 (lctxDep + 1)}"
    else
      f!"(.ofLam (argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec H 1 (lctxDep + 1)})"
  | @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg =>
    if n == 0 then
      f!"Auto.Embedding.Lam.LamWF.ofApp (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"(fn := {fn.reprPrec 1}) (arg := {arg.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1 lctxDep} {LamWF.reprPrec HArg 1 lctxDep}"
    else
      f!"(.ofApp (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1 lctxDep} {LamWF.reprPrec HArg 1 lctxDep})"

instance : Repr (LamWF ltv judge) where
  reprPrec wf _ := LamWF.reprPrec wf 0 0

def LamWF.ofLamTerm {ltv : LamTyVal} :
  {lctx : Nat → LamSort} → (t : LamTerm) → Option ((rty : LamSort) × LamWF ltv ⟨lctx, t, rty⟩)
| lctx, .atom n => .some ⟨ltv.lamVarTy n, .ofAtom n⟩
| lctx, .base b =>
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
      have tyEq := LamSort.beq_eq _ _ heq
      have argTyEq := LamSort.beq_eq _ _ heqa
      .some ⟨ty₂, .ofApp s (tyEq ▸ fnWf) (argTyEq ▸ argWf)⟩
    | _, _ => .none
  | _, _ => .none

-- #eval (@LamWF.ofLamTerm
--   (ltv := {(Inhabited.default : LamTyVal) with
--     lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1)})
--   (lctx := fun _ => .atom 0)
--   (t := .lam (.atom 0) (.app (.atom 1) (.atom 0))))
-- 
-- #check Auto.Embedding.Lam.LamWF.ofLam
--   (ltv := {(Inhabited.default : LamTyVal) with
--     lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1)})
--   (lctx := fun _ => .atom 0) (argTy := (.atom 0)) (bodyTy := (.atom 1)) (body := (.app (.atom 1) (.atom 0))) (.ofApp (lctx := _) (argTy := (.atom 2)) (resTy := (.atom 1)) (.ofAtom 1) (.ofAtom 0))

def LamWF.complete_Aux
  {b : β} (p : Bool) (f : (p = true) → β) (eq : p = true) :
  (match (generalizing:=false) h : p with
  | true => f h
  | false => b) = f eq := by
  cases p
  case false => cases eq
  case true => simp

-- Of course `ofLamTerm` is sound with respect to `LamWF`. So, we
--   only need to show that it's complete
def LamWF.complete {ltv : LamTyVal} :
  {j : LamJudge} → (wf : LamWF ltv j) → LamWF.ofLamTerm j.rterm = .some ⟨j.rty, wf⟩
| .(_), @LamWF.ofAtom _ lctx n => rfl
| .(_), @LamWF.ofBase _ lctx b s h => by
  unfold ofLamTerm; rw [LamBaseTerm.wf_complete]
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

def LamTerm.lamCheck?_of_lamWF
  {ltv : LamTyVal} {lctx : Nat → LamSort} {t : LamTerm} {ty : LamSort} :
  LamWF ltv ⟨lctx, t, ty⟩ → t.lamCheck? ltv lctx = .some ty := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rty := ty : LamJudge} = Judge 
  intro HWf; revert lctx t ty JudgeEq; induction HWf
  case ofAtom lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq]; rfl
  case ofBase lctx' b s H =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq, lamCheck?]; rw [LamBaseTerm.lamCheck_of_LamWF H]
  case ofBVar lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]; rfl
  case ofLam lctx' argTy bodyTy body H H_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq];
    simp [lamCheck?]; rw [H_ih]; rfl
  case ofApp lctx' argTy resTy fn arg HFn HArg HFn_ih HArg_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]
    simp [lamCheck?];
    rw [@HFn_ih lctx' fn (LamSort.func argTy resTy)] <;> try rfl;
    rw [@HArg_ih lctx' arg argTy] <;> try rfl;
    simp [LamSort.beq_refl]

def LamTerm.lamCheck!_of_lamWF {default : LamSort}
  {ltv : LamTyVal} {lctx : Nat → LamSort} {t : LamTerm} {ty : LamSort}
  (H : LamWF ltv ⟨lctx, t, ty⟩) : t.lamCheck! default ltv lctx = ty :=
  LamTerm.lamCheck.equiv default (LamTerm.lamCheck?_of_lamWF H)

-- This function is meant to be `execute`-d (`eval`-ed), not `reduce`-d
-- **TODO**: Change type to `match` so that we don't need `rw`.
--   But do not delete this, because it shows problems (proof not fully reducing)
def LamWF.ofLamCheck? {ltv : LamTyVal} :
  {lctx : Nat → LamSort} → {t : LamTerm} → {ty : LamSort} →
  t.lamCheck? ltv lctx = .some ty → LamWF ltv ⟨lctx, t, ty⟩
| lctx, .atom n, ty, HCheck => by
  have HCheck' := Option.some.inj HCheck
  rw [← HCheck']; apply LamWF.ofAtom
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
    cases heq : LamSort.beq ty₁ s
    case false => intro contra; cases contra
    have heq' : ty₁ = s := LamSort.beq_eq _ _ heq; cases heq'
    cases heqa : LamSort.beq argTy s
    case false => intro contra; cases contra
    have heqa' : argTy = s := LamSort.beq_eq _ _ heqa; cases heqa'
    case true =>
      dsimp;
      intro H; rw [← Option.some.inj H]; apply LamWF.ofApp (argTy:=s);
      case HFn => apply (ofLamCheck? CheckFnEq)
      case HArg => apply (ofLamCheck? CheckArgEq)
  | .some (LamSort.func _ _), .none => intro contra; cases contra
  | .some (LamSort.atom _), _ => intro contra; cases contra
  | .some (LamSort.base _), _ => intro contra; cases contra
  | .none, _ => intro contra; cases contra

/-
#reduce @LamWF.ofLamCheck?
  (ltv := {(Inhabited.default : LamTyVal) with lamVarTy := fun n => .atom 0})
  (lctx := fun _ => .atom 0)
  (t := .atom 0)
  (ty := .atom 0)
  rfl

#reduce @LamWF.ofLamCheck?
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then .func (.atom 0) (.atom 0) else .atom 0})
  (lctx := fun _ => .atom 0)
  (t := .app (.atom 0) (.atom 0) (.atom 1))
  (ty := .atom 0)
  rfl

#reduce @LamWF.ofLamCheck?
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1)})
  (lctx := fun _ => .atom 0)
  (t := .lam (.atom 0) (.app (.atom 2) (.atom 1) (.atom 0)))
  (ty := .func (.atom 0) (.atom 1))
  rfl

#eval @LamWF.ofLamCheck?
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1)})
  (lctx := fun _ => .atom 0)
  (t := .lam (.atom 0) (.app (.atom 2) (.atom 1) (.atom 0)))
  (ty := .func (.atom 0) (.atom 1))
  rfl
-/

structure LamValuation.{u} where
  ilVal     : ILValuation.{u}
  varVal    : ∀ (n : Nat), (ilVal.lamVarTy n).interp ilVal.tyVal

def LamTerm.interp.{u}
  (dfSort : LamSort) (lval : LamValuation.{u}) (dfVal : dfSort.interp lval.ilVal.tyVal)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) :
  (t : LamTerm) → (t.lamCheck! dfSort lval.ilVal.toLamTyVal lctxTy).interp lval.ilVal.tyVal
| .atom n => lval.varVal n
| .base b => LamBaseTerm.interp lval.ilVal b
| .bvar n => lctxTerm n
| .lam s body =>
  fun (x : s.interp lval.ilVal.tyVal) =>
    LamTerm.interp dfSort lval dfVal (pushLCtx s lctxTy) (pushLCtxDep (rty:=lctxTy) x lctxTerm) body
| .app s fn arg => (fun fnInterp argInterp => by
  dsimp [lamCheck!]
  revert fnInterp argInterp
  match
    hCheck₁ : lamCheck! dfSort lval.ilVal.toLamTyVal lctxTy fn,
    hCheck₂ : lamCheck! dfSort lval.ilVal.toLamTyVal lctxTy arg with
  | .atom _, _ => intros _ _; exact dfVal
  | .base _, _ => intros _ _; exact dfVal
  | .func argTy' resTy', argTy =>
    dsimp
    match heq : LamSort.beq argTy' s, heqa : LamSort.beq argTy s with
    | true, true =>
      intros fnInterp argInterp; dsimp at fnInterp
      have heq' := LamSort.beq_eq _ _ heq; cases heq'
      have heqa' := LamSort.beq_eq _ _ heqa; cases heqa'
      dsimp [LamSort.interp] at fnInterp
      exact (fnInterp argInterp)
    | true,  false => intros _ _; exact dfVal
    | false, true  => intros _ _; exact dfVal
    | false, false => intros _ _; exact dfVal)
  (LamTerm.interp dfSort lval dfVal lctxTy lctxTerm fn)
  (LamTerm.interp dfSort lval dfVal lctxTy lctxTerm arg)

def LamTerm.interpAsPropAux.{u}
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) (t : LamTerm)
  (heq : t.lamCheck! (.base .prop) lval.ilVal.toLamTyVal lctxTy = s) : GLift.{1, u} Prop :=
  match s with
  | .base .prop =>
    let m := LamTerm.interp (.base .prop) lval (GLift.up False) lctxTy lctxTerm t
    Eq.mp (by rw [heq]) m
  | _ => GLift.up False

theorem LamTerm.interpAsPropAux.equiv
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) (t : LamTerm)
  (heq : t.lamCheck! (.base .prop) lval.ilVal.toLamTyVal lctxTy = s)
  (heq' : t.lamCheck! (.base .prop) lval.ilVal.toLamTyVal lctxTy = .base .prop) :
  HEq
    (LamTerm.interpAsPropAux lval lctxTy lctxTerm t heq)
    (LamTerm.interp (.base .prop) lval (GLift.up False) lctxTy lctxTerm t) := by
  dsimp [LamTerm.interpAsPropAux];
  rw [heq'] at heq; cases s <;> try cases heq
  dsimp; apply HEq.symm; apply heq_of_cast_eq _ rfl

def LamTerm.interpAsProp.{u}
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) (t : LamTerm) : GLift.{1, u} Prop :=
  LamTerm.interpAsPropAux lval lctxTy lctxTerm t rfl

theorem LamTerm.interpAsProp.equiv
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) (t : LamTerm)
  (heq : t.lamCheck! (.base .prop) lval.ilVal.toLamTyVal lctxTy = .base .prop) :
  HEq
    (LamTerm.interpAsProp lval lctxTy lctxTerm t)
    (LamTerm.interp (.base .prop) lval (GLift.up False) lctxTy lctxTerm t) := by
  apply LamTerm.interpAsPropAux.equiv; exact heq

def LamWF.interp.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (lwf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩) → rty.interp lval.ilVal.tyVal
| _,      lctxTerm, .ofAtom n => lval.varVal n
| _,      _       , .ofBase H => LamBaseTerm.LamWF.interp lval.ilVal H
| lctxTy, lctxTerm, .ofBVar n => lctxTerm n
| lctxTy, lctxTerm, @LamWF.ofLam _ _ argTy _ body H =>
  fun (x : argTy.interp lval.ilVal.tyVal) =>
    LamWF.interp lval (pushLCtx argTy lctxTy) (pushLCtxDep (rty:=lctxTy) x lctxTerm) H
| lctxTy, lctxTerm, .ofApp _ HFn HArg =>
  let mfn := LamWF.interp lval lctxTy lctxTerm HFn
  let marg := LamWF.interp lval lctxTy lctxTerm HArg
  mfn marg

theorem LamWF.interp.heq (lval : LamValuation.{u})
  {lctxTy₁ lctxTy₂ : Nat → LamSort} (HLCtxTyEq : lctxTy₁ = lctxTy₂)
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval.ilVal.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval.ilVal.tyVal}
  (HLCtxTermEq : HEq lctxTerm₁ lctxTerm₂)
  (lwf₁ : LamWF lval.ilVal.toLamTyVal ⟨lctxTy₁, t₁, rty₁⟩)
  (lwf₂ : LamWF lval.ilVal.toLamTyVal ⟨lctxTy₂, t₂, rty₂⟩)
  (HTeq : t₁ = t₂) :
  HEq (LamWF.interp lval lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval lctxTy₂ lctxTerm₂ lwf₂) := by
  cases HTeq; cases HLCtxTyEq; cases HLCtxTermEq;
  have HUniq := LamWF.unique lwf₁ lwf₂
  cases HUniq; case intro left right =>
    cases left; cases right; rfl

theorem LamWF.interp_irrelevance
  (lval : LamValuation.{u}) {lctxTy₁ lctxTy₂ : Nat → LamSort}
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval.ilVal.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval.ilVal.tyVal}
  {t : LamTerm} {rty : LamSort}
  (lwf₁ : LamWF lval.ilVal.toLamTyVal ⟨lctxTy₁, t, rty⟩)
  (lwf₂ : LamWF lval.ilVal.toLamTyVal ⟨lctxTy₂, t, rty⟩)
  (hirr : ∀ n, n < t.maxLooseBVarSucc → 
    lctxTy₁ n = lctxTy₂ n ∧ HEq (lctxTerm₁ n) (lctxTerm₂ n)) :
  HEq (LamWF.interp lval lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval lctxTy₂ lctxTerm₂ lwf₂) := by
  revert lctxTy₁ lctxTy₂ rty;
  induction t <;> intros lctxTy₁ lctxTy₂ lctxTerm₁ lctxTerm₂ rty lwf₁ lwf₂ hirr
  case atom n =>
    cases lwf₁; cases lwf₂; rfl
  case base b =>
    cases lwf₁; cases lwf₂; dsimp [interp]; apply LamBaseTerm.LamWF.interp.heq <;> rfl
  case bvar n =>
    cases lwf₁; dsimp [interp]
    have htyeq : lctxTy₁ n = lctxTy₂ n := by
      apply (hirr _ _).left; exact .refl
    rw [htyeq] at lwf₂; apply HEq.trans (b:=interp _ _ lctxTerm₂ lwf₂)
    case h₁ =>
      cases lwf₂; dsimp [interp]; apply (hirr _ _).right; exact .refl
    case h₂ =>
      apply interp.heq <;> rfl
  case lam s t IH =>
    cases lwf₁;
    case ofLam bodyTy₁ H₁ =>
      cases lwf₂
      case ofLam H₂ =>
        dsimp [interp]; apply HEq.funext; intros x; apply IH
        intros n hlt; dsimp [pushLCtx, pushLCtxDep]
        cases n
        case zero => exact And.intro rfl HEq.rfl
        case succ n =>
          apply hirr;
          apply Nat.le_pred_of_succ_le _ hlt
          apply Nat.not_eq_zero_of_lt hlt
  case app s fn arg IHFn IHArg =>
    cases lwf₁;
    case ofApp HArg₁ HFn₁ =>
      cases lwf₂;
      case ofApp HArg₂ HFn₂ =>
        dsimp [interp]; apply congr_h_heq <;> try rfl
        case h₁ =>
          apply IHFn; intros n hlt;
          apply (hirr n (Nat.le_trans hlt (Nat.le_max_left _ _)))
        case h₂ =>
          apply IHArg; intros n hlt;
          apply (hirr n (Nat.le_trans hlt (Nat.le_max_right _ _)))

theorem LamTerm.interp.equiv
  {dfSort : LamSort} (lval : LamValuation.{u})
  {dfVal : LamSort.interp lval.ilVal.tyVal dfSort}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  (lwf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩) :
  HEq (LamWF.interp lval lctxTy lctxTerm lwf) (LamTerm.interp dfSort lval dfVal lctxTy lctxTerm t) := by
  revert lctxTy rty; induction t <;> intros rty lctxTy lctxTerm lwf
  case atom n =>
    cases lwf; rfl
  case base b =>
    cases lwf; apply LamBaseTerm.interp.equiv
  case bvar n =>
    cases lwf; rfl
  case lam s t IH =>
    cases lwf
    case ofLam bodyTy H =>
      dsimp [LamWF.interp, interp]; apply HEq.funext; intros x
      apply IH
  case app s fn arg IHFn IHArg =>
    have HApp := lamCheck!_of_lamWF (default:=dfSort) lwf
    cases lwf
    case ofApp HArg HFn =>
      dsimp [LamWF.interp, interp, lamCheck!]
      have HFn' := lamCheck!_of_lamWF (default:=dfSort) HFn
      have HArg' := lamCheck!_of_lamWF (default:=dfSort) HArg
      let bf := fun
        (f : LamSort.interp lval.ilVal.tyVal (LamSort.func s rty))
        (x : LamSort.interp lval.ilVal.tyVal s) => f x
      apply HEq.trans (b := bf
        (LamWF.interp lval lctxTy lctxTerm HFn)
        (LamWF.interp lval lctxTy lctxTerm HArg)) HEq.rfl
      apply congr₂_h_heq
      case Hγ => dsimp [lamCheck!] at HApp; rw [HApp]
      case h₁ =>
        rw [HFn', HArg']; dsimp
        rw [LamSort.beq_refl]
      case h₂ => apply IHFn
      case h₃ => apply IHArg

-- Judgement, `lctx ⊢ rterm ≝ mterm : ty`
structure Judgement.{u} where
  -- Local context, list of CIC terms
  lctxTy   : Nat → Type u
  lctxTerm : ∀ (n : Nat), lctxTy n
  -- A term in simply typed lambda calculus
  rterm    : LamTerm
  -- Type of `mterm`
  ty       : Type u
  -- The CIC term that `rterm` translates into
  mterm    : ty

-- Valuation
structure Valuation.{u} extends BaseValuation.{u} where
  -- valuation of free variables to constants in COC
  varTy       : Nat → Type u
  varVal      : ∀ (n : Nat), varTy n

@[reducible] def Valuation.ofLamValuation : LamValuation → Valuation :=
  fun ⟨ilVal, varVal⟩ =>
    let baseVal : BaseValuation := ⟨
      ilVal.tyVal,
      fun n => (ilVal.eqLamVal n).interp ilVal.tyVal,
      fun n => (ilVal.forallLamVal n).interp ilVal.tyVal,
      fun n => (ilVal.existLamVal n).interp ilVal.tyVal,
      ilVal.eqVal,
      ilVal.forallVal,
      ilVal.existVal
    ⟩
    ⟨baseVal, fun n => (ilVal.lamVarTy n).interp ilVal.tyVal, varVal⟩

inductive LamTerm.check.{u} (val : Valuation.{u}) :
  (lctx : Nat → Type u) → LamTerm → (ty : Type u) → Type (u + 1)
  | ofAtom n : check val lctx (.atom n) (val.varTy n)
  | ofBase b : check val lctx (.base b) (b.check val.toBaseValuation)
  | ofBVar n : check val lctx (.bvar n) (lctx n)
  | ofLam s
      (tch : check val (pushLCtx (s.interp val.tyVal) lctx) t tty) :
      check val lctx (.lam s t) (s.interp val.tyVal → tty)
  | ofApp
      (fnch : check val lctx fn ((s.interp val.tyVal) → resTy))
      (argch : check val lctx arg argTy) :
      check val lctx (.app s fn arg) resTy

def LamTerm.check_of_LamWF (lVal : LamValuation) :
  (H : LamWF lVal.ilVal.toLamTyVal ⟨lctx, t, s⟩) →
  LamTerm.check (.ofLamValuation lVal) (fun n => (lctx n).interp lVal.ilVal.tyVal) t (s.interp lVal.ilVal.tyVal)
| .ofAtom n => .ofAtom n
| .ofBase (b:=b) H => LamBaseTerm.check_of_LamWF _ H ▸ .ofBase b
| .ofBVar n => .ofBVar n
| .ofLam (body:=body) _ wfBody =>
  .ofLam _
    (Eq.mp (congrFun (congrFun (congrArg _ (funext (fun _ => pushLCtx.comm (LamSort.interp _) _ _ _))) _) _)
    (LamTerm.check_of_LamWF lVal wfBody))
| .ofApp _ wfFn wfArg =>
  .ofApp (LamTerm.check_of_LamWF lVal wfFn) (LamTerm.check_of_LamWF lVal wfArg)

def impEqAx.{u, v} := ∀ (α₁ α₂ : Sort u) (β₁ β₂ : Sort v),
  (α₁ → β₁) = (α₂ → β₂) → α₁ = α₂ ∧ β₁ = β₂

def LamTerm.check.unique.{u} {ax : impEqAx.{u + 1, u + 1}} (val : Valuation.{u}) :
  (hch₁ : LamTerm.check val lctx t ty₁) → (hch₂ : LamTerm.check val lctx t ty₂) →
  ty₁ = ty₂ ∧ HEq hch₁ hch₂
| .ofAtom _,  .ofAtom _ => And.intro rfl HEq.rfl
| .ofBase b₁, .ofBase _ => And.intro rfl HEq.rfl
| .ofBVar _,  .ofBVar _ => And.intro rfl HEq.rfl
| .ofLam (t:=t₁) (tty:=tty₁) s tch₁, .ofLam (tty:=tty₂) _ tch₂ => by
  have hCheck := LamTerm.check.unique (ax:=ax) val tch₁ tch₂
  cases hCheck
  case intro left right =>
    cases left; cases right; apply And.intro <;> rfl
| .ofApp fnch₁ argch₁, .ofApp fnch₂ argch₂ => by
  have fnCheck := LamTerm.check.unique (ax:=ax) val fnch₁ fnch₂
  have argCheck := LamTerm.check.unique (ax:=ax) val argch₁ argch₂
  cases argCheck
  case intro left right =>
    cases left; cases right
    cases fnCheck
    case intro left' right' =>
      let axEq := ax _ _ _ _ left'
      cases axEq; case intro left'' right'' =>
        cases right''; cases right'; apply And.intro <;> rfl
        
set_option genInjectivity false in
inductive WF.{u} (val : Valuation.{u}) : Judgement.{u} → Type (u + 1)
  | ofAtom
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n} (n : Nat) :
    WF val <|
      ⟨lctxTy, lctxTerm, (.atom n), val.varTy n, val.varVal n⟩
  | ofBase
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hb : LamBaseTerm} {α : Type u} {b : α}
      (Hb : LamBaseTerm.WF val.toBaseValuation ⟨hb, α, b⟩) :
    WF val <|
      ⟨lctxTy, lctxTerm, (.base hb), α, b⟩
  | ofBVar
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n} (n : Nat) :
    WF val <|
      ⟨lctxTy, lctxTerm, .bvar n, lctxTy n, lctxTerm n⟩
  | ofLam
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hs : LamSort} {ht : LamTerm}
      -- The `HCheck` here is necessary. For example, if we
      --   don't require `α` to be equal to `hs.interp val.tyVal`,
      --   it's always possible to take `α = Empty`, `β`
      --   an arbitrary type, and `fn = Empty.elim β`.
      (α β : Type u) (fn : α → β) (HChk : LamTerm.check val lctxTy (.lam hs ht) (α → β))
      (H : ∀ (t : α), WF val ⟨pushLCtx α lctxTy, pushLCtxDep (lctxty:=id) t lctxTerm, ht, β, fn t⟩) :
    WF val <|
      ⟨lctxTy, lctxTerm, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hfn harg : LamTerm}
      (s : LamSort) (β : Type u) (fn : s.interp val.tyVal → β) (arg : s.interp val.tyVal)
      (Hfn : WF val ⟨lctxTy, lctxTerm, hfn, s.interp val.tyVal → β, fn⟩)
      (Harg : WF val ⟨lctxTy, lctxTerm, harg, s.interp val.tyVal, arg⟩)
      :
    WF val <|
      ⟨lctxTy, lctxTerm, .app s hfn harg, β, fn arg⟩

def WF.unique.{u} {ax : impEqAx.{u + 1, u + 1}} (val : Valuation.{u})
  {lctxTy : Nat → Type u} {lctxTerm : ∀ n, lctxTy n} :
  (wf₁ : WF val ⟨lctxTy, lctxTerm, t, s₁, val₁⟩) →
  (wf₂ : WF val ⟨lctxTy, lctxTerm, t, s₂, val₂⟩) →
  s₁ = s₂ ∧ HEq val₁ val₂ ∧ HEq wf₁ wf₂
| .ofAtom _, .ofAtom _ => And.intro rfl (And.intro HEq.rfl HEq.rfl)
| .ofBase H₁, .ofBase H₂ => by
  have heq := LamBaseTerm.WF.unique val.toBaseValuation H₁ H₂
  cases heq
  case intro left right =>
    cases left; cases right
    case intro left' right' =>
      cases left'; cases right'
      apply And.intro rfl (And.intro HEq.rfl HEq.rfl)
| .ofBVar _, .ofBVar _ => And.intro rfl (And.intro HEq.rfl HEq.rfl)
| .ofLam (hs:=hs) (ht:=ht) α₁ β₁ fn₁ HChk₁ H₁, .ofLam α₂ β₂ fn₂ HChk₂ H₂ => by
  have checkUniq := LamTerm.check.unique (ax:=ax) val HChk₁ HChk₂
  have tyEq := ax _ _ _ _ (And.left checkUniq)
  have checkEq := And.right checkUniq
  cases tyEq;
  case intro left right =>
    cases left; cases right; cases checkEq; apply And.intro rfl;
    have fnEq : fn₁ = fn₂ := funext (fun x =>
      let heq := WF.unique (ax:=ax) val (H₁ x) (H₂ x)
      eq_of_heq heq.right.left
    )
    cases fnEq;
    have wfEq : H₁ = H₂ := funext (fun x =>
      let heq := WF.unique (ax:=ax) val (H₁ x) (H₂ x)
      eq_of_heq heq.right.right
    )
    cases wfEq; apply And.intro <;> rfl
| .ofApp _ β₁ fn₁ arg₁ HFn₁ HArg₁, .ofApp _ β₂ fn₂ arg₂ HFn₂ HArg₂ => by
  have hFnEq := WF.unique (ax:=ax) val HFn₁ HFn₂
  have hArgEq := WF.unique (ax:=ax) val HArg₁ HArg₂
  have hTyEq := ax _ _ _ _ hFnEq.left
  cases hTyEq.left; cases hTyEq.right;
  cases hFnEq.right.left; cases hFnEq.right.right;
  cases hArgEq.right.left; cases hArgEq.right.right;
  apply And.intro rfl (And.intro HEq.rfl HEq.rfl)

def LamTerm.wf_of_lamWF.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (lwf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩) →
  WF (Valuation.ofLamValuation lval)
    ⟨fun n => (lctxTy n).interp lval.ilVal.tyVal, lctxTerm, t, rty.interp lval.ilVal.tyVal, LamWF.interp lval lctxTy lctxTerm lwf⟩
| _,       lctxTerm', @LamWF.ofAtom _ _ n => WF.ofAtom _
| _,       _,         @LamWF.ofBase _ _ b s H => WF.ofBase (LamBaseTerm.wf_of_lamWF lval.ilVal H)
| lctxTy', lctxTerm', @LamWF.ofBVar _ _ n => WF.ofBVar _
| lctxTy', lctxTerm', @LamWF.ofLam _ _ argTy bodyTy body H => @WF.ofLam
    (Valuation.ofLamValuation lval)
    (fun n => (lctxTy' n).interp lval.ilVal.tyVal) lctxTerm'
    argTy body (LamSort.interp lval.ilVal.tyVal argTy) (LamSort.interp lval.ilVal.tyVal bodyTy)
    (LamWF.interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H))
    (LamTerm.check_of_LamWF _ (@LamWF.ofLam _ _ argTy bodyTy body H))
    (fun t' =>
      let hWF := LamTerm.wf_of_lamWF lval (pushLCtx argTy lctxTy') (pushLCtxDep (rty:=lctxTy') t' lctxTerm') H
      Eq.mp (congrArg _ (eq_of_heq (
        congr_arg₂_heq _ (
          fun lctxTy lctxTerm => Judgement.mk lctxTy lctxTerm _ _ _
        ) (funext (fun _ => pushLCtx.comm _ _ _ _)) (pushLCtxDep.absorb _ _)
      ))) hWF)
| _,       _, @LamWF.ofApp _ _ _ resTy _ _ Hfn Harg =>
  let WFfn := LamTerm.wf_of_lamWF _ _ _ Hfn
  let WFarg := LamTerm.wf_of_lamWF _ _ _ Harg
  WF.ofApp _ _ _ _ WFfn WFarg

section Example

  private def BaseValuationEx₁ : BaseValuation :=
    ⟨fun _ => GLift Nat, fun _ => GLift Prop, fun _ => GLift Prop, fun _ => GLift Prop,
     fun n => EqLift.default _, fun n => ForallLift.default _, fun n => ExistLift.default _⟩
  
  private def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  private def interpEx₁.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .lam (.atom 0) (.app (.atom 0) (.atom 0) (.bvar 0)),
     GLift.{1, u} Nat → GLift.{1, u} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  private def valuation₁.{u} : Valuation.{u} :=
    ⟨BaseValuationEx₁,
     fun _ => GLift.{1, u} Nat → GLift.{1, u} Nat,
     fun _ => Nat.succLift⟩

  private def wf₁.{u} : WF valuation₁.{u} interpEx₁.{u} := by
    apply WF.ofLam
    case HChk =>
      apply @LamTerm.check.ofLam.{u}
        valuation₁ (fun _ => Sort u) (LamTerm.app _ (LamTerm.atom 0) (LamTerm.bvar 0))
        (GLift.{1, u} Nat) (.atom 0)
      dsimp [LamSort.interp, Auto.Embedding.Lam.valuation₁]
      dsimp [Auto.Embedding.Lam.BaseValuationEx₁]
      apply LamTerm.check.ofApp.{u}
      case fnch => apply LamTerm.check.ofAtom
      case argch => apply LamTerm.check.ofBVar
    case H =>
      intro t
      apply WF.ofApp
      case Hfn =>
        apply WF.ofAtom
      case Harg =>
        apply WF.ofBVar

  -- Original: Nat.add 2 3
  -- Lifting to: GLift.up (Nat.add 2 3)
  private def Nat.addLift.{u} (x y : GLift.{1, u} Nat) :=
    GLift.up (Nat.add (GLift.down x) (GLift.down y))

  private def interpEx₂.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .app (.atom 1) (.app (.atom 1) (.atom 0) (.atom 1)) (.atom 2),
      GLift.{1, u} Nat, GLift.up (Nat.add 2 3)⟩

  private def valuation₂.{u} : Valuation.{u} :=
    ⟨BaseValuationEx₁,
     fun n => [GLift.{1, u} Nat → GLift.{1, u} Nat → GLift.{1, u} Nat,
               GLift.{1, u} Nat, GLift.{1, u} Nat].getD n (GLift.{1, u} Nat),
     fun n =>
       match n with
       | 0 => Nat.addLift
       | 1 => GLift.up 2
       | 2 => GLift.up 3
       | _ + 3 => GLift.up 0⟩
  
  private def wf₂.{u} : WF valuation₂.{u} interpEx₂.{u} := by
    apply WF.ofApp (val:=valuation₂) (.atom 1) _ (Nat.addLift (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg =>
      apply WF.ofAtom

  -- Original: @Eq Nat 2 3
  -- Lifting to: GLift.up (@Eq Nat 2 3)
  -- **Note**: Sometimes we might want to lift to universe `u + 1`
  --   to avoid universe level issues.
  private def interpEx₃.{u} : Judgement.{u + 1} :=
    ⟨fun _ => Type u, fun _ => Sort u, .app (.atom 1) (.app (.atom 1) (.atom 0) (.atom 1)) (.atom 2), Type u, GLift (2 = 3)⟩
  
  private def valuation₃.{u} : Valuation.{u + 1} :=
    ⟨BaseValuationEx₁,
    fun n => [GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat → Type u,
              GLift.{1, u + 1} Nat,
              GLift.{1, u + 1} Nat].getD n (GLift.{1, u + 1} Nat),
    fun n =>
      match n with
      | 0 => fun a b => GLift (a.down = b.down)
      | 1 => GLift.up 2
      | 2 => GLift.up 3
      | _ + 3 => GLift.up 0⟩

  private def wf₃.{u} : WF valuation₃.{u} interpEx₃.{u} := by
    apply WF.ofApp
      (val:=valuation₃) (.atom 1) _
      (fun (b : GLift.{1, u + 1} Nat) => GLift (2 = b.down))
    case Hfn =>
      apply WF.ofApp (val:=valuation₃) (.atom 1) _ (fun (a b : GLift Nat) => GLift (a.down = b.down)) <;> apply WF.ofAtom
    case Harg => apply WF.ofAtom

end Example

def LamTerm.mapBVarAt (idx : Nat) (f : Nat → Nat) (t : LamTerm) : LamTerm :=
  match t with
  | .atom n       => .atom n
  | .base b       => .base b
  | .bvar n       => .bvar (mapAt idx f n)
  | .lam s t      => .lam s (t.mapBVarAt (.succ idx) f)
  | .app s fn arg => .app s (fn.mapBVarAt idx f) (arg.mapBVarAt idx f)

def LamTerm.mapBVar := LamTerm.mapBVarAt 0

def LamWF.ofMapBVarAt (covP : covPair f restore) (idx : Nat)
  {lamVarTy lctx} (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨lctx, rterm, rty⟩) →
  LamWF lamVarTy ⟨restoreAt idx restore lctx, rterm.mapBVarAt idx f, rty⟩
| .ofAtom n => .ofAtom n
| .ofBase b => .ofBase b
| .ofBVar n => covPairAt.ofCovPair covP idx lctx n ▸ .ofBVar (mapAt idx f n)
| .ofLam (body:=body) bodyTy wfBody =>
  .ofLam bodyTy (restoreAt.succ_pushLCtx_Fn restore _ _ _ ▸ LamWF.ofMapBVarAt covP (.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  .ofApp argTy' (LamWF.ofMapBVarAt covP idx _ HFn) (LamWF.ofMapBVarAt covP idx _ HArg)

theorem LamWF.ofMapBVarAt.correct (lval : LamValuation.{u}) {restoreDep : _}
  (covPD : covPairDep (LamSort.interp lval.ilVal.tyVal) f restore restoreDep) (idx : Nat)
  {lctxTy : Nat → LamSort} (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) :
  (rterm : LamTerm) → (HWF : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, rterm, rTy⟩) →
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (restoreAt idx restore lctxTy)
    (restoreAtDep idx restoreDep lctxTerm)
    (ofMapBVarAt (restore:=restore) covPD.left idx rterm HWF)
| .atom _, .ofAtom _ => rfl
| .base _, .ofBase _ => rfl
| .bvar n, .ofBVar _ => by
  dsimp [ofMapBVarAt, LamWF.interp]
  apply eq_of_heq
  apply HEq.trans (b := LamWF.interp lval
    (restoreAt idx restore lctxTy) (restoreAtDep idx restoreDep lctxTerm)
    (ofBVar (mapAt idx f n)))
  case h.h₁ =>
    dsimp [LamWF.interp]
    apply HEq.symm; apply (covPairDepAt.ofCovPairDep covPD).right
  case h.h₂ =>
    apply LamWF.interp.heq <;> rfl
| .lam argTy body, .ofLam bodyTy wfBody => by
  apply funext; intros x
  dsimp [LamWF.interp]
  apply Eq.trans (b := LamWF.interp lval
    (restoreAt (.succ idx) restore (pushLCtx argTy lctxTy))
    (restoreAtDep (.succ idx) restoreDep (pushLCtxDep x lctxTerm))
    (ofMapBVarAt (restore:=restore) covPD.left (.succ idx) _ wfBody))
  case h.h₁ =>
    apply LamWF.ofMapBVarAt.correct _ covPD _ _ _ wfBody
  case h.h₂ =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq => apply restoreAt.succ_pushLCtx_Fn
    case h.HLCtxTermEq => apply restoreAtDep.succ_pushLCtxDep_Fn
| .app s fn arg, .ofApp _ wfFn wfArg => by
  dsimp [LamWF.interp]
  let IHFn := LamWF.ofMapBVarAt.correct lval covPD idx lctxTerm fn wfFn
  let IHArg := LamWF.ofMapBVarAt.correct lval covPD idx lctxTerm arg wfArg
  rw [IHFn]; rw [IHArg]

-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (?n + lvl)`
def LamTerm.bvarLiftsIdx (idx lvl : Nat) := LamTerm.mapBVarAt idx (fun x => Nat.add x lvl)

@[reducible] def LamTerm.bvarLifts := LamTerm.bvarLiftsIdx 0

-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (Nat.succ ?n)`
def LamTerm.bvarLiftIdx (idx : Nat) (t : LamTerm) := LamTerm.bvarLiftsIdx idx 1 t

def LamTerm.bvarLiftsIdx.zero (idx : Nat) : (t : LamTerm) → LamTerm.bvarLiftsIdx idx 0 t = t
| .atom n => rfl
| .base b => rfl
| .bvar n => by
  dsimp [bvarLiftsIdx, mapBVarAt]
  rw [mapAt_id_eq_id']; rfl
| .lam s t => by
  dsimp [bvarLiftsIdx, mapBVarAt];
  have IH := LamTerm.bvarLiftsIdx.zero (.succ idx) t
  dsimp [bvarLiftsIdx] at IH
  rw [IH]
| .app s fn arg => by
  dsimp [bvarLiftsIdx, mapBVarAt];
  have IHFn := LamTerm.bvarLiftsIdx.zero idx fn
  have IHArg := LamTerm.bvarLiftsIdx.zero idx arg
  dsimp [bvarLiftsIdx] at IHFn IHArg
  rw [IHFn];
  rw [IHArg];

def LamTerm.bvarLiftsIdx.succ_l (idx lvl : Nat) (t : LamTerm) :
  LamTerm.bvarLiftsIdx idx (.succ lvl) t = LamTerm.bvarLiftsIdx idx lvl (LamTerm.bvarLiftIdx idx t) := by
  revert idx lvl
  induction t <;> intros idx lvl
  case atom a => rfl
  case base b => rfl
  case bvar n =>
    dsimp [bvarLiftsIdx, bvarLiftIdx, mapBVarAt];
    have hAddAt := addAt.succ_r lvl idx n
    dsimp [addAt] at hAddAt; rw [hAddAt]
  case lam s t IH =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IH
    rw [IH]; rfl
  case app fn arg IHFn IHArg =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IHFn IHArg;
    rw [IHFn, IHArg]; rfl

def LamTerm.bvarLiftsIdx.succ_r (idx lvl : Nat) (t : LamTerm) :
  LamTerm.bvarLiftsIdx idx (.succ lvl) t = LamTerm.bvarLiftIdx idx (LamTerm.bvarLiftsIdx idx lvl t) := by
  revert idx lvl
  induction t <;> intros idx lvl
  case atom a => rfl
  case base b => rfl
  case bvar n =>
    dsimp [bvarLiftsIdx, bvarLiftIdx, mapBVarAt];
    have hAddAt := addAt.succ_l lvl idx n
    dsimp [addAt] at hAddAt; rw [hAddAt];
  case lam s t IH =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IH
    rw [IH]; rfl
  case app fn arg IHFn IHArg =>
    dsimp [bvarLiftsIdx, mapBVarAt];
    dsimp [bvarLiftsIdx] at IHFn IHArg;
    rw [IHFn, IHArg]; rfl

def LamWF.ofBVarLiftsIdx
  {lamVarTy lctx} {idx lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxsAt xs idx lctx, rterm.bvarLiftsIdx idx lvl, rTy⟩ :=
  LamWF.ofMapBVarAt (covPair.ofPushsPops _ _ heq) idx rterm HWF

theorem LamWF.ofBVarLiftsIdx.correct
  (lval : LamValuation.{u}) {idx lvl : Nat}
  {tys : List LamSort} (xs : HList (LamSort.interp lval.ilVal.tyVal) tys) (heq : tys.length = lvl)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  (rterm : LamTerm) (HWF : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxsAt tys idx lctxTy) (pushLCtxsAtDep xs idx lctxTerm)
    (ofBVarLiftsIdx heq rterm HWF) :=
  LamWF.ofMapBVarAt.correct lval (covPairDep.ofPushsDepPopsDep _ _ heq) idx lctxTerm rterm HWF

def LamWF.ofBVarLiftIdx {lamVarTy lctx} (idx : Nat)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxAt s idx lctx, rterm.bvarLiftIdx idx, rTy⟩ :=
  LamWF.ofMapBVarAt (covPair.ofPushPop _) idx rterm HWF

theorem LamWF.ofBVarLiftIdx.correct
  (lval : LamValuation.{u}) {idx : Nat}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.ilVal.tyVal xty)
  (rterm : LamTerm) (HWF : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxAt xty idx lctxTy) (pushLCtxAtDep x idx lctxTerm)
    (ofBVarLiftIdx idx rterm HWF) :=
  LamWF.ofMapBVarAt.correct lval (covPairDep.ofPushDepPopDep _) idx lctxTerm rterm HWF

def LamThmWF
  (lval : LamValuation) (lctx : List LamSort) (rty : LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamWF lval.ilVal.toLamTyVal ⟨pushLCtxs lctx lctx', t, rty⟩

def LamThmWFP (lval : LamValuation) (lctx : List LamSort) (rty : LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), Nonempty (LamWF lval.ilVal.toLamTyVal ⟨pushLCtxs lctx lctx', t, rty⟩)

def LamThmValid (lval : LamValuation) (lctx : List LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort),
    ∃ (wf : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxs lctx lctx', t, .base .prop⟩),
    ∀ (lctxTerm : ∀ n, (pushLCtxs lctx lctx' n).interp lval.ilVal.tyVal),
      GLift.down (LamWF.interp lval (pushLCtxs lctx lctx') lctxTerm wf)

@[reducible] def dfLCtxTy : Nat → LamSort := fun _ => .base .prop

@[reducible] def dfLCtxTerm (val : Nat → Type u) : ∀ n, LamSort.interp val (dfLCtxTy n) :=
  fun _ => GLift.up.{1, u} False

theorem LamThmWFP.ofLamThmWF (H : LamThmWF lval lctx s t) :
  LamThmWFP lval lctx s t :=
  fun lctx => Nonempty.intro (H lctx)

theorem LamThmWF.ofLamThmWFP (H : LamThmWFP lval lctx s t) :
  LamThmWF lval lctx s t := by
  intro lctx'; cases h₁ : LamTerm.lamCheck? lval.ilVal.toLamTyVal (pushLCtxs lctx lctx') t
  case none =>
    apply False.elim; have ⟨wf⟩ := H lctx'
    have hChk := LamTerm.lamCheck?_of_lamWF wf
    rw [h₁] at hChk; cases hChk
  case some s' =>
    cases h₂ : s'.beq s
    case false =>
      apply False.elim; have ⟨wf⟩ := H lctx'
      have hChk := LamTerm.lamCheck?_of_lamWF wf
      rw [h₁] at hChk; rw [Option.some.inj hChk] at h₂
      rw [LamSort.beq_refl] at h₂; cases h₂
    case true =>
      rw [LamSort.beq_eq _ _ h₂] at h₁
      apply LamWF.ofLamCheck? h₁

def LamThmWF.append (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (lctx ++ ex) rty t := by
  dsimp [LamThmWF]; intros lctx'; rw [pushLCtxs.append]; apply H

def LamThmWF.prepend (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (ex ++ lctx) rty (t.bvarLifts ex.length) := by
  dsimp [LamThmWF]; intros lctx';
  rw [pushLCtxs.append]; rw [← pushLCtxsAt.zero ex]
  apply LamWF.ofBVarLiftsIdx (idx:=0); rfl; apply H

theorem LamThmWF.ofLamCheck?
  {lval : LamValuation} {lctx : List LamSort} {rty : LamSort} {t : LamTerm}
  (h₁ : LamTerm.lamCheck? lval.ilVal.toLamTyVal (pushLCtxs lctx dfLCtxTy) t = .some rty)
  (h₂ : t.maxLooseBVarSucc ≤ lctx.length) : LamThmWF lval lctx rty t := by
  intros lctx'; apply LamWF.ofLamCheck?; apply Eq.trans _ h₁
  apply LamTerm.lamCheck?_irrelevence; intro n hlt; dsimp [pushLCtxs]
  have hlt' : n < List.length lctx := Nat.le_trans hlt h₂
  have htrue : Nat.blt n (List.length lctx) = true := by
    rw [Nat.blt_eq]; exact hlt'
  rw [htrue]; dsimp;
  rw [List.getD_eq_get _ _ hlt']; rw [List.getD_eq_get _ _ hlt']

theorem LamThmWF.ofLamThmValid (H : LamThmValid lval lctx t) :
  LamThmWF lval lctx (.base .prop) t :=
  LamThmWF.ofLamThmWFP (fun lctx => let ⟨wf, _⟩ := H lctx; Nonempty.intro wf)

theorem LamThmValid.append (H : LamThmValid lval lctx t)
  (ex : List LamSort) : LamThmValid lval (lctx ++ ex) t := by
  dsimp [LamThmValid]; intros lctx'; let ⟨wft, Ht⟩ := H (pushLCtxs ex lctx')
  exists (pushLCtxs.append _ _ _ ▸ wft); intros lctxTerm
  let Ht' := Ht (pushLCtxs.append _ _ _ ▸ lctxTerm)
  apply Eq.mp _ Ht'; apply congr_arg (f:=GLift.down)
  apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
  case h.HLCtxTyEq => apply Eq.symm; apply pushLCtxs.append
  case h.HLCtxTermEq => apply eqRec_heq'

theorem LamThmValid.prepend (H : LamThmValid lval lctx t)
  (ex : List LamSort) : LamThmValid lval (ex ++ lctx) (t.bvarLifts ex.length) := by
  dsimp [LamThmValid]; intros lctx'; let ⟨wft, Ht⟩ := H lctx'
  let wft' := @LamWF.ofBVarLiftsIdx _ _ _ 0 _ ex rfl _ wft
  rw [pushLCtxsAt.zero, ← pushLCtxs.append] at wft'; exists wft'
  intros lctxTerm;
  let lctxTerm₁ : (n : ℕ) → LamSort.interp lval.ilVal.tyVal (pushLCtxs lctx lctx' n) :=
    fun n => pushLCtxs.append_add _ _ _ _  rfl _ ▸ lctxTerm (n + ex.length)
  let Ht' := Ht lctxTerm₁
  apply Eq.mp _ Ht'; apply congr_arg (f:=GLift.down)
  let Hl := HList.ofFun lctxTerm ex.length
  let Hl' : HList (LamSort.interp lval.ilVal.tyVal) ex := by
    rw [pushLCtxs.append] at Hl; rw [List.ofFun.ofPushLCtx] at Hl;
    exact Hl; rfl
  apply Eq.trans _ (Eq.trans (@LamWF.ofBVarLiftsIdx.correct
    _ _ 0 _ ex Hl' rfl _ lctxTerm₁ _ wft) _)
  case _ => rfl
  case _ =>
    apply eq_of_heq; apply LamWF.interp.heq <;> try rfl
    case h.HLCtxTyEq =>
      rw [pushLCtxsAt.zero]; rw [pushLCtxs.append]
    case h.HLCtxTermEq =>
      apply HEq.trans _ (pushsDep_popsDep_eq (lvl:=ex.length) _)
      apply HEq.trans (pushLCtxsAtDep.zero _ _)
      apply HEq.funext; intro n;
      apply pushLCtxsDep.heq <;> try rfl
      case H.h₃ =>
        rw [pushLCtxs.append]; rw [List.ofFun.ofPushLCtx]; rfl
      case H.h₄ =>
        dsimp;
        apply HEq.trans (cast_heq _ _) _
        apply cast_heq
      case H.h₅ =>
        apply HEq.funext; intro n;
        rw [pushLCtxs.append]; rw [covPair.ofPushsPops]; rfl
      case H.h₆ =>
        apply HEq.funext; intro n; apply eqRec_heq'

-- Only accepts propositions `p` without loose bound variables
theorem LamThmValid.ofInterpAsProp
  (lval : LamValuation) (p : LamTerm)
  (h₁ : LamTerm.lamCheck? lval.ilVal.toLamTyVal dfLCtxTy p = .some (.base .prop))
  (h₂ : (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down)
  (h₃ : p.maxLooseBVarSucc = 0) : LamThmValid lval [] p := by
  intros lctx';
  have h₁' := Eq.trans (LamTerm.lamCheck?_irrelevence (lctx₁:=lctx') (by
    intro n hlt; rw [h₃] at hlt; cases hlt)) h₁
  have wf := LamWF.ofLamCheck? h₁'; exists wf; intros lctxTerm
  apply Eq.mp _ h₂
  apply congrArg; apply eq_of_heq;
  apply HEq.trans (LamTerm.interpAsProp.equiv _ _ _ _ (LamTerm.lamCheck.equiv _ h₁))
  case _ =>
    apply HEq.trans _ (LamWF.interp_irrelevance
      (lctxTy₁:=dfLCtxTy) (lctxTerm₁:=dfLCtxTerm _) _ _ _)
    case _ =>
      apply LamThmWF.ofLamCheck? (lctx:=[]) _ _ dfLCtxTy
      rw [pushLCtxs.nil, h₁]
      rw [h₃]; exact .refl
    case _ => apply HEq.symm; apply LamTerm.interp.equiv
    case _ => intros n h; rw [h₃] at h; cases h

end Auto.Embedding.Lam