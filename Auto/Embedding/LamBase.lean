import Auto.Embedding.Lift
import Auto.Embedding.LCtx
import Auto.Util.ExprExtra
import Auto.Util.SigEq
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
  | trueE   : LamBaseTerm -- Propositional `true`
  | falseE  : LamBaseTerm -- Propositional `false`
  | not     : LamBaseTerm -- Propositional `not`
  | and     : LamBaseTerm -- Propositional `and`
  | or      : LamBaseTerm -- Propositional `or`
  | imp     : LamBaseTerm -- Propositional `imp`
  | iff     : LamBaseTerm -- Propositional `iff`
  | intVal  : Int → LamBaseTerm
  | realVal : CstrReal → LamBaseTerm
  | bvVal   : List Bool → LamBaseTerm
  | eq      : Nat → LamBaseTerm -- Polymorphic `eq`
  | forallE : Nat → LamBaseTerm -- Polymorphic `forall`
  | existE  : Nat → LamBaseTerm -- Polymorphic `exist`
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
    | .eq s       => f!".eq {s}"
    | .forallE s  => f!".forallE {s}"
    | .existE s   => f!".existE {s}"
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

def LamBaseTerm.check (ltv : LamTyVal) : LamBaseTerm → LamSort
| .trueE      => .base .prop
| .falseE     => .base .prop
| .not        => .func (.base .prop) (.base .prop)
| .and        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .or         => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .imp        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .iff        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .intVal n   => .base .int
| .realVal cr => .base .real
| .bvVal ls   => .base (.bv ls.length)
| .eq n       =>
  let s := ltv.eqLamVal n
  .func s (.func s (.base .prop))
| .forallE n  =>
  let s := ltv.forallLamVal n
  .func (.func s (.base .prop)) (.base .prop)
| .existE n   =>
  let s := ltv.existLamVal n
  .func (.func s (.base .prop)) (.base .prop)

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
  | ofEq n       : LamWF ltv (.eq n) (.func (ltv.eqLamVal n) (.func (ltv.eqLamVal n) (.base .prop)))
  | ofForallE n  : LamWF ltv (.forallE n) (.func (.func (ltv.forallLamVal n) (.base .prop)) (.base .prop))
  | ofExistE n   : LamWF ltv (.existE n) (.func (.func (ltv.existLamVal n) (.base .prop)) (.base .prop))

def LamBaseTerm.LamWF.reprPrec (wf : LamBaseTerm.LamWF ltv s t) (n : Nat) :=
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
    | .ofEq s       => f!".ofEq {s}"
    | .ofForallE s  => f!".ofForallE {s}"
    | .ofExistE s   => f!".ofExistE {s}"
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
| .eq n       => ⟨.func _ (.func _ (.base .prop)), .ofEq n⟩
| .forallE n  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallE n⟩
| .existE n   => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistE n⟩

def LamBaseTerm.wf_complete (wf : LamBaseTerm.LamWF ltv b s) : LamBaseTerm.LamWF.ofLamBaseTerm ltv b = ⟨s, wf⟩ := by
  cases wf <;> rfl

def LamBaseTerm.check_of_LamWF (H : LamBaseTerm.LamWF ltv b s) : b.check ltv = s := by
  cases H <;> rfl

def LamBaseTerm.wf_of_Check (H : b.check ltv = s) : LamBaseTerm.LamWF ltv b s := by
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

def LamBaseTerm.interp (ilVal : ILValuation.{u}) : (b : LamBaseTerm) → (b.check ilVal.toLamTyVal).interp ilVal.tyVal
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
| .eq n       => (ilVal.eqVal n).eqF
| .forallE n  => (ilVal.forallVal n).forallF
| .existE n   => (ilVal.existVal n).existF

def LamBaseWF.interp (ilVal : ILValuation.{u}) : (lwf : LamBaseTerm.LamWF ilVal.toLamTyVal b s) → s.interp ilVal.tyVal
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
| .ofEq n       => (ilVal.eqVal n).eqF
| .ofForallE n  => (ilVal.forallVal n).forallF
| .ofExistE n   => (ilVal.existVal n).existF

def LamBaseTerm.interp.equiv (ilVal : ILValuation.{u})
  (lwf : LamBaseTerm.LamWF ilVal.toLamTyVal b (b.check ilVal.toLamTyVal)) :
  LamBaseWF.interp ilVal lwf = LamBaseTerm.interp ilVal b := by
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
  existTyVal : Nat → Type u
  eqVal       : ∀ (n : Nat), EqLift.{u + 1, u} (eqTyVal n)
  forallVal   : ∀ (n : Nat), ForallLift.{u + 1, u, 0, 0} (forallTyVal n)
  existVal   : ∀ (n : Nat), ExistLift.{u + 1, u} (existTyVal n)

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

inductive LamBaseTerm.WF.{u} (baseVal : BaseValuation.{u}) : LamBaseTerm.Judgement.{u} → Type u
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
  | ofEq n       : WF baseVal ⟨.eq n, baseVal.eqTyVal n → baseVal.eqTyVal n → GLift.{1, u} Prop, (baseVal.eqVal n).eqF⟩
  | ofForallE n  : WF baseVal ⟨.forallE n, (baseVal.forallTyVal n → GLift.{1, u} Prop) → GLift.{1, u} Prop, (baseVal.forallVal n).forallF⟩
  | ofExistE n   : WF baseVal ⟨.existE n, (baseVal.existTyVal n → GLift.{1, u} Prop) → GLift.{1, u} Prop, (baseVal.existVal n).existF⟩

def LamBaseTerm.wf_of_lamWF.{u} (ilVal : ILValuation.{u})
  : (lwf : LamBaseTerm.LamWF ilVal.toLamTyVal b s) →
     WF (.ofILValuation ilVal) ⟨b, s.interp ilVal.tyVal, LamBaseWF.interp ilVal lwf⟩
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
| .ofEq n       => .ofEq (baseVal:=.ofILValuation ilVal) n
| .ofForallE n  => .ofForallE (baseVal:=.ofILValuation ilVal) n
| .ofExistE n   => .ofExistE (baseVal:=.ofILValuation ilVal) n

inductive LamTerm
  | atom    : Nat → LamTerm
  | base    : LamBaseTerm → LamTerm
  | bvar    : Nat → LamTerm
  | lam     : LamSort → LamTerm → LamTerm
  | app     : LamTerm → LamTerm → LamTerm
deriving Inhabited, Hashable

def LamTerm.reprPrec (t : LamTerm) (n : Nat) :=
  let s :=
    match t with
    | .atom m => f!".atom {m}"
    | .base b => f!".base {LamBaseTerm.reprPrec b 1}"
    | .bvar m => f!".bvar {m}"
    | .lam s t => f!".lam {LamSort.reprPrec s 1} {LamTerm.reprPrec t 1}"
    | .app t₁ t₂ => f!".app {LamTerm.reprPrec t₁ 1} {LamTerm.reprPrec t₂ 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamTerm" ++ s
  else
    f!"({s})"

instance : Repr LamTerm where
  reprPrec f n := LamTerm.reprPrec f n

-- Typecheck. `ltv, lctx ⊢ term : type?`
-- `ltv`          : LamTyVal
-- `Nat → LamSort` : Local Context
def LamTerm.check? (ltv : LamTyVal) :
  (Nat → LamSort) → LamTerm → Option LamSort
| _,    .atom n  => ltv.lamVarTy n
| _,    .base b  => b.check ltv
| lctx, .bvar n  => lctx n
| lctx, .lam s t =>
  match t.check? ltv (pushLCtx lctx s) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app fn arg =>
  match fn.check? ltv lctx, arg.check? ltv lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    match ty₁.beq argTy with
    | true => .some ty₂ 
    | false => none
  | _, _ => .none

def LamTerm.check! (default : LamSort) (ltv : LamTyVal) :
  (Nat → LamSort) → LamTerm → LamSort
| _,    .atom n  => ltv.lamVarTy n
| _,    .base b  => b.check ltv
| lctx, .bvar n  => lctx n
| lctx, .lam s t => .func s (t.check! default ltv (pushLCtx lctx s))
| lctx, .app fn arg =>
  match fn.check! default ltv lctx, arg.check! default ltv lctx with
  | .func ty₁ ty₂, argTy =>
    match ty₁.beq argTy with
    | true => ty₂
    | false => default
  | _, _ => default

def LamTerm.check.equiv (default : LamSort) (ltv : LamTyVal) (lctx : Nat → LamSort) :
  (t : LamTerm) → (res : LamSort) → LamTerm.check? ltv lctx t = .some res →
  LamTerm.check! defualt ltv lctx t = res
| .atom n, _, H => Option.some.inj H
| .base b, _, H => Option.some.inj H
| .bvar n, _, H => Option.some.inj H
| .lam s t, res, H => by
  dsimp [check?] at H; revert H
  cases hCheck : (check? ltv (pushLCtx lctx s) t)
  case none => intro contra; cases contra
  case some res' =>
    intro heq;
    have heq' := Option.some.inj heq; rw [← heq']
    dsimp [check!]; congr
    apply LamTerm.check.equiv default ltv (pushLCtx lctx s) _ _ hCheck    
| .app fn arg, res, H => by
  dsimp [check?] at H; revert H
  match hCheckFn : check? ltv lctx fn, hCheckArg : check? ltv lctx arg with
  | .some resFn, .some resArg =>
    dsimp [check!];
    rw [LamTerm.check.equiv default ltv lctx _ _ hCheckFn]
    rw [LamTerm.check.equiv default ltv lctx _ _ hCheckArg]
    match resFn with
    | .atom _ => intro contra; cases contra
    | .base _ => intro contra; cases contra
    | .func argTy resTy =>
      dsimp;
      match LamSort.beq argTy resArg with
      | true => intro H; exact Option.some.inj H
      | false => intro contra; cases contra
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
      (H : LamWF ltv ⟨pushLCtx lctx argTy, body, bodyTy⟩) :
    LamWF ltv ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
  | ofApp
      {lctx : Nat → LamSort}
      (argTy : LamSort) {resTy : LamSort}
      {fn : LamTerm} {arg : LamTerm}
      (HFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩)
      (HArg : LamWF ltv ⟨lctx, arg, argTy⟩) :
    LamWF ltv ⟨lctx, .app fn arg, resTy⟩

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
  let bodyWf := @LamWF.ofLamTerm ltv (pushLCtx lctx argTy) body
  match bodyWf with
  | .some ⟨bodyTy, wf⟩ => .some ⟨.func argTy bodyTy, .ofLam bodyTy wf⟩
  | .none => .none
| lctx, .app fn arg =>
  let fnWf := @LamWF.ofLamTerm ltv lctx fn
  let argWf := @LamWF.ofLamTerm ltv lctx arg
  match fnWf, argWf with
  | .some (⟨.func ty₁ ty₂, fnWf⟩), .some ⟨argTy, argWf⟩ =>
    match heq : ty₁.beq argTy with
    | true =>
      have tyEq := LamSort.beq_eq _ _ heq
      have fnWf' := tyEq ▸ fnWf
      .some ⟨ty₂, .ofApp argTy fnWf' argWf⟩
    | false => .none
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

def LamTerm.check_of_lamWF
  {ltv : LamTyVal} {lctx : Nat → LamSort} {t : LamTerm} {ty : LamSort} :
  LamWF ltv ⟨lctx, t, ty⟩ → t.check? ltv lctx = .some ty := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rty := ty : LamJudge} = Judge 
  intro HWf; revert lctx t ty JudgeEq; induction HWf
  case ofAtom lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq]; rfl
  case ofBase lctx' b s H =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq, check?]; rw [LamBaseTerm.check_of_LamWF H]
  case ofBVar lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]; rfl
  case ofLam lctx' argTy bodyTy body H H_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq];
    simp [check?]; rw [H_ih]; rfl
  case ofApp lctx' argTy resTy fn arg HFn HArg HFn_ih HArg_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]
    simp [check?];
    rw [@HFn_ih lctx' fn (LamSort.func argTy resTy)] <;> try rfl;
    rw [@HArg_ih lctx' arg argTy] <;> try rfl;
    simp [LamSort.beq_refl]

private def List.get?_eq_some' : {l : List α} → {n : Nat} → l.get? n = some a →
  (@PSigma (n < List.length l) (fun h => List.get l ⟨n, h⟩ = a))
| a::_,  0    , eq => ⟨Nat.succ_le_succ (Nat.zero_le _), by simp at eq; exact eq⟩
| _::as, n + 1, eq => by
    simp at eq; simp;
    match @List.get?_eq_some' α a as n eq with
    | PSigma.mk h' proof' =>
      apply PSigma.mk;
      case fst => apply Nat.succ_lt_succ; exact h'
      case snd => exact proof'
| .nil, _     , eq => by simp at eq

-- This function is meant to be `execute`-d (`eval`-ed), not `reduce`-d
-- **TODO**: Change type to `match` so that we don't need `rw`.
--   But do not delete this, because it shows problems (proof not fully reducing)
def LamTerm.lamWF_of_check {ltv : LamTyVal} :
  {lctx : Nat → LamSort} → {t : LamTerm} → {ty : LamSort} →
  t.check? ltv lctx = .some ty → LamWF ltv ⟨lctx, t, ty⟩
| lctx, .atom n, ty, HCheck => by
  have HCheck' := Option.some.inj HCheck
  rw [← HCheck']; apply LamWF.ofAtom
| lctx, .base b, ty, HCheck => by
  simp [check?] at HCheck; exact LamWF.ofBase (LamBaseTerm.wf_of_Check HCheck)
| lctx, .bvar n, ty, HCheck => by
  simp [check?] at HCheck; rw [← HCheck]; apply LamWF.ofBVar
| lctx, .lam argTy body, ty, HCheck => by
  dsimp [check?] at HCheck; revert HCheck
  cases CheckEq : check? ltv (pushLCtx lctx argTy) body
  case none => intro contra; cases contra
  case some bodyTy =>
    dsimp; intro tyEq; rw [← Option.some.inj tyEq]
    apply LamWF.ofLam; apply (LamTerm.lamWF_of_check CheckEq)
| lctx, .app fn arg, ty, HCheck => by
  simp [check?] at HCheck; revert HCheck
  match CheckFnEq : check? ltv lctx fn, CheckArgEq : check? ltv lctx arg with
  | .some (LamSort.func ty₁ ty₂), .some argTy =>
    dsimp;
    cases heq : LamSort.beq ty₁ argTy
    case false => intro contra; cases contra
    case true =>
      dsimp; intro H; rw [← Option.some.inj H]; apply LamWF.ofApp (argTy:=ty₁);
      case HFn => apply (LamTerm.lamWF_of_check CheckFnEq)
      case HArg =>
        have heq' : ty₁ = argTy := LamSort.beq_eq _ _ heq
        rw [heq']
        apply (LamTerm.lamWF_of_check CheckArgEq)
  | .some (LamSort.func _ _), .none => intro contra; cases contra
  | .some (LamSort.atom _), _ => intro contra; cases contra
  | .some (LamSort.base _), _ => intro contra; cases contra
  | .none, _ => intro contra; cases contra


/-
#reduce @LamTerm.lamWF_of_check
  (ltv := {(Inhabited.default : LamTyVal) with lamVarTy := fun n => .atom 0})
  (lctx := fun _ => .atom 0)
  (t := .atom 0)
  (ty := .atom 0)
  rfl

#reduce @LamTerm.lamWF_of_check
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then .func (.atom 0) (.atom 0) else .atom 0})
  (lctx := fun _ => .atom 0)
  (t := .app (.atom 0) (.atom 1))
  (ty := .atom 0)
  rfl

#reduce @LamTerm.lamWF_of_check
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1)})
  (lctx := fun _ => .atom 0)
  (t := .lam (.atom 0) (.app (.atom 1) (.atom 0)))
  (ty := .func (.atom 0) (.atom 1))
  rfl

#eval @LamTerm.lamWF_of_check
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1)})
  (lctx := fun _ => .atom 0)
  (t := .lam (.atom 0) (.app (.atom 1) (.atom 0)))
  (ty := .func (.atom 0) (.atom 1))
  rfl
-/

structure LamValuation.{u} where
  ilVal     : ILValuation.{u}
  varVal    : ∀ (n : Nat), (ilVal.lamVarTy n).interp ilVal.tyVal

def LamTerm.interp.{u}
  (dfSort : LamSort) (lval : LamValuation.{u}) (dfVal : dfSort.interp lval.ilVal.tyVal)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) :
  (t : LamTerm) → (t.check! dfSort lval.ilVal.toLamTyVal lctxTy).interp lval.ilVal.tyVal
| .atom n => lval.varVal n
| .base b => LamBaseTerm.interp lval.ilVal b
| .bvar n => lctxTerm n
| .lam s body =>
  fun (x : s.interp lval.ilVal.tyVal) =>
    LamTerm.interp dfSort lval dfVal (pushLCtx lctxTy s) (pushLCtxDep (rty:=lctxTy) lctxTerm x) body
| .app fn arg => (fun fnInterp argInterp => by
  dsimp [check!]
  revert fnInterp argInterp
  match
    hCheck₁ : check! dfSort lval.ilVal.toLamTyVal lctxTy fn,
    hCheck₂ : check! dfSort lval.ilVal.toLamTyVal lctxTy arg with
  | .atom _, _ => intros _ _; exact dfVal
  | .base _, _ => intros _ _; exact dfVal
  | .func argTy' resTy', argTy =>
    dsimp
    match heq : LamSort.beq argTy' argTy with
    | true =>
      intros fnInterp argInterp; dsimp at fnInterp
      rw [LamSort.beq_eq _ _ heq] at fnInterp
      dsimp [LamSort.interp] at fnInterp
      exact (fnInterp argInterp)
    | false => intros _ _; exact dfVal)
  (LamTerm.interp dfSort lval dfVal lctxTy lctxTerm fn)
  (LamTerm.interp dfSort lval dfVal lctxTy lctxTerm arg)

def LamWF.interp.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (lwf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩) → rty.interp lval.ilVal.tyVal
| lctxTy, lctxTerm, .ofAtom n => lval.varVal n
| lctxTy, lctxTerm, .ofBase H => LamBaseWF.interp lval.ilVal H
| lctxTy, lctxTerm, .ofBVar n => lctxTerm n
| lctxTy, lctxTerm, @LamWF.ofLam _ _ argTy _ body H =>
  fun (x : argTy.interp lval.ilVal.tyVal) =>
    LamWF.interp lval (pushLCtx lctxTy argTy) (pushLCtxDep (rty:=lctxTy) lctxTerm x) H
| lctxTy, lctxTerm, .ofApp _ HFn HArg =>
  let mfn := LamWF.interp lval lctxTy lctxTerm HFn
  let marg := LamWF.interp lval lctxTy lctxTerm HArg
  mfn marg

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
      (α β : Type u) (fn : α → β)
      (H : ∀ (t : α), WF val ⟨pushLCtx lctxTy α, pushLCtxDep (lctxty:=id) lctxTerm t, ht, β, fn t⟩) :
    WF val <|
      ⟨lctxTy, lctxTerm, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hfn harg : LamTerm}
      (α β : Type u) (fn : α → β) (arg : α)
      (Hfn : WF val ⟨lctxTy, lctxTerm, hfn, α → β, fn⟩)
      (Harg : WF val ⟨lctxTy, lctxTerm, harg, α, arg⟩)
      :
    WF val <|
      ⟨lctxTy, lctxTerm, .app hfn harg, β, fn arg⟩

def LamTerm.wf_of_lamWF.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (lwf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, t, rty⟩) →
  WF (Valuation.ofLamValuation lval)
    ⟨fun n => (lctxTy n).interp lval.ilVal.tyVal, lctxTerm, t, rty.interp lval.ilVal.tyVal, LamWF.interp lval lctxTy lctxTerm lwf⟩
| lctxTy', lctxTerm', @LamWF.ofAtom _ _ n => WF.ofAtom _
| lctxTy', lctxTerm', @LamWF.ofBase _ _ b s H => WF.ofBase (LamBaseTerm.wf_of_lamWF lval.ilVal H)
| lctxTy', lctxTerm', @LamWF.ofBVar _ _ n => WF.ofBVar _
| lctxTy', lctxTerm', @LamWF.ofLam _ _ argTy bodyTy body H => @WF.ofLam
    (Valuation.ofLamValuation lval)
    (fun n => (lctxTy' n).interp lval.ilVal.tyVal) lctxTerm'
    argTy body (LamSort.interp lval.ilVal.tyVal argTy) (LamSort.interp lval.ilVal.tyVal bodyTy)
    (LamWF.interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H))
    (fun t' =>
      let ty₁ := fun n => LamSort.interp lval.ilVal.tyVal (pushLCtx lctxTy' argTy n)
      let ty₂ := pushLCtx (fun n => LamSort.interp lval.ilVal.tyVal (lctxTy' n)) (LamSort.interp lval.ilVal.tyVal argTy)
      let term₁ : ∀ (n : Nat), ty₁ n := pushLCtxDep (rty:=lctxTy') lctxTerm' t'
      let term₂ : ∀ (n : Nat), ty₂ n := pushLCtxDep (lctxty:=id) lctxTerm' t'
      let hTermEq : PSigmaEq (fun (α : Nat → Type _) => (∀ (n : Nat), α n)) term₁ term₂ := pushLCtxDep.absorb _ _
      let motive := fun {ty : Nat → Type u} (term : ∀ n, ty n) =>
        WF (Valuation.ofLamValuation lval)
          ⟨ty, term, body, LamSort.interp lval.ilVal.tyVal bodyTy, LamWF.interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H) t'⟩
      let hWF : motive (ty:=ty₁) term₁ := LamTerm.wf_of_lamWF lval _ _ H
      @PSigmaEq.ndrec (Nat → Type _) (fun α => (n : Nat) → α n) ty₁ term₁ motive hWF ty₂ term₂ hTermEq)
| lctxTy', lctxTerm', @LamWF.ofApp _ _ argTy resTy fn arg Hfn Harg =>
  let WFfn := LamTerm.wf_of_lamWF _ _ _ Hfn
  let WFarg := LamTerm.wf_of_lamWF _ _ _ Harg
  WF.ofApp _ _ _ _ WFfn WFarg

section Example

  private def BaseValuationEx₁ : BaseValuation :=
    ⟨fun _ => GLift Prop, fun _ => GLift Prop, fun _ => GLift Prop,
     fun _ => GLift Prop, fun n => sorry, fun n => sorry, fun n => sorry⟩
  
  private def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  private def interpEx₁.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .lam (.atom 0) (.app (.atom 0) (.bvar 0)),
     GLift.{1, u} Nat → GLift.{1, u} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  private def valuation₁.{u} : Valuation.{u} :=
    ⟨BaseValuationEx₁,
     fun _ => GLift.{1, u} Nat → GLift.{1, u} Nat,
     fun _ => Nat.succLift⟩

  private def wf₁.{u} : WF valuation₁.{u} interpEx₁.{u} := by
    apply WF.ofLam
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
    ⟨fun _ => Sort u, fun _ => PUnit, .app (.app (.atom 0) (.atom 1)) (.atom 2),
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
    apply WF.ofApp (fn := Nat.addLift (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg =>
      apply WF.ofAtom

  -- Original: @Eq Nat 2 3
  -- Lifting to: GLift.up (@Eq Nat 2 3)
  -- **Note**: Sometimes we might want to lift to universe `u + 1`
  --   to avoid universe level issues.
  private def interpEx₃.{u} : Judgement.{u + 1} :=
    ⟨fun _ => Type u, fun _ => Sort u, .app (.app (.atom 0) (.atom 1)) (.atom 2), Type u, GLift (2 = 3)⟩
  
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
    apply WF.ofApp (fn := fun (b : GLift.{1, u + 1} Nat) => GLift (2 = b.down))
    case Hfn =>
      apply WF.ofApp (fn := fun (a b : GLift Nat) => GLift (a.down = b.down)) <;> apply WF.ofAtom
    case Harg => apply WF.ofAtom

end Example

end Auto.Embedding.Lam