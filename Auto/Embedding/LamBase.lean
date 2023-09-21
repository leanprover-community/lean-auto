import Lean
import Auto.Embedding.Lift
import Auto.Embedding.LCtx
import Auto.Lib.ExprExtra
import Auto.Lib.NatExtra
import Auto.Lib.IntExtra
import Auto.Lib.HEqExtra
import Auto.Lib.ListExtra
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.BitVec.Defs
-- import Mathlib.Data.Int.Basic
import Auto.MathlibEmulator

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.Embedding.Lam

-- Interpreted sorts
inductive LamBaseSort
  | prop : LamBaseSort             -- GLift `prop`
  | int  : LamBaseSort             -- GLift `int`
  | real : LamBaseSort             -- GLift `real`
  | bv   : (n : Nat) → LamBaseSort -- GLift `bv n`
deriving Hashable, Inhabited, Lean.ToExpr

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

def LamBaseSort.toString : LamBaseSort → String
| .prop => "Prop"
| .int  => "Int"
| .real => "Real"
| .bv n => s!"Bitvec {n}"

instance : ToString LamBaseSort where
  toString := LamBaseSort.toString

def LamBaseSort.beq : LamBaseSort → LamBaseSort → Bool
| .prop, .prop => true
| .int,  .int  => true
| .real, .real => true
| .bv n, .bv m => n == m
| _,     _     => false

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
deriving Inhabited, Hashable, Lean.ToExpr

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

def LamSort.toString : LamSort → String
| .atom n => s!"#{n}"
| .base b => s!"{b}"
| .func s1 s2 => s!"({LamSort.toString s1} → {LamSort.toString s2})"

instance : ToString LamSort where
  toString := LamSort.toString

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

-- Given `a` and `[ty₀, ty₁, ⋯, tyᵢ₋₁]`, return `ty₀ → ty₁ → ⋯ → tyᵢ₋₁ → a`
def LamSort.mkFuncs (a : LamSort) (tys : List LamSort) : LamSort :=
  tys.foldr (fun s cur => .func s cur) a

theorem LamSort.mkFuncs_nil : LamSort.mkFuncs a .nil = a := rfl

theorem LamSort.mkFuncs_singleton : LamSort.mkFuncs a [ty] = .func ty a := rfl

theorem LamSort.mkFuncs_cons : LamSort.mkFuncs a (ty :: tys) = .func ty (.mkFuncs a tys) := rfl

theorem LamSort.mkFuncs_append : LamSort.mkFuncs a (tys₁ ++ tys₂) = .mkFuncs (.mkFuncs a tys₂) tys₁ := by
  induction tys₁
  case nil => rfl
  case cons ty₁ tys₁ IH =>
    rw [List.cons_append, mkFuncs_cons, mkFuncs_cons, IH]

theorem LamSort.mkFuncs_append_singleton : LamSort.mkFuncs a (tys ++ [ty]) = .mkFuncs (.func ty a) tys := by
  rw [LamSort.mkFuncs_append, LamSort.mkFuncs_singleton]

-- Given `a` and `[ty₀, ty₁, ⋯, tyᵢ₋₁]`, return `tyᵢ₋₁ → ⋯ → ty₁ → ty₀ → a`
def LamSort.mkFuncsRev (a : LamSort) (tys : List LamSort) : LamSort :=
  tys.foldl (fun cur s => .func s cur) a

theorem LamSort.mkFuncsRev_nil : LamSort.mkFuncsRev a .nil = a := rfl

theorem LamSort.mkFuncsRev_cons : LamSort.mkFuncsRev a (ty :: tys) = .mkFuncsRev (.func ty a) tys := rfl

theorem LamSort.mkFuncsRev_eq : LamSort.mkFuncsRev a tys = LamSort.mkFuncs a tys.reverse := by
  induction tys generalizing a
  case nil => rfl
  case cons ty tys IH =>
    rw [mkFuncsRev_cons, List.reverse_cons, mkFuncs_append_singleton, IH]

theorem LamSort.mkFuncs_eq : LamSort.mkFuncs a tys = LamSort.mkFuncsRev a tys.reverse := by
  conv => enter [1, 2]; rw [← List.reverse_reverse tys]
  apply Eq.symm mkFuncsRev_eq

-- Given `ty₀ → ty₁ → ⋯ → tyᵢ₋₁ → a`, return `[ty₀, ty₁, ⋯, tyᵢ₋₁]`
def LamSort.getArgTys : LamSort → List LamSort
| .atom _ => .nil
| .base _ => .nil
| .func argTy resTy => argTy :: getArgTys resTy

-- Given `ty₀ → ty₁ → ⋯ → tyᵢ₋₁ → a`, return `a`
def LamSort.getResTy : LamSort → LamSort
| .atom n => .atom n
| .base b => .base b
| .func _ resTy => resTy.getResTy

theorem LamSort.getArgTys_getResTy_eq :
  {s : LamSort} → .mkFuncs s.getResTy s.getArgTys = s
| .atom _ => rfl
| .base _ => rfl
| .func _ resTy => congrArg _ (@getArgTys_getResTy_eq resTy)

@[reducible] def LamSort.interp.{u} (val : Nat → Type u) : LamSort → Type u
| .atom n => val n
| .base b => b.interp
| .func dom cod => interp val dom → interp val cod

def LamSort.curry (f : HList (LamSort.interp tyVal) tys → LamSort.interp tyVal s) :
  LamSort.interp tyVal (s.mkFuncs tys) :=
  match tys with
  | .nil => f .nil
  | .cons _ _ => fun x => LamSort.curry (fun xs => f (.cons x xs))

def LamSort.curryRev (f : HList (LamSort.interp tyVal) tys → LamSort.interp tyVal s) :
  LamSort.interp tyVal (s.mkFuncsRev tys) :=
  match tys with
  | .nil => f .nil
  | .cons _ tys => LamSort.curryRev (tys:=tys) (fun xs x => f (.cons x xs))

-- Representable real numbers
inductive CstrReal
  | zero    : CstrReal
  | one     : CstrReal
deriving Inhabited, Hashable, Lean.ToExpr

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

def CstrReal.beq : CstrReal → CstrReal → Bool
| .zero, .zero => true
| .one,  .one  => true
| _,     _     => false

theorem CstrReal.beq_refl : (c : CstrReal) → (c.beq c) = true
| .zero => rfl
| .one  => rfl

theorem CstrReal.beq_eq (c₁ c₂ : CstrReal) : c₁.beq c₂ → c₁ = c₂ := by
  intro h; cases c₁ <;> cases c₂ <;> try cases h <;> rfl

def CstrReal.interp : (c : CstrReal) → Real
| zero => 0
| one  => 1

-- Interpreted constants
-- Note that `eq`, `forallE`, `existE` have `ilVal/lamILTy`
--   associated with them. During proof reconstruction, we should collect
--   the sort arguments of all `eq, forallE, existE` that occurs in the
--   proof into `ilVal`.
-- For `ilVal`, we need to use `ILLift.ofIsomTy` to construct
--   `ILLift` structures. The idea is that we want the interpretation
--   of reified assumptions to be definitionally
--   equal to the assumption (or `GLift.up` applied to the assumption, to
--   be precise), so we'll have to use the specially designed
--   `of(Eq/Forall/Exist)Lift` function.
-- Note that at the end of the proof, we'll have a `LamTerm.base .falseE`,
--   no `=, ∀, ∃` left, so whatever `(Eq/Forall/Exist)Lift`
--   structure are within the `(eq/forall/lam)Val`, the final result
--   will always interpret to `GLift.up False`.
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
deriving Inhabited, Hashable, Lean.ToExpr

def LamBaseTerm.isInt : LamBaseTerm → Bool
| .intVal _ => true
| _         => false

def LamBaseTerm.isRealVal : LamBaseTerm → Bool
| .realVal _ => true
| _          => false

def LamBaseTerm.isBvVal : LamBaseTerm → Bool
| .bvVal _ => true
| _        => false

def LamBaseTerm.isEqI : LamBaseTerm → Bool
| .eqI _ => true
| _      => false

def LamBaseTerm.isForallEI : LamBaseTerm → Bool
| .forallEI _ => true
| _           => false

def LamBaseTerm.isExistEI : LamBaseTerm → Bool
| .existEI _ => true
| _          => false

def LamBaseTerm.isEq : LamBaseTerm → Bool
| .eq _ => true
| _     => false

def LamBaseTerm.isForallE : LamBaseTerm → Bool
| .forallE _ => true
| _          => false

def LamBaseTerm.isExistE : LamBaseTerm → Bool
| .existE _ => true
| _         => false

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
    | .forallE s  => f!".forallE {LamSort.reprPrec s 1}"
    | .existE s   => f!".existE {LamSort.reprPrec s 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamBaseTerm" ++ s
  else
    f!"({s})"

instance : Repr LamBaseTerm where
  reprPrec := LamBaseTerm.reprPrec

def LamBaseTerm.toString : LamBaseTerm → String
| .trueE      => "True"
| .falseE     => "False"
| .not        => "¬"
| .and        => "∧"
| .or         => "∨"
| .imp        => "→"
| .iff        => "↔"
| .intVal n   => s!"{n} : Int"
| .realVal cr => s!"{CstrReal.reprPrec cr 1} : Real"
| .bvVal l    => s!"{l} : Bitvec {l.length}"
| .eqI _      => "="
| .forallEI _ => "∀"
| .existEI _  => "∃"
| .eq _       => "="
| .forallE _  => "∀"
| .existE _   => "∃"

instance : ToString LamBaseTerm where
  toString := LamBaseTerm.toString

def LamBaseTerm.beq : LamBaseTerm → LamBaseTerm → Bool
| .trueE,       .trueE       => true
| .falseE,      .falseE      => true
| .not,         .not         => true
| .and,         .and         => true
| .or,          .or          => true
| .imp,         .imp         => true
| .iff,         .iff         => true
| .intVal n₁,   .intVal n₂   => Int.beq n₁ n₂
| .realVal cr₁, .realVal cr₂ => cr₁.beq cr₂
| .bvVal l₁,    .bvVal l₂    => l₁.beq l₂
| .eqI n₁,      .eqI n₂      => n₁.beq n₂
| .forallEI n₁, .forallEI n₂ => n₁.beq n₂
| .existEI n₁,  .existEI n₂  => n₁.beq n₂
| .eq s₁,       .eq s₂       => s₁.beq s₂
| .forallE s₁,  .forallE s₂  => s₁.beq s₂
| .existE s₁,   .existE s₂   => s₁.beq s₂
| _,            _            => false

def LamBaseTerm.beq_refl (b : LamBaseTerm) : (b.beq b) = true := by
  cases b <;> first | rfl | apply LamSort.beq_refl | apply Nat.beq_refl | skip
  case intVal i => apply Int.beq_refl
  case realVal c => apply CstrReal.beq_refl
  case bvVal s => apply List.beq_refl Bool.beq_refl

def LamBaseTerm.beq_eq (b₁ b₂ : LamBaseTerm) (H : b₁.beq b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> (first | contradiction | rfl | apply congrArg) <;>
    (try apply LamSort.beq_eq _ _ H) <;> (try apply Nat.eq_of_beq_eq_true H)
  case intVal.intVal.h n₁ n₂ => apply Int.beq_eq _ _ H
  case realVal.realVal.h c₁ c₂ => apply CstrReal.beq_eq _ _ H
  case bvVal.bvVal.h v₁ v₂ => apply List.beq_eq Bool.beq_eq _ _ H

structure LamTyVal where
  lamVarTy     : Nat → LamSort
  lamILTy      : Nat → LamSort
  lamEVarTy    : Nat → LamSort

instance : Inhabited LamTyVal where
  default := let func := fun _ => .atom 0; ⟨func, func, func⟩

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
  let s := ltv.lamILTy n
  .func s (.func s (.base .prop))
| .forallEI n =>
  let s := ltv.lamILTy n
  .func (.func s (.base .prop)) (.base .prop)
| .existEI n  =>
  let s := ltv.lamILTy n
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
  | ofEqI n      : LamWF ltv (.eqI n) (.func (ltv.lamILTy n) (.func (ltv.lamILTy n) (.base .prop)))
  | ofForallEI n : LamWF ltv (.forallEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
  | ofExistEI n  : LamWF ltv (.existEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
  | ofEq s       : LamWF ltv (.eq s) (.func s (.func s (.base .prop)))
  | ofForallE s  : LamWF ltv (.forallE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofExistE s   : LamWF ltv (.existE s) (.func (.func s (.base .prop)) (.base .prop))

def LamBaseTerm.LamWF.unique {ltv : LamTyVal} {b : LamBaseTerm} {s₁ s₂ : LamSort}
  (lbwf₁ : LamWF ltv b s₁) (lbwf₂ : LamWF ltv b s₂) : s₁ = s₂ ∧ HEq lbwf₁ lbwf₂ := by
  cases lbwf₁ <;> cases lbwf₂ <;> trivial

def LamBaseTerm.LamWF.eVarIrrelevance
  (hLamVarTy : ltv₁.lamVarTy = ltv₂.lamVarTy)
  (hLamILTy : ltv₁.lamILTy = ltv₂.lamILTy)
  (lbwf : LamWF ltv₁ b s) : LamWF ltv₂ b s := by
  cases b <;> cases lbwf <;> (try constructor) <;> cases ltv₁ <;> cases ltv₂ <;>
    cases hLamVarTy <;> cases hLamILTy <;> constructor

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

def LamBaseTerm.lamWF_complete (wf : LamWF ltv b s) : LamWF.ofLamBaseTerm ltv b = ⟨s, wf⟩ := by
  cases wf <;> rfl

def LamBaseTerm.lamCheck_of_LamWF (H : LamWF ltv b s) : b.lamCheck ltv = s := by
  cases H <;> rfl

def LamBaseTerm.LamWF.ofCheck (H : b.lamCheck ltv = s) : LamWF ltv b s := by
  cases H; cases b <;> constructor

structure ILLift (β : Type u) where
  eqL     : EqLift.{u + 1, u} β
  forallL : ForallLift.{u + 1, u, 0, 0} β
  existL  : ExistLift.{u + 1, u} β

def ILLift.ofIsomTy {α : Sort u} {β : Type v} (I : IsomType α β) : ILLift β :=
  ⟨EqLift.ofIsomTy I, ForallLift.ofIsomTy I, ExistLift.ofIsomTy I⟩

def ILLift.default (β : Type u) : ILLift β :=
  ⟨EqLift.default β, ForallLift.default β, ExistLift.default β⟩

structure LamValuation extends LamTyVal where
  tyVal    : Nat → Type u
  varVal   : ∀ (n : Nat), (lamVarTy n).interp tyVal
  ilVal    : ∀ (n : Nat), ILLift.{u} ((lamILTy n).interp tyVal)
  eVarVal  : ∀ (n : Nat), (lamEVarTy n).interp tyVal

def LamBaseTerm.interp (lval : LamValuation.{u}) : (b : LamBaseTerm) → (b.lamCheck lval.toLamTyVal).interp lval.tyVal
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
| .eqI n      => (lval.ilVal n).eqL.eqF
| .forallEI n => (lval.ilVal n).forallL.forallF
| .existEI n  => (lval.ilVal n).existL.existF
| .eq s       => @eqLiftFn (s.interp lval.tyVal)
| .forallE s  => @forallLiftFn (s.interp lval.tyVal)
| .existE s   => @existLiftFn (s.interp lval.tyVal)

def LamBaseTerm.LamWF.interp (lval : LamValuation.{u}) : (lwf : LamWF lval.toLamTyVal b s) → s.interp lval.tyVal
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
| .ofEqI n      => (lval.ilVal n).eqL.eqF
| .ofForallEI n => (lval.ilVal n).forallL.forallF
| .ofExistEI n  => (lval.ilVal n).existL.existF
| .ofEq s       => @eqLiftFn (s.interp lval.tyVal)
| .ofForallE s  => @forallLiftFn (s.interp lval.tyVal)
| .ofExistE s   => @existLiftFn (s.interp lval.tyVal)

theorem LamBaseTerm.LamWF.interp_heq (lval : LamValuation.{u})
  (lwf₁ : LamWF lval.toLamTyVal b₁ s₁)
  (lwf₂ : LamWF lval.toLamTyVal b₂ s₂)
  (HBeq : b₁ = b₂) : HEq (LamWF.interp lval lwf₁) (LamWF.interp lval lwf₂) := by
  cases HBeq;
  cases LamWF.unique lwf₁ lwf₂
  case intro seq lweq =>
    cases seq; cases lweq; apply HEq.rfl

theorem LamBaseTerm.LamWF.interp_lvalIrrelevance
  (lval₁ lval₂ : LamValuation.{u})
  (lwf₁ : LamWF lval₁.toLamTyVal b₁ s₁)
  (lwf₂ : LamWF lval₂.toLamTyVal b₂ s₂)
  (HBeq : b₁ = b₂)
  (hTyVal : lval₁.tyVal = lval₂.tyVal)
  (hLamILTy : lval₁.lamILTy = lval₂.lamILTy)
  (hILVal : HEq lval₁.ilVal lval₂.ilVal) :
  HEq (LamWF.interp lval₁ lwf₁) (LamWF.interp lval₂ lwf₂) := by
  cases HBeq
  cases lval₁
  case mk toLamTyVal₁ tyVal₁ varVal₁ ilVal₁ eVarVal₁ =>
    cases toLamTyVal₁
    case mk lamVarTy₁ lamILTy₁ lamEVarTy₁ =>
      cases lval₂
      case mk toLamTyVal₂ tyVal₂ varVal₂ ilVal₂ eVarVal₂ =>
        cases toLamTyVal₂
        case mk lamVarTy₂ lamILTy₂ lamEVarTy₂ =>
          dsimp at varVal₁ ilVal₁ eVarVal₁ lwf₁ varVal₂ ilVal₂ eVarVal₂ lwf₂
          dsimp at hTyVal hLamILTy hILVal;
          cases hTyVal; cases hLamILTy; cases hILVal
          cases lwf₁ <;> cases lwf₂ <;> dsimp [interp] <;> apply HEq.rfl

def LamBaseTerm.interp_equiv (lval : LamValuation.{u})
  (lwf : LamWF lval.toLamTyVal b s) :
  HEq (LamWF.interp lval lwf) (interp lval b) := by
  cases lwf <;> rfl

def LamValuation.insertEVarAt (lval : LamValuation.{u})
  (ty : LamSort) (val : ty.interp lval.tyVal) (pos : Nat) :=
  {lval with lamEVarTy := replaceAt ty pos lval.lamEVarTy,
             eVarVal := replaceAtDep val pos lval.eVarVal}

theorem LamTyVal.insertEVarAt_eVarIrrelevance
  {ltv₁ : LamTyVal} (H : n < pos) :
  let ltv₂ := {ltv₁ with lamEVarTy := replaceAt ty pos ltv₁.lamEVarTy}
  ltv₁.lamEVarTy n = ltv₂.lamEVarTy n := by
  dsimp [replaceAt]
  cases h : Nat.beq n pos
  case true =>
    dsimp; cases Nat.eq_of_beq_eq_true h;
    have H' := (Nat.not_le).mpr H; apply False.elim (H' _); apply Nat.le_refl
  case false => rfl

theorem LamValuation.insertEVarAt_eVarIrrelevance
  {lval₁ : LamValuation.{u}} {val} (H : n < pos) :
  let lval₂ := lval₁.insertEVarAt ty val pos;
  lval₁.lamEVarTy n = lval₂.lamEVarTy n ∧ HEq (lval₁.eVarVal n) (lval₂.eVarVal n) := by
  dsimp [insertEVarAt, replaceAt, replaceAtDep]
  cases h : Nat.beq n pos
  case true =>
    dsimp; cases Nat.eq_of_beq_eq_true h;
    have H' := (Nat.not_le).mpr H; apply False.elim (H' _); apply Nat.le_refl
  case false => apply And.intro rfl HEq.rfl

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
| .lam _ t => t.size +1
| .app _ t₁ t₂ => t₁.size + t₂.size

-- Check whether the term contains loose bound variables `idx` levels
--   above local context root
def LamTerm.hasLooseBVarEq (idx : Nat) : LamTerm → Bool
| .atom _ => false
| .etom _ => false
| .base _ => false
| .bvar n => idx.beq n
| .lam _ t => t.hasLooseBVarEq (.succ idx)
| .app _ t₁ t₂ => t₁.hasLooseBVarEq idx || t₂.hasLooseBVarEq idx

-- Check whether the term contains loose bound variables greater
--   or equal to `idx` levels above local context root
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
    let h' := Nat.succ_le_succ h
    apply IH.mpr; rw [Nat.succ_pred] at h'; exact h'
    revert h; cases (maxLooseBVarSucc t)
    case zero => intro h; cases h
    case succ _ => intro _; simp
| .app _ t₁ t₂ => by
  dsimp [hasLooseBVarGe, maxLooseBVarSucc];
  rw [Bool.or_eq_true]; rw [spec m t₁]; rw [spec m t₂];
  simp [Nat.max]; rw [Nat.gt_eq_succ_le]; rw [Nat.gt_eq_succ_le]; rw [Nat.gt_eq_succ_le];
  rw [Nat.le_max_iff]

def LamTerm.maxEVarSucc : LamTerm → Nat
| .atom _ => 0
| .etom n => .succ n
| .base _ => 0
| .bvar _ => 0
| .lam _ t => t.maxEVarSucc
| .app _ t₁ t₂ => Nat.max t₁.maxEVarSucc t₂.maxEVarSucc

def LamTerm.mkImp (t₁ t₂ : LamTerm) : LamTerm :=
  .app (.base .prop) (.app (.base .prop) (.base .imp) t₁) t₂

def LamTerm.mkEq (s : LamSort) (t₁ t₂ : LamTerm) : LamTerm :=
  .app s (.app s (.base (.eq s)) t₁) t₂

def LamTerm.mkForallE (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.forallE s)) p

def LamTerm.mkForallEF (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.forallE s)) (.lam s p)

def LamTerm.mkExistE (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.existE s)) p

def LamTerm.mkExistEF (s : LamSort) (p : LamTerm) : LamTerm :=
  .app (.func s (.base .prop)) (.base (.existE s)) (.lam s p)

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

def LamTerm.mkLamFN (t : LamTerm) : List LamSort → LamTerm
| .nil => t
| .cons s lctx => (LamTerm.lam s t).mkLamFN lctx

theorem LamTerm.mkLamFN_append :
  mkLamFN t (l₁ ++ l₂) = mkLamFN (mkLamFN t l₁) l₂ := by
  induction l₁ generalizing t
  case nil => rfl
  case cons s l₁ IH =>
    rw [List.cons_append]; dsimp [mkLamFN]; apply IH

theorem LamTerm.mkLamFN_append_singleton :
  mkLamFN t (l₁ ++ [s]) = .lam s (mkLamFN t l₁) := by
  rw [mkLamFN_append]; rfl

def LamTerm.mkForallEFN (t : LamTerm) : List LamSort → LamTerm
| .nil => t
| .cons s lctx => (LamTerm.mkForallEF s t).mkForallEFN lctx

theorem LamTerm.mkForallEFN_append :
  mkForallEFN t (l₁ ++ l₂) = mkForallEFN (mkForallEFN t l₁) l₂ := by
  induction l₁ generalizing t
  case nil => rfl
  case cons s l₁ IH =>
    rw [List.cons_append]; dsimp [mkForallEFN]; apply IH

theorem LamTerm.mkForallEFN_append_singleton :
  mkForallEFN t (l₁ ++ [s]) = mkForallEF s (mkForallEFN t l₁) := by
  rw [mkForallEFN_append]; rfl

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

theorem LamTerm.maxEVarSucc_getAppArgsAux
  (hs : HList (fun (_, arg) => arg.maxEVarSucc ≤ n) args) (ht : t.maxEVarSucc ≤ n) :
  HList (fun (_, arg) => arg.maxEVarSucc ≤ n) (LamTerm.getAppArgsAux args t) := by
  induction t generalizing args <;> try exact hs
  case app s fn arg IHFn IHArg =>
    dsimp [maxEVarSucc] at ht; rw [Nat.max_le] at ht
    exact IHFn (.cons ht.right hs) ht.left

def LamTerm.getAppArgs := getAppArgsAux []

theorem LamTerm.maxEVarSucc_getAppArgs :
  HList (fun (_, arg) => arg.maxEVarSucc ≤ t.maxEVarSucc) (LamTerm.getAppArgs t) :=
  LamTerm.maxEVarSucc_getAppArgsAux .nil (Nat.le_refl _)

theorem LamTerm.appFn_appArg_eqAux (args : List (LamSort × LamTerm)) (t : LamTerm) :
  LamTerm.mkAppN t args = LamTerm.mkAppN t.getAppFn (t.getAppArgsAux args) := by
  induction t generalizing args <;> try rfl
  case app s _ arg IHFn _ => apply IHFn ((s, arg) :: args)

theorem LamTerm.appFn_appArg_eq (t : LamTerm) : t = LamTerm.mkAppN t.getAppFn t.getAppArgs := appFn_appArg_eqAux [] t

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

def LamTerm.reprPrec (t : LamTerm) (n : Nat) :=
  let s :=
    match t with
    | .atom m => f!".atom {m}"
    | .etom m => f!".etom {m}"
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

theorem LamTerm.beq_refl (t : LamTerm) : (t.beq t = true) := by
  induction t <;> dsimp [beq] <;> try apply Nat.beq_refl
  case base b => apply LamBaseTerm.beq_refl
  case lam s t IH => rw [LamSort.beq_refl, IH]; rfl
  case app s fn arg IHFn IHArg =>
    rw [LamSort.beq_refl, IHFn, IHArg]; rfl

theorem LamTerm.beq_eq (t₁ t₂ : LamTerm) : (t₁.beq t₂ = true) → t₁ = t₂ := by
  induction t₁ generalizing t₂ <;> intro H <;> cases t₂ <;> try cases H
  case atom.atom n₁ n₂ => apply congrArg _ (Nat.eq_of_beq_eq_true H)
  case etom.etom n₁ n₂ => apply congrArg _ (Nat.eq_of_beq_eq_true H)
  case base.base b₁ b₂ => apply congrArg _ (LamBaseTerm.beq_eq _ _ H)
  case bvar.bvar n₁ n₂ => apply congrArg _ (Nat.eq_of_beq_eq_true H)
  case lam.lam s₁ t₁ IH s₂ t₂ =>
    dsimp [beq] at H; rw [Bool.and_eq_true] at H
    have seq := LamSort.beq_eq _ _ H.left
    have teq := IH _ H.right
    rw [seq, teq]
  case app.app s₁ fn₁ arg₁ IHFn IHArg s₂ fn₂ arg₂ =>
    dsimp [beq] at H; rw [Bool.and_eq_true] at H; rw [Bool.and_eq_true] at H
    let seq := LamSort.beq_eq _ _ H.left.left
    let fneq := IHFn _ H.left.right
    let argeq := IHArg _ H.right
    rw [seq, fneq, argeq]

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
      apply Nat.not_eq_zero_of_lt hlt
  case app s fn arg IHFn IHArg =>
    rw [IHFn]; rw [IHArg];
    intros n hlt; rw [hirr n (Nat.le_trans hlt (Nat.le_max_right _ _))]
    intros n hlt; rw [hirr n (Nat.le_trans hlt (Nat.le_max_left _ _))]

-- Judgement. `lamVarTy, lctx ⊢ term : type?`
-- We put `rterm` before `rty` to avoid dependent elimination failure
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

def LamWF.unique {ltv : LamTyVal} :
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
    apply Nat.not_eq_zero_of_lt hlt
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
  (eVarIrrelevance hLamVarTy hLamILTy (fun n H => hirr _ (Nat.le_trans H (Nat.le_max_left _ _))) HFn)
  (eVarIrrelevance hLamVarTy hLamILTy (fun n H => hirr _ (Nat.le_trans H (Nat.le_max_right _ _))) HArg)

def LamWF.mkEq {ltv : LamTyVal}
  (wft₁ : LamWF ltv ⟨lctx, t₁, s⟩) (wft₂ : LamWF ltv ⟨lctx, t₂, s⟩) :
  LamWF ltv ⟨lctx, .mkEq s t₁ t₂, .base .prop⟩ :=
  LamWF.ofApp _ (LamWF.ofApp _ (.ofBase (.ofEq _)) wft₁) wft₂

theorem LamWF.mkEq_sortEq (hwf : LamWF ltv ⟨lctx, .app s' (.app s'' (.base (.eq s)) t₁) t₂, rty⟩) :
  s' = s ∧ s'' = s ∧ rty = .base .prop :=
  match hwf with
  | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) _) _ => And.intro rfl (And.intro rfl rfl)

def LamWF.getAtom {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .atom n, s⟩) : ltv.lamVarTy n = s :=
  match wft with
  | .ofAtom _ => rfl

def LamWF.getEtom {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .etom n, s⟩) : ltv.lamEVarTy n = s :=
  match wft with
  | .ofEtom _ => rfl

def LamWF.getBase {ltv : LamTyVal}
  (wft : LamWF ltv ⟨lctx, .base b, s⟩) : LamBaseTerm.LamWF ltv b s :=
  match wft with
  | .ofBase H => H

def LamWF.getBVar {ltv : LamTyVal}
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

def LamWF.mkForallE {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .func s (.base .prop)⟩) :
  LamWF ltv ⟨lctx, .mkForallE s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofForallE _)) wfp

def LamWF.mkForallEF {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtx s lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkForallEF s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ wfp)

def LamWF.mkLamFN {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtxs ls lctx, p, s⟩) :
  LamWF ltv ⟨lctx, .mkLamFN p ls, LamSort.mkFuncsRev s ls⟩ :=
  match ls with
  | .nil => wfp
  | .cons s ls => by
    dsimp [LamTerm.mkLamFN]; rw [pushLCtxs_cons] at wfp
    apply LamWF.mkLamFN (ls:=ls); apply LamWF.ofLam _ wfp

def LamWF.mkForallEFN {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtxs ls lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkForallEFN p ls, .base .prop⟩ :=
  match ls with
  | .nil => wfp
  | .cons s ls => by
    dsimp [LamTerm.mkForallEFN]; rw [pushLCtxs_cons] at wfp
    apply LamWF.mkForallEFN (ls:=ls); apply LamWF.mkForallEF wfp

def LamWF.mkExistE {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨lctx, p, .func s (.base .prop)⟩) :
  LamWF ltv ⟨lctx, .mkExistE s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofExistE _)) wfp

def LamWF.mkExistEF {ltv : LamTyVal}
  (wfp : LamWF ltv ⟨pushLCtx s lctx, p, .base .prop⟩) :
  LamWF ltv ⟨lctx, .mkExistEF s p, .base .prop⟩ := LamWF.ofApp _ (.ofBase (.ofExistE _)) (.ofLam _ wfp)

def LamWF.ofAtom' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : ltv.lamVarTy n = s) : LamWF ltv ⟨lctx, .atom n, s⟩ := by
  rw [← heq]; apply LamWF.ofAtom

def LamWF.ofBVar' {ltv : LamTyVal} {lctx : Nat → LamSort} (n : Nat)
  (s : LamSort) (heq : lctx n = s) : LamWF ltv ⟨lctx, .bvar n, s⟩ := by
  rw [← heq]; apply LamWF.ofBVar

def LamWF.getAppFn (wfAppN : LamWF ltv ⟨lctx, .mkAppN fn args, rty⟩) :
  (fnTy : LamSort) × LamWF ltv ⟨lctx, fn, fnTy⟩ :=
  match args with
  | .nil => ⟨rty, wfAppN⟩
  | .cons _ args =>
    let ⟨_, .ofApp _ HFn _⟩ := getAppFn (args:=args) wfAppN
    ⟨_, HFn⟩

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
        dsimp; rw [← List.reverseAux, List.reverseAux_eq]
        rw [pushLCtxs_lt (by rw [List.length_append]; apply Nat.le_trans exlt (Nat.le_add_right _ _))]
        dsimp [List.getD]; rw [List.get?_append exlt];
        rw [List.get?_reverse _ (by dsimp [List.length]; apply Nat.le_refl _)]
        dsimp [List.length]; simp
      conv => enter [2, 3]; rw [tyeq]
      exact .ofBVar _)

private def LamWF.bvarAppsRev_Aux :
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
  | @LamWF.ofEtom _ lctx m =>
    if n == 0 then
      f!"Auto.Embedding.Lam.LamWF.ofEtom (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofEtom {m})"
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
| lctx, .etom n => .some ⟨ltv.lamEVarTy n, .ofEtom n⟩
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

-- Of course `ofLamTerm` is sound with respect to `LamWF`. So, we
--   only need to show that it's complete
def LamWF.complete {ltv : LamTyVal} :
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

def LamTerm.lamCheck?_of_lamWF
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

-- This function is meant to be `execute`-d (`eval`-ed), not `reduce`-d
-- **TODO**: Change type to `match` so that we don't need `rw`.
--   But do not delete this, because it shows problems (proof not fully reducing)
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
    have heq' : ty₁ = argTy := LamSort.beq_eq _ _ heq; cases heq'
    cases heqa : LamSort.beq ty₁ s <;> try (intro contra; cases contra)
    cases LamSort.beq_eq _ _ heqa
    apply LamWF.ofApp (argTy:=s) (ofLamCheck? CheckFnEq) (ofLamCheck? CheckArgEq)
  | .some (LamSort.func _ _), .none => intro contra; cases contra
  | .some (LamSort.atom _), _ => intro contra; cases contra
  | .some (LamSort.base _), _ => intro contra; cases contra
  | .none, _ => intro contra; cases contra

-- Interpreting while typechecking a `λ` term. If the term fails to
--   typecheck at some point, return `⟨.base .prop, GLift.up False⟩`
--   as a default value.
def LamTerm.interp.{u} (lval : LamValuation.{u}) (lctxTy : Nat → LamSort) :
  (t : LamTerm) → (s : LamSort) ×
    ((lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) → s.interp lval.tyVal)
| .atom n => ⟨lval.lamVarTy n, fun _ => lval.varVal n⟩
| .etom n => ⟨lval.lamEVarTy n, fun _ => lval.eVarVal n⟩
| .base b =>
  ⟨b.lamCheck lval.toLamTyVal,
    fun _ => LamBaseTerm.interp lval b⟩
| .bvar n => ⟨lctxTy n, fun lctxTerm => lctxTerm n⟩
| .lam s body =>
  match LamTerm.interp lval (pushLCtx s lctxTy) body with
  | ⟨bodyTy, bodyInterp⟩ =>
    ⟨.func s bodyTy, fun lctxTerm (x : s.interp lval.tyVal) =>
      bodyInterp (pushLCtxDep (rty:=lctxTy) x lctxTerm)⟩
| .app s fn arg =>
  match LamTerm.interp lval lctxTy fn with
  | ⟨fnTy, fnInterp⟩ =>
    match LamTerm.interp lval lctxTy arg with
    | ⟨argTy, argInterp⟩ =>
      match fnTy with
      | .atom _ => ⟨.base .prop, fun _ => GLift.up False⟩
      | .base _ => ⟨.base .prop, fun _ => GLift.up False⟩
      | .func argTy' resTy =>
        match heq : LamSort.beq argTy' argTy, heqa : LamSort.beq argTy' s with
        | true, true =>
          have heq' := LamSort.beq_eq _ _ heq;
          ⟨resTy, fun lctxTerm => (fnInterp lctxTerm) (heq' ▸ argInterp lctxTerm)⟩
        | true,  false => ⟨.base .prop, fun _ => GLift.up False⟩
        | false, true  => ⟨.base .prop, fun _ => GLift.up False⟩
        | false, false => ⟨.base .prop, fun _ => GLift.up False⟩

def LamTerm.interpAsProp.{u}
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort)
  (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) (t : LamTerm) : GLift.{1, u} Prop :=
  match t.interp lval lctxTy with
  | ⟨.base .prop, tInterp⟩ => tInterp lctxTerm
  | _ => GLift.up False

def LamWF.interp.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (lwf : LamWF lval.toLamTyVal ⟨lctxTy, t, rty⟩) → rty.interp lval.tyVal
| _,      _       , .ofAtom n => lval.varVal n
| _,      _       , .ofEtom n => lval.eVarVal n
| _,      _       , .ofBase H => LamBaseTerm.LamWF.interp lval H
| lctxTy, lctxTerm, .ofBVar n => lctxTerm n
| lctxTy, lctxTerm, @LamWF.ofLam _ _ argTy _ body H =>
  fun (x : argTy.interp lval.tyVal) =>
    LamWF.interp lval (pushLCtx argTy lctxTy) (pushLCtxDep (rty:=lctxTy) x lctxTerm) H
| lctxTy, lctxTerm, .ofApp _ HFn HArg =>
  let mfn := LamWF.interp lval lctxTy lctxTerm HFn
  let marg := LamWF.interp lval lctxTy lctxTerm HArg
  mfn marg

theorem LamWF.interp_eq (lval : LamValuation.{u})
  {lctxTerm₁ : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy n).interp lval.tyVal}
  (HLCtxTermEq : HEq lctxTerm₁ lctxTerm₂)
  (lwf₁ : LamWF lval.toLamTyVal ⟨lctxTy, t₁, rty⟩)
  (lwf₂ : LamWF lval.toLamTyVal ⟨lctxTy, t₂, rty⟩)
  (HTeq : t₁ = t₂) :
  LamWF.interp lval lctxTy lctxTerm₁ lwf₁ = LamWF.interp lval lctxTy lctxTerm₂ lwf₂ := by
  cases HTeq; cases HLCtxTermEq;
  have HUniq := LamWF.unique lwf₁ lwf₂
  rcases HUniq with ⟨⟨⟩, ⟨⟩⟩; rfl

theorem LamWF.interp_heq (lval : LamValuation.{u})
  {lctxTy₁ lctxTy₂ : Nat → LamSort} (HLCtxTyEq : lctxTy₁ = lctxTy₂)
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval.tyVal}
  (HLCtxTermEq : HEq lctxTerm₁ lctxTerm₂)
  (lwf₁ : LamWF lval.toLamTyVal ⟨lctxTy₁, t₁, rty₁⟩)
  (lwf₂ : LamWF lval.toLamTyVal ⟨lctxTy₂, t₂, rty₂⟩)
  (HTeq : t₁ = t₂) :
  HEq (LamWF.interp lval lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval lctxTy₂ lctxTerm₂ lwf₂) := by
  cases HTeq; cases HLCtxTyEq; cases HLCtxTermEq;
  have HUniq := LamWF.unique lwf₁ lwf₂
  cases HUniq; case intro left right =>
    cases left; cases right; rfl

theorem LamTerm.interp_equiv
  (lval : LamValuation.{u}) (lctxTy : Nat → LamSort) (lwf : LamWF lval.toLamTyVal ⟨lctxTy, t, rty⟩) :
  ⟨rty, fun lctxTerm => LamWF.interp lval lctxTy lctxTerm lwf⟩ = LamTerm.interp lval lctxTy t := by
  induction t generalizing lctxTy rty <;> try (cases lwf; rfl)
  case base b =>
    let .ofBase bH := lwf; apply eq_sigma_of_heq
    case h₁ => rw [LamBaseTerm.lamCheck_of_LamWF bH]
    case h₂ =>
      apply HEq.funext; intros _; apply LamBaseTerm.interp_equiv
  case lam s t IH =>
    let .ofLam bodyTy H := lwf; apply eq_sigma_of_heq
    case h₁ => rw [← IH _ H]
    case h₂ =>
      dsimp [LamWF.interp, interp];
      apply HEq.funext; intros lctxTerm
      apply HEq.funext; intros x
      rw [← IH _ H]
  case app s fn arg IHFn IHArg =>
    let .ofApp _ HFn HArg := lwf
    dsimp [LamWF.interp, interp]
    have IHFn' := heq_of_eq_sigma (IHFn _ HFn)
    have IHArg' := heq_of_eq_sigma (IHArg _ HArg)
    revert IHFn' IHArg'
    match LamTerm.interp lval lctxTy fn with
    | ⟨fnTy, fnInterp⟩ =>
      match LamTerm.interp lval lctxTy arg with
      | ⟨argTy, argInterp⟩ =>
        dsimp; intros IHFn' IHArg'
        let ⟨fnTyEq, fnInterpEq⟩ := IHFn'
        let ⟨argTyEq, argInterpEq⟩ := IHArg'
        cases fnTyEq; cases argTyEq; cases fnInterpEq; cases argInterpEq
        dsimp; rw [LamSort.beq_refl]

-- In most use cases, we would have `b = .prop`
theorem LamWF.interp_substLCtxTerm
  {wf : LamWF lval.toLamTyVal ⟨lctxTy, t, s⟩}
  {wf' : LamWF lval.toLamTyVal ⟨lctxTy', t, s⟩}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm' : ∀ n, (lctxTy' n).interp lval.tyVal}
  (HLCtxTyEq : lctxTy = lctxTy') (HLCtxTermEq : HEq lctxTerm lctxTerm') :
  LamWF.interp lval lctxTy lctxTerm wf = LamWF.interp lval lctxTy' lctxTerm' wf' := by
  cases HLCtxTyEq; cases HLCtxTermEq; rcases (LamWF.unique wf wf') with ⟨_, ⟨⟩⟩; rfl 

-- In most use cases, we would have `b = .prop`
theorem LamWF.interp_substLCtxTerm_rec
  {wf : LamWF lval.toLamTyVal ⟨lctxTy, t, s⟩}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal}
  {lctxTerm' : ∀ n, (lctxTy' n).interp lval.tyVal}
  (HLCtxTyEq : lctxTy = lctxTy') (HLCtxTermEq : HEq lctxTerm lctxTerm') :
  LamWF.interp lval lctxTy lctxTerm wf = LamWF.interp lval lctxTy' lctxTerm' (HLCtxTyEq ▸ wf) := by
  cases HLCtxTyEq; cases HLCtxTermEq; rfl

theorem LamWF.interp_substWF
  {wf wf' : LamWF lval.toLamTyVal ⟨lctxTy, t, s⟩}
  {lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal} :
  LamWF.interp lval lctxTy lctxTerm wf = LamWF.interp lval lctxTy lctxTerm wf' :=
  LamWF.interp_substLCtxTerm rfl HEq.rfl

theorem LamWF.interp_prop_eqExists
  {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∃ (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩), GLift.down (LamWF.interp lval lctx lctxTerm wf)) =
  GLift.down (LamWF.interp lval lctx lctxTerm wf) :=
  propext (Iff.intro
    (fun ⟨wf', H'⟩ => Eq.mp (by
      apply congrArg; apply eq_of_heq; apply interp_heq <;> rfl) H')
    (fun H => ⟨wf, H⟩))

theorem LamWF.interp_prop_eqForall
  {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∀ (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩), GLift.down (LamWF.interp lval lctx lctxTerm wf)) =
  GLift.down (LamWF.interp lval lctx lctxTerm wf) :=
  propext (Iff.intro
    (fun H => H wf)
    (fun H wf => Eq.mp (by
      apply congrArg; apply eq_of_heq; apply interp_heq <;> rfl) H))

theorem LamWF.interp_atom
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .atom n, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (lval.varVal n) :=
  match wft with
  | .ofAtom _ => HEq.rfl

theorem LamWF.interp_etom
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .etom n, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (lval.eVarVal n) :=
  match wft with
  | .ofEtom _ => HEq.rfl

theorem LamWF.interp_base
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .base b, s⟩) {lctxTerm} :
  wft.interp lval lctxTy lctxTerm = wft.getBase.interp lval :=
  match wft with
  | .ofBase _ => rfl

theorem LamWF.interp_base'
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .base b, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (b.interp lval) :=
  match wft with
  | .ofBase _ => LamBaseTerm.interp_equiv _ _

theorem LamWF.interp_bvar
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .bvar n, s⟩) {lctxTerm} :
  HEq (wft.interp lval lctxTy lctxTerm) (lctxTerm n) :=
  match wft with
  | .ofBVar _ => HEq.rfl

theorem LamWF.interp_lam
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .lam argTy body, .func argTy resTy⟩) {lctxTerm} :
  wft.interp lval lctxTy lctxTerm = (fun x => wft.getLam.interp lval
    (pushLCtx argTy lctxTy) (pushLCtxDep x lctxTerm)) :=
  match wft with
  | .ofLam _ _ => rfl

theorem LamWF.interp_app
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨lctxTy, .app argTy fn arg, s⟩) {lctxTerm} :
  wft.interp lval lctxTy lctxTerm = (wft.getFn.interp lval lctxTy lctxTerm) (wft.getArg.interp lval lctxTy lctxTerm) :=
  match wft with
  | .ofApp _ _ _ => rfl

theorem LamWF.interp_bvarAppsRev
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨pushLCtxs lctxTy.reverse lctxTy', t, LamSort.mkFuncs s lctxTy⟩)
  (wfAp : LamWF lval.toLamTyVal ⟨pushLCtxs lctxTy.reverse lctxTy', t.bvarAppsRev lctxTy, s⟩)
  {valPre : HList (LamSort.interp lval.tyVal) lctxTy → LamSort.interp lval.tyVal s}
  {lctxTerm : HList (LamSort.interp lval.tyVal) lctxTy}
  {lctxTerm' : ∀ (n : Nat), (lctxTy' n).interp lval.tyVal}
  (ht : HEq (wft.interp lval _ (pushLCtxsDep lctxTerm.reverse lctxTerm')) (LamSort.curry valPre)) :
  HEq
    (LamWF.interp lval (pushLCtxs lctxTy.reverse lctxTy') (pushLCtxsDep lctxTerm.reverse lctxTerm') wfAp)
    (valPre lctxTerm) := by
  induction lctxTerm generalizing t lctxTy' lctxTerm'
  case nil =>
    apply HEq.trans _ ht; apply LamWF.interp_heq <;> rfl
  case cons lty lctxTy lterm lctxTerm IH =>
    dsimp [LamSort.mkFuncs_cons] at wft;
    rw [List.reverse_cons, pushLCtxs_append_singleton] at wft
    dsimp [LamTerm.bvarAppsRev] at wfAp
    rw [List.reverse_cons, pushLCtxs_append_singleton] at wfAp
    rw [interp_substLCtxTerm_rec (by rw [List.reverse_cons])
      (pushLCtxsDep_substxs _ _ _ (List.reverse_cons _ _) HList.reverse_cons)]
    rw [interp_substLCtxTerm_rec
      (pushLCtxs_append_singleton _ _ _) (pushLCtxsDep_append_singleton _ _ _)]
    rw [LamWF.interp_substWF (wf':=wfAp)]
    apply IH (LamWF.ofApp _ wft LamWF.bvarAppsRev_Aux)
    dsimp [interp]; apply HEq.trans (b:=LamSort.curry valPre lterm) <;> try rfl
    case h₁ =>
      apply heq_of_eq; apply congr
      case h₁ =>
        apply eq_of_heq; apply HEq.trans _ ht; apply heq_of_eq; apply interp_substLCtxTerm
        rw [List.reverse_cons, pushLCtxs_append_singleton]
        apply HEq.symm; apply HEq.trans _ (pushLCtxsDep_append_singleton _ _ _)
        apply pushLCtxsDep_substxs; rw [List.reverse_cons]; apply HList.reverse_cons
      case h₂ =>
        apply eq_of_heq; apply HEq.trans (LamWF.interp_bvar _)
        apply HEq.trans (pushLCtxsDep_ge _ (Nat.le_of_eq (List.length_reverse _)))
        rw [List.length_reverse, Nat.sub_self]; rfl

theorem LamWF.interp_bvarApps
  {lval : LamValuation.{u}}
  (wft : LamWF lval.toLamTyVal ⟨pushLCtxs (List.reverseAux tyex lctx) lctx', t, LamSort.mkFuncsRev s lctx⟩)
  (wfAp : LamWF lval.toLamTyVal ⟨pushLCtxs (List.reverseAux tyex lctx) lctx', LamTerm.bvarApps t lctx (List.length tyex), s⟩)
  {valPre : HList (LamSort.interp lval.tyVal) lctx → LamSort.interp lval.tyVal s}
  {termex : HList (LamSort.interp lval.tyVal) tyex}
  {lctxTerm : HList (LamSort.interp lval.tyVal) lctx}
  {lctxTerm' : ∀ (n : Nat), (lctx' n).interp lval.tyVal}
  (ht : HEq (wft.interp lval _ (pushLCtxsDep (HList.reverseAux termex lctxTerm) lctxTerm')) (LamSort.curryRev valPre)) :
  HEq
    (LamWF.interp lval
      (pushLCtxs (List.reverseAux tyex lctx) lctx')
      (pushLCtxsDep (lctxty:=LamSort.interp lval.tyVal) (HList.reverseAux termex lctxTerm) lctxTerm')
      wfAp)
    (valPre lctxTerm) := by
  induction lctxTerm generalizing s tyex
  case nil =>
    apply HEq.trans _ ht; apply LamWF.interp_heq <;> rfl
  case cons lty lctx lx lctxTerm IH =>
    dsimp [LamSort.mkFuncsRev] at wft
    dsimp [LamTerm.bvarApps] at wfAp; cases wfAp; case ofApp HArg HFn =>
      dsimp [interp]; apply congr_hd_heq (f₂:=fun lx =>valPre (HList.cons lx lctxTerm)) (x₂:=lx) <;> try rfl
      case h₁ =>
        apply @IH (lty::tyex) (.func lty s) wft _ (fun lctxTerm lx => valPre (.cons lx lctxTerm)) (.cons lx termex) ht
      case h₂ =>
        apply HEq.trans (LamWF.interp_bvar _);
        clear s t wft valPre ht HFn HArg IH
        dsimp [pushLCtxs, pushLCtxsDep]
        have hlt : tyex.length < (tyex.reverseAux (lty :: lctx)).length := by
          rw [List.reverseAux_eq, List.length_append, List.length_reverse];
          dsimp [List.length]; rw [Nat.add_succ]; apply Nat.succ_le_succ_iff.mpr
          apply Nat.le_add_right
        rw [Eq.mp (Eq.symm Nat.blt_eq) hlt]; dsimp
        apply HEq.trans (b:=HList.getD (lctxTerm' 0) (HList.append (termex.reverseAux .nil) (.cons lx lctxTerm)) tyex.length)
        case h₁ =>
          apply HList.getD_heq <;> try rfl
          case htys => rw [List.reverseAux_eq_append]
          case hhl => apply HList.reverseAux_eq_append
        case h₂ =>
          apply HEq.trans (HList.getD_append_right _ _ ?left) ?right <;>
            rw [List.reverseAux_eq, List.append_nil, List.length_reverse]
          case left => apply Nat.le_refl
          case right => rw [Nat.sub_self]; rfl

theorem LamWF.interp_insertEVarAt_eIdx
  {lval : LamValuation.{u}} {val : LamSort.interp lval.tyVal ty}
  (lwf : LamWF {lval.toLamTyVal with lamEVarTy := replaceAt ty pos lamEVarTy'} ⟨lctxTy, .etom pos, rty⟩)
  {lctxTerm : ∀ (n : Nat), LamSort.interp lval.tyVal (lctxTy n)}
  {eVarVal' : (n : Nat) → LamSort.interp lval.tyVal (lamEVarTy' n)} :
  let lval' := {lval with lamEVarTy := replaceAt ty pos lamEVarTy',
                          eVarVal := replaceAtDep val pos eVarVal'}
  HEq (lwf.interp lval' lctxTy lctxTerm) val := by
  cases lwf; dsimp [interp, replaceAt, replaceAtDep]; rw [Nat.beq_refl]

theorem LamWF.interp_eVarIrrelevance
  (lval₁ : LamValuation.{u}) (lval₂ : LamValuation.{u})
  {lctxTy₁ lctxTy₂ : Nat → LamSort}
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval₁.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval₂.tyVal}
  {t : LamTerm} {rty : LamSort}
  (lwf₁ : LamWF lval₁.toLamTyVal ⟨lctxTy₁, t, rty⟩)
  (lwf₂ : LamWF lval₂.toLamTyVal ⟨lctxTy₂, t, rty⟩)
  (hLamVarTy : lval₁.lamVarTy = lval₂.lamVarTy)
  (hLamILTy : lval₁.lamILTy = lval₂.lamILTy)
  (hTyVal : HEq lval₁.tyVal lval₂.tyVal)
  (hVarVal : HEq lval₁.varVal lval₂.varVal)
  (hILVal : HEq lval₁.ilVal lval₂.ilVal)
  (hLCtxTy : lctxTy₁ = lctxTy₂)
  (hLCtxTerm : HEq lctxTerm₁ lctxTerm₂)
  (hirr : ∀ n, n < t.maxEVarSucc →
    lval₁.lamEVarTy n = lval₂.lamEVarTy n ∧ HEq (lval₁.eVarVal n) (lval₂.eVarVal n)) :
  HEq (LamWF.interp lval₁ lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval₂ lctxTy₂ lctxTerm₂ lwf₂) := by
  rcases lval₁ with ⟨⟨lamVarTy₁, lamILTy₁, lamEVarTy₁⟩, tyVal₁, varVal₁, ilVal₁, eVarVal₁⟩
  rcases lval₂ with ⟨⟨lamVarTy₂, lamILTy₂, lamEVarTy₂⟩, tyVal₂, varVal₂, ilVal₂, eVarVal₂⟩
  dsimp at hLamVarTy hLamILTy hTyVal hVarVal hILVal hirr
  cases hLamVarTy; cases hLamILTy; cases hTyVal
  cases hVarVal; cases hILVal; cases hLCtxTy; cases hLCtxTerm
  case refl.refl.refl.refl.refl.refl =>
    dsimp; dsimp at varVal₁ ilVal₁ eVarVal₁ lctxTerm₁ lwf₁ eVarVal₂ lwf₂
    induction t generalizing lctxTy₁ rty <;> try (cases lwf₁; cases lwf₂; rfl)
    case etom n =>
      cases lwf₁
      have htyeq : lamEVarTy₁ n = lamEVarTy₂ n := by
        apply (hirr _ _).left; exact .refl
      dsimp at lwf₂;
      let lwf₂' := htyeq ▸ lwf₂;
      let lval₂ : LamValuation := ⟨⟨lamVarTy₁, lamILTy₁, lamEVarTy₂⟩, tyVal₁, varVal₁, ilVal₁, eVarVal₂⟩
      apply HEq.trans _ (LamWF.interp_heq (lval:=lval₂) (lwf₁ := lwf₂') rfl HEq.rfl _ rfl)
      cases lwf₂'; dsimp [interp]; apply (hirr _ _).right; exact .refl
    case base b =>
      cases lwf₁; cases lwf₂; dsimp [interp]
      apply LamBaseTerm.LamWF.interp_lvalIrrelevance <;> rfl
    case lam s t IH =>
      cases lwf₁; case ofLam bodyTy₁ H₁ =>
        cases lwf₂; case ofLam H₂ =>
          dsimp [interp]; apply HEq.funext; intro x; apply IH
          exact hirr
    case app s fn arg IHFn IHArg =>
      cases lwf₁; case ofApp HArg₁ HFn₁ =>
        cases lwf₂; case ofApp HArg₂ HFn₂ =>
          dsimp [interp]; apply congr_h_heq <;> try rfl
          case h₁ =>
            apply IHFn; intros n hlt;
            apply (hirr n (Nat.le_trans hlt (Nat.le_max_left _ _)))
          case h₂ =>
            apply IHArg; intros n hlt;
            apply (hirr n (Nat.le_trans hlt (Nat.le_max_right _ _)))

theorem LamWF.interp_lctxIrrelevance
  (lval : LamValuation.{u}) {lctxTy₁ lctxTy₂ : Nat → LamSort}
  {lctxTerm₁ : ∀ n, (lctxTy₁ n).interp lval.tyVal}
  {lctxTerm₂ : ∀ n, (lctxTy₂ n).interp lval.tyVal}
  {t : LamTerm} {rty : LamSort}
  (lwf₁ : LamWF lval.toLamTyVal ⟨lctxTy₁, t, rty⟩)
  (lwf₂ : LamWF lval.toLamTyVal ⟨lctxTy₂, t, rty⟩)
  (hirr : ∀ n, n < t.maxLooseBVarSucc → 
    lctxTy₁ n = lctxTy₂ n ∧ HEq (lctxTerm₁ n) (lctxTerm₂ n)) :
  HEq (LamWF.interp lval lctxTy₁ lctxTerm₁ lwf₁) (LamWF.interp lval lctxTy₂ lctxTerm₂ lwf₂) := by
  induction t generalizing lctxTy₁ lctxTy₂ rty <;> try (cases lwf₁; cases lwf₂; rfl)
  case base b =>
    cases lwf₁; cases lwf₂; dsimp [interp]; apply LamBaseTerm.LamWF.interp_heq <;> rfl
  case bvar n =>
    cases lwf₁; dsimp [interp]
    have htyeq : lctxTy₁ n = lctxTy₂ n := by
      apply (hirr _ _).left; exact .refl
    rw [htyeq] at lwf₂; apply HEq.trans (b:=interp _ _ lctxTerm₂ lwf₂)
    case h₁ =>
      cases lwf₂; dsimp [interp]; apply (hirr _ _).right; exact .refl
    case h₂ =>
      apply interp_heq <;> rfl
  case lam s t IH =>
    cases lwf₁; case ofLam bodyTy₁ H₁ =>
      cases lwf₂; case ofLam H₂ =>
        dsimp [interp]; apply HEq.funext; intros x; apply IH
        intros n hlt; dsimp [pushLCtx, pushLCtxDep]
        cases n
        case zero => exact And.intro rfl HEq.rfl
        case succ n =>
          apply hirr;
          apply Nat.le_pred_of_succ_le _ hlt
          apply Nat.not_eq_zero_of_lt hlt
  case app s fn arg IHFn IHArg =>
    cases lwf₁; case ofApp HArg₁ HFn₁ =>
      cases lwf₂; case ofApp HArg₂ HFn₂ =>
        dsimp [interp]; apply congr_h_heq <;> try rfl
        case h₁ =>
          apply IHFn; intros n hlt;
          apply (hirr n (Nat.le_trans hlt (Nat.le_max_left _ _)))
        case h₂ =>
          apply IHArg; intros n hlt;
          apply (hirr n (Nat.le_trans hlt (Nat.le_max_right _ _)))

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

def LamWF.ofMapBVarAt (covP : coPair f restore) (idx : Nat)
  {lamVarTy lctx} (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨lctx, rterm, rty⟩) →
  LamWF lamVarTy ⟨restoreAt idx restore lctx, rterm.mapBVarAt idx f, rty⟩
| .ofAtom n => .ofAtom n
| .ofEtom n => .ofEtom n
| .ofBase b => .ofBase b
| .ofBVar n => coPairAt.ofcoPair covP idx lctx n ▸ .ofBVar (mapAt idx f n)
| .ofLam (body:=body) bodyTy wfBody =>
  .ofLam bodyTy (restoreAt_succ_pushLCtx_Fn restore _ _ _ ▸ LamWF.ofMapBVarAt covP (.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  .ofApp argTy' (LamWF.ofMapBVarAt covP idx _ HFn) (LamWF.ofMapBVarAt covP idx _ HArg)

def LamWF.fromMapBVarAtAux
  (covP : coPair f restore) (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
  (hLCtx : lctx' = restoreAt idx restore lctx)
  (hRTerm : rterm' = rterm.mapBVarAt idx f)
  (HWF : LamWF lamVarTy ⟨lctx', rterm', rty⟩) : LamWF lamVarTy ⟨lctx, rterm, rty⟩ :=
  match rterm with
  | .atom n =>
    match HWF with
    | .ofAtom _ => by rw [LamTerm.atom.inj hRTerm]; apply ofAtom
  | .etom n =>
    match HWF with
    | .ofEtom _ => by rw [LamTerm.etom.inj hRTerm]; apply ofEtom
  | .base b =>
    match HWF with
    | .ofBase H => by rw [← LamTerm.base.inj hRTerm]; apply ofBase H
  | .bvar n =>
    match HWF with
    | .ofBVar _ => by
      rw [LamTerm.bvar.inj hRTerm, hLCtx]
      rw [coPairAt.ofcoPair covP idx lctx n]
      apply ofBVar
  | .lam argTy body =>
    match HWF with
    | .ofLam bodyTy wfBody => by
      have ⟨argTyEq, bodyEq⟩ := LamTerm.lam.inj hRTerm
      rw [argTyEq, bodyEq, hLCtx] at wfBody
      rw [← restoreAt_succ_pushLCtx_Fn restore _ _ _] at wfBody
      rw [argTyEq]; apply LamWF.ofLam bodyTy
      apply LamWF.fromMapBVarAtAux covP (.succ idx) _ rfl rfl wfBody
  | .app argTy' fn arg =>
    match HWF with
    | .ofApp _ HFn HArg =>
      have ⟨sEq, fnEq, argEq⟩ := LamTerm.app.inj hRTerm
      LamWF.ofApp argTy'
        (LamWF.fromMapBVarAtAux covP idx _ hLCtx fnEq (sEq ▸ HFn))
        (LamWF.fromMapBVarAtAux covP idx _ hLCtx argEq (sEq ▸ HArg))

def LamWF.fromMapBVarAt
  (covP : coPair f restore) (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
  (HWF : LamWF lamVarTy ⟨restoreAt idx restore lctx, rterm.mapBVarAt idx f, rty⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rty⟩ := LamWF.fromMapBVarAtAux covP idx rterm rfl rfl HWF

theorem LamWF.ofMapBVarAt.correct (lval : LamValuation.{u}) {restoreDep : _}
  (covPD : coPairDep (LamSort.interp lval.tyVal) f restore restoreDep) (idx : Nat)
  {lctxTy : Nat → LamSort} (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) :
  (rterm : LamTerm) → (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) →
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (restoreAt idx restore lctxTy)
    (restoreAtDep idx restoreDep lctxTerm)
    (ofMapBVarAt (restore:=restore) covPD.left idx rterm HWF)
| .atom _, .ofAtom _ => rfl
| .etom _, .ofEtom _ => rfl
| .base _, .ofBase _ => rfl
| .bvar n, .ofBVar _ => by
  dsimp [ofMapBVarAt, LamWF.interp]
  apply eq_of_heq; apply HEq.symm (HEq.trans (interp_bvar _) _)
  apply (coPairDepAt.ofCoPairDep covPD).right
| .lam argTy body, .ofLam bodyTy wfBody => by
  apply funext; intros x; dsimp [LamWF.interp]
  apply Eq.trans (LamWF.ofMapBVarAt.correct _ covPD (.succ idx) _ _ wfBody)
  apply LamWF.interp_substLCtxTerm_rec
  apply restoreAtDep_succ_pushLCtxDep_Fn
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

@[reducible] def LamTerm.bvarLift := LamTerm.bvarLiftIdx 0

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

def LamWF.ofBVarLiftsIdx
  {lamVarTy lctx} {idx lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxsAt xs idx lctx, rterm.bvarLiftsIdx idx lvl, rTy⟩ :=
  LamWF.ofMapBVarAt (coPair.ofPushsPops _ _ heq) idx rterm HWF

def LamWF.fromBVarLiftsIdx
  {lamVarTy lctx} {idx lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtxsAt xs idx lctx, rterm.bvarLiftsIdx idx lvl, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromMapBVarAt (coPair.ofPushsPops _ _ heq) idx rterm HWF  

theorem LamWF.ofBVarLiftsIdx.correct
  (lval : LamValuation.{u}) {idx lvl : Nat}
  {tys : List LamSort} (xs : HList (LamSort.interp lval.tyVal) tys) (heq : tys.length = lvl)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxsAt tys idx lctxTy) (pushLCtxsAtDep xs idx lctxTerm)
    (ofBVarLiftsIdx heq rterm HWF) :=
  LamWF.ofMapBVarAt.correct lval (coPairDep.ofPushsDepPopsDep _ _ heq) idx lctxTerm rterm HWF

def LamWF.ofBVarLifts
  {lamVarTy lctx} {lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxs xs lctx, rterm.bvarLifts lvl, rTy⟩ :=
  Eq.mp (by rw [pushLCtxsAt_zero]) (LamWF.ofBVarLiftsIdx (idx:=0) heq rterm HWF)

def LamWF.fromBVarLifts
  {lamVarTy lctx} {lvl : Nat}
  {xs : List LamSort} (heq : xs.length = lvl)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtxs xs lctx, rterm.bvarLifts lvl, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromBVarLiftsIdx (idx:=0) heq rterm (Eq.mp (by rw [pushLCtxsAt_zero]) HWF) 

theorem LamWF.ofBVarLifts.correct
  (lval : LamValuation.{u}) {lvl : Nat}
  {tys : List LamSort} (xs : HList (LamSort.interp lval.tyVal) tys) (heq : tys.length = lvl)
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxs tys lctxTy) (pushLCtxsDep xs lctxTerm)
    (ofBVarLifts heq rterm HWF) := by
  apply Eq.trans (LamWF.ofBVarLiftsIdx.correct (idx:=0) _ xs heq _ lctxTerm _ _)
  apply interp_substLCtxTerm; rw [pushLCtxsAt_zero]; apply pushLCtxsAtDep_zero

def LamWF.ofBVarLiftIdx {lamVarTy lctx} (idx : Nat)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtxAt s idx lctx, rterm.bvarLiftIdx idx, rTy⟩ :=
  LamWF.ofMapBVarAt (coPair.ofPushPop _) idx rterm HWF

def LamWF.fromBVarLiftIdx {lamVarTy lctx} (idx : Nat)
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtxAt s idx lctx, rterm.bvarLiftIdx idx, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromMapBVarAt (coPair.ofPushPop _) idx rterm HWF

theorem LamWF.ofBVarLiftIdx.correct
  (lval : LamValuation.{u}) {idx : Nat}
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.tyVal xty)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtxAt xty idx lctxTy) (pushLCtxAtDep x idx lctxTerm)
    (ofBVarLiftIdx idx rterm HWF) :=
  LamWF.ofMapBVarAt.correct lval (coPairDep.ofPushDepPopDep _) idx lctxTerm rterm HWF

def LamWF.ofBVarLift {lamVarTy lctx}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨pushLCtx s lctx, rterm.bvarLift, rTy⟩ :=
  Eq.mp (by rw [pushLCtxAt_zero]) (LamWF.ofBVarLiftIdx (s:=s) 0 _ HWF)

def LamWF.fromBVarLift {lamVarTy lctx}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨pushLCtx s lctx, rterm.bvarLift, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm, rTy⟩ :=
  LamWF.fromBVarLiftIdx (s:=s) 0 _ (Eq.mp (by rw [pushLCtxAt_zero]) HWF)

theorem LamWF.ofBVarLift.correct
  (lval : LamValuation.{u})
  (lctxTy : Nat → LamSort) (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal)
  {xty : LamSort} (x : LamSort.interp lval.tyVal xty)
  (rterm : LamTerm) (HWF : LamWF lval.toLamTyVal ⟨lctxTy, rterm, rTy⟩) :
  LamWF.interp lval lctxTy lctxTerm HWF = LamWF.interp lval
    (pushLCtx xty lctxTy) (pushLCtxDep x lctxTerm) (ofBVarLift rterm HWF) := by
  apply Eq.trans (LamWF.ofBVarLiftIdx.correct (idx:=0) _ _ lctxTerm x _ _)
  apply interp_substLCtxTerm; rw [pushLCtxAt_zero]; apply pushLCtxAtDep_zero

def LamWF.pushLCtxAt_ofBVar :
  LamWF lamVarTy ⟨pushLCtxAt s idx lctx, .bvar idx, s⟩ :=
  Eq.mp (by rw [pushLCtxAt_eq]) (@LamWF.ofBVar lamVarTy (pushLCtxAt s idx lctx) idx)

def LamWF.pushLCtx_ofBVar :
  LamWF lamVarTy ⟨pushLCtx s lctx, .bvar 0, s⟩ :=
  Eq.mp (by rw [pushLCtx_zero]) (@LamWF.ofBVar lamVarTy (pushLCtx s lctx) 0)

def LamThmWF
  (lval : LamValuation) (lctx : List LamSort) (rty : LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t, rty⟩

def LamThmWFP (lval : LamValuation) (lctx : List LamSort) (rty : LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), Nonempty (LamWF lval.toLamTyVal ⟨pushLCtxs lctx lctx', t, rty⟩)

abbrev LamValid (lval : LamValuation) (lctx : Nat → LamSort) (t : LamTerm) :=
  ∃ (wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩),
    ∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal), GLift.down (LamWF.interp lval lctx lctxTerm wf)

def LamThmValid (lval : LamValuation) (lctx : List LamSort) (t : LamTerm) :=
  ∀ (lctx' : Nat → LamSort), LamValid lval (pushLCtxs lctx lctx') t

theorem LamValid_substLCtxRecWF
  (lctx' : Nat → LamSort) (heq : ∀ n, lctx' n = lctx n)
  {lval : LamValuation} {wf : LamWF lval.toLamTyVal ⟨lctx, t, .base .prop⟩} :
  (∀ (lctxTerm : ∀ n, (lctx n).interp lval.tyVal), GLift.down (LamWF.interp lval lctx lctxTerm wf)) ↔
  (∀ (lctxTerm' : ∀ n, (lctx' n).interp lval.tyVal),
    GLift.down (LamWF.interp (t:=t) (rty:=.base .prop) lval lctx' lctxTerm' ((@id (lctx' = lctx) (funext heq)) ▸ wf))) := by
  cases (@id (lctx' = lctx) (funext heq)); exact Iff.intro id id

def LamNonempty (tyVal : Nat → Type u) (s : LamSort) := Nonempty (s.interp tyVal)

@[reducible] def dfLCtxTy : Nat → LamSort := fun _ => .base .prop

@[reducible] def dfLCtxTerm (val : Nat → Type u) : ∀ n, LamSort.interp val (dfLCtxTy n) :=
  fun _ => GLift.up.{1, u} False

theorem LamThmValid.getDefault (H : LamThmValid lval [] t) :
  GLift.down (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm lval.tyVal) t) := by
  have ⟨wf, H⟩ := H dfLCtxTy
  have hTermEquiv := LamTerm.interp_equiv _ dfLCtxTy wf
  dsimp [LamTerm.interpAsProp]; rw [← hTermEquiv]; apply H

theorem LamThmValid.getFalse (H : LamThmValid lval [] (.base .falseE)) : False :=
  LamThmValid.getDefault H

theorem LamThmWFP.ofLamThmWF (H : LamThmWF lval lctx s t) :
  LamThmWFP lval lctx s t :=
  fun lctx => Nonempty.intro (H lctx)

theorem LamWF.ofNonemptyLamWF (H : Nonempty (LamWF ltv ⟨lctx, t, s⟩)) :
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
      rw [LamSort.beq_eq _ _ h₂] at h₁
      apply LamWF.ofLamCheck? h₁
  
theorem LamWF.ofExistsLamWF (H : ∃ (_ : LamWF ltv ⟨lctx, t, s⟩), p) :
  LamWF ltv ⟨lctx, t, s⟩ := by
  apply LamWF.ofNonemptyLamWF; cases H; apply Nonempty.intro; assumption

theorem LamThmWF.ofLamThmWFP (H : LamThmWFP lval lctx s t) :
  LamThmWF lval lctx s t := by
  intro lctx'; apply LamWF.ofNonemptyLamWF (H lctx')

def LamThmWF.append (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (lctx ++ ex) rty t := by
  dsimp [LamThmWF]; intros lctx'; rw [pushLCtxs_append]; apply H

def LamThmWF.prepend (H : LamThmWF lval lctx rty t) (ex : List LamSort) :
  LamThmWF lval (ex ++ lctx) rty (t.bvarLifts ex.length) := by
  dsimp [LamThmWF]; intros lctx';
  rw [pushLCtxs_append]; rw [← pushLCtxsAt_zero ex]
  apply LamWF.ofBVarLiftsIdx (idx:=0); rfl; apply H

def LamTerm.lamThmWFCheck? (ltv : LamTyVal) (lctx : List LamSort) (t : LamTerm) : Option LamSort :=
  match LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t with
  | .some s =>
    match Nat.ble (t.maxLooseBVarSucc) lctx.length with
    | true => .some s
    | false => .none
  | .none => .none

theorem LamThmWF.ofLamThmWFCheck?
  {lval : LamValuation} {lctx : List LamSort} {rty : LamSort} {t : LamTerm}
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

theorem LamThmWF.ofLamThmValid (H : LamThmValid lval lctx t) :
  LamThmWF lval lctx (.base .prop) t :=
  LamThmWF.ofLamThmWFP (fun lctx => let ⟨wf, _⟩ := H lctx; Nonempty.intro wf)

theorem LamWF.interp_eqForallEF
  {wf : LamWF lval.toLamTyVal ⟨pushLCtx s lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEF wf)) = (∀ x,
    GLift.down (LamWF.interp lval (pushLCtx s lctx) (pushLCtxDep x lctxTerm) wf)) := rfl

theorem LamWF.interp_eqLamFN
  {lval : LamValuation.{u}} {lctxTerm : ∀ n, (lctx n).interp lval.tyVal}
  {wf : LamWF lval.toLamTyVal ⟨pushLCtxs ls lctx, t, s⟩} :
  LamWF.interp lval lctx lctxTerm (.mkLamFN wf) = LamSort.curryRev (fun xs =>
    LamWF.interp lval (pushLCtxs ls lctx) (pushLCtxsDep xs lctxTerm) wf) := by
  induction ls generalizing t s
  case nil => rfl
  case cons s' ls IH =>
    dsimp [LamSort.curryRev, mkLamFN]; rw [IH]
    apply congrArg; funext xs x; dsimp [interp]; apply interp_substLCtxTerm
    case HLCtxTyEq => rw [pushLCtxs_cons]
    case HLCtxTermEq => apply HEq.symm; apply pushLCtxsDep_cons

theorem LamWF.interp_eqForallEFN
  {lval : LamValuation.{u}} {lctxTerm : ∀ n, (lctx n).interp lval.tyVal}
  {wf : LamWF lval.toLamTyVal ⟨pushLCtxs ls lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEFN wf)) = (∀ xs,
    GLift.down (LamWF.interp lval (pushLCtxs ls lctx) (pushLCtxsDep xs lctxTerm) wf)) := by
  induction ls generalizing t
  case nil =>
    dsimp [mkForallEFN, interp]
    conv =>
      enter [2]; rw [IsomType.eqForall HList.nil_IsomType.{u + 1, u + 1, 0}]
      rw [PUnit.eqForall]; unfold HList.nil_IsomType; dsimp
      dsimp [pushLCtxs, pushLCtxsDep, Nat.blt, Nat.ble]
  case cons s ls IH =>
    dsimp [mkForallEFN, interp]; apply Eq.trans IH
    conv =>
      enter [2]; rw [IsomType.eqForall HList.cons_IsomType]; rw [Prod.eqForall']
      unfold HList.cons_IsomType; dsimp; enter [xs, x]
    dsimp [mkForallEF, interp, LamBaseTerm.LamWF.interp, forallLiftFn]
    apply forall_congr; intro xs; apply forall_congr; intro x
    apply congrArg; apply eq_of_heq; apply interp_heq <;> try rfl
    case HLCtxTyEq => rw [pushLCtxs_cons]
    case HLCtxTermEq => apply HEq.symm; apply pushLCtxsDep_cons

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
    GLift.down (LamWF.interp lval (pushLCtx argTy lctx) (pushLCtxDep x lctxTerm) (.ofApp _ wf.ofBVarLift .pushLCtx_ofBVar))) := by
  dsimp [interp, LamBaseTerm.LamWF.interp, forallLiftFn]
  conv => enter [2, x, 1]; rw [← ofBVarLift.correct]

theorem LamValid.revert1H (H : LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0))) :
  LamValid lval lctx (.mkForallE s t) :=
  have ⟨wfAp, ht⟩ := LamValid.revert1F H
  have .ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ (.ofApp _ wft (.ofBVar _))) := wfAp
  ⟨LamWF.mkForallE (.fromBVarLift _ wft), fun lctxTerm => by
    dsimp [LamWF.mkForallE, LamWF.interp, LamBaseTerm.LamWF.interp]; intro x
    dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, forallLiftFn] at ht
    apply Eq.mp _ (ht lctxTerm x); apply congrArg; apply congrFun
    apply Eq.trans (b := LamWF.interp lval (pushLCtx s lctx) (pushLCtxDep x lctxTerm)
      (.ofBVarLift _ (.fromBVarLift _ wft)))
    case h₁ => apply eq_of_heq; apply LamWF.interp_heq <;> rfl
    case h₂ => rw [← LamWF.ofBVarLift.correct]⟩

theorem LamThmValid.revert1H (H : LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0))) :
  LamThmValid lval lctx (.mkForallE s t) := by
  intro lctx'; have H' := H lctx'; rw [pushLCtxs_cons] at H'; apply LamValid.revert1H H'

theorem LamValid.intro1H (H : LamValid lval lctx (.mkForallE s t)) :
  LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  LamValid.intro1F (
    have ⟨wfF, hF⟩ := H
    have .ofApp _ (.ofBase (.ofForallE _)) wft := wfF
    ⟨.mkForallEF (.ofApp _ (.ofBVarLift _ wft) .pushLCtx_ofBVar), fun lctxTerm => by
      dsimp [LamWF.mkForallEF, LamWF.interp, LamBaseTerm.LamWF.interp]; intro x; dsimp
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, forallLiftFn] at hF
      apply Eq.mp _ (hF lctxTerm x); apply congrArg; rw [← LamWF.ofBVarLift.correct]⟩
  )

theorem LamThmValid.intro1H (H : LamThmValid lval lctx (.mkForallE s t)) :
  LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0)) := by
  intro lctx'; rw [pushLCtxs_cons]; apply LamValid.intro1H (H lctx')

theorem LamValid.eqForallEH : LamValid lval lctx (.mkForallE s t) ↔ LamValid lval (pushLCtx s lctx) (.app s t.bvarLift (.bvar 0)) :=
  Iff.intro LamValid.intro1H LamValid.revert1H

theorem LamThmValid.eqForallEH : LamThmValid lval lctx (.mkForallE s t) ↔ LamThmValid lval (s :: lctx) (.app s t.bvarLift (.bvar 0)) :=
  Iff.intro LamThmValid.intro1H LamThmValid.revert1H

theorem LamValid.eqForallEFN : LamValid lval lctx (.mkForallEFN t l) ↔ LamValid lval (pushLCtxs l lctx) t := by
  induction l generalizing t
  case nil => rw [pushLCtxs_nil]; rfl
  case cons s l IH =>
    dsimp [LamTerm.mkForallEFN]; rw [pushLCtxs_cons]
    rw [IH, ← LamValid.eqForallEF]

theorem LamThmValid.eqForallEFN : LamThmValid lval lctx (.mkForallEFN t l) ↔ LamThmValid lval (l ++ lctx) t :=
  Iff.intro
    (fun H lctx' => by rw [pushLCtxs_append]; exact LamValid.eqForallEFN.mp (H lctx'))
    (fun H lctx' => have H' := H lctx'; by rw [pushLCtxs_append] at H'; exact LamValid.eqForallEFN.mpr H')

theorem LamThmValid.append (H : LamThmValid lval lctx t)
  (ex : List LamSort) : LamThmValid lval (lctx ++ ex) t := by
  dsimp [LamThmValid]; intros lctx'; rw [pushLCtxs_append]; exact H (pushLCtxs ex lctx')

theorem LamValid.prepend (H : LamValid lval lctx t)
  (ex : List LamSort) : LamValid lval (pushLCtxs ex lctx) (t.bvarLifts ex.length) := by
  have ⟨wft, ht⟩ := H
  rw [← pushLCtxsAt_zero ex]; exists (LamWF.ofBVarLiftsIdx rfl _ wft)
  intro lctxTerm;
  let lctxTerm₁ := fun n => lctxTerm (n + ex.length)
  have lctxeq : ∀ (n : Nat), pushLCtxsAt ex 0 lctx (n + List.length ex) = lctx n := by
    intro n; rw [pushLCtxsAt_zero, pushLCtxs_ge, Nat.add_sub_cancel]; apply Nat.le_add_left
  have ht' := (LamValid_substLCtxRecWF _ lctxeq).mp ht lctxTerm₁
  apply Eq.mp _ ht'; apply congrArg
  let hl' : HList (LamSort.interp lval.tyVal) ex := by
    apply Eq.mp _ (HList.ofFun lctxTerm ex.length)
    rw [pushLCtxsAt_zero, List.ofFun_ofPushLCtx]; rfl
  apply Eq.trans (@LamWF.ofBVarLiftsIdx.correct _ _ 0 _ ex hl' rfl _ lctxTerm₁ _ _) _
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

-- Only accepts propositions `p` without loose bound variables
theorem LamThmValid.ofInterpAsProp
  (lval : LamValuation) (p : LamTerm)
  (h₁ : LamTerm.lamCheck? lval.toLamTyVal dfLCtxTy p = .some (.base .prop))
  (h₂ : (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down)
  (h₃ : p.maxLooseBVarSucc = 0) : LamThmValid lval [] p := by
  intros lctx';
  have h₁' := Eq.trans (LamTerm.lamCheck?_irrelevence (lctx₁:=lctx') (by
    intro n hlt; rw [h₃] at hlt; cases hlt)) h₁
  have wf₁ := LamWF.ofLamCheck? h₁'; exists wf₁; intros lctxTerm
  have wf₂ := LamWF.ofLamCheck? h₁
  have hieq := LamTerm.interp_equiv _ _ wf₂
  dsimp [LamTerm.interpAsProp] at h₂; rw [← hieq] at h₂; dsimp at h₂
  apply Eq.mp _ h₂
  apply congrArg; apply eq_of_heq;
  apply LamWF.interp_lctxIrrelevance (lctxTy₁:=dfLCtxTy) (lctxTerm₁:=dfLCtxTerm _) _ _
  intros n h; rw [h₃] at h; cases h

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

def LamThmWFD (lval : LamValuation.{u}) lctx rty t :=
  ∃ (_ : LamWF lval.toLamTyVal ⟨pushLCtxs lctx dfLCtxTy, t, rty⟩), t.maxLooseBVarSucc ≤ lctx.length

theorem LamThmWFD.ofLamThmWF (H : LamThmWF lval lctx rty t) : LamThmWFD lval lctx rty t := by
  exists (H dfLCtxTy); apply LamThmWF.maxLooseBVarSucc H

theorem LamThmWF.ofLamThmWFD (H : LamThmWFD lval lctx rty t) : LamThmWF lval lctx rty t := by
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

def LamThmValidD (lval : LamValuation.{u}) lctx t :=
  t.maxLooseBVarSucc ≤ lctx.length ∧ 
  ∃ (wf : LamWF lval.toLamTyVal ⟨pushLCtxs lctx dfLCtxTy, t, .base .prop⟩),
    ∀ (lctxTerm : HList (LamSort.interp lval.tyVal) lctx),
      (wf.interp lval _ (pushLCtxsDep lctxTerm (dfLCtxTerm _))).down

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

private def getILSortString : LamBaseTerm → String
| .eq s => s!"{s}"
| .forallE s => s!"{s}"
| .existE s => s!"{s}"
| _ => "❌"

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
    match b.beq .not with
    | true =>
      match args with
      | [(_, arg)] => s!"(¬ {toStringLCtx lctx arg})"
      | _ => "❌"
    | false =>
      match b.beq .and || b.beq .or || b.beq .imp || b.beq .iff || b.isEq || b.isEqI with
      | true =>
        match args with
        | [(_, arg)] => s!"({toStringLCtx lctx arg} {b})"
        | [(_, arg₁), (_, arg₂)] => s!"({toStringLCtx lctx arg₁} {b} {toStringLCtx lctx arg₂})"
        | _ => "❌"
      | false =>
        match b.isForallE || b.isForallEI || b.isExistE || b.isExistEI with
        | true =>
          match args with
          | [(_, arg)] =>
            match arg with
            | .lam s t => s!"({b} x{lctx} : {s}, {toStringLCtx (.succ lctx) t})"
            | arg =>
              let arg's := toStringLCtx (.succ lctx) (arg.bvarLifts 1)
              s!"({b}x{lctx} : {getILSortString b}, {arg's} x{lctx})"
          | _ => "❌"
        | false => "❌"
  | fn => "(" ++ toStringLCtx lctx fn ++ " " ++ String.intercalate " " (args.map (fun x => toStringLCtx lctx x.snd)) ++ ")"

def LamTerm.toString := LamTerm.toStringLCtx 0

instance : ToString LamTerm where
  toString := LamTerm.toString

end Auto.Embedding.Lam