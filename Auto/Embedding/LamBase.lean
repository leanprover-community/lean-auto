import Lean
import Auto.Embedding.Lift
import Auto.Embedding.LCtx
import Auto.Lib.ExprExtra
import Auto.Lib.NatExtra
import Auto.Lib.IntExtra
import Auto.Lib.HEqExtra
import Auto.Lib.ListExtra
-- import Mathlib.Data.Real.Basic
import Auto.MathlibEmulator

set_option linter.unusedVariables false

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.Embedding.Lam

open ToExprExtra

/-- Interpreted sorts -/
inductive LamBaseSort
  | prop   : LamBaseSort            -- GLift `Prop`
  | bool   : LamBaseSort            -- GLift `Bool`
  | nat    : LamBaseSort            -- GLift `Nat`
  | int    : LamBaseSort            -- GLift `Int`
  /--
    For each `p : Pos`, `isto0 p` is an interpreted sort
    `p`       `isto0 p`
    .xH        String
    .xO .xH    Empty
    _          Empty
  -/
  | isto0  : Pos → LamBaseSort
  | bv     : (n : Nat) → LamBaseSort -- GLift `BitVec n`
deriving Hashable, Inhabited, Lean.ToExpr

def LamBaseSort.string := LamBaseSort.isto0 .xH

def LamBaseSort.empty := LamBaseSort.isto0 (.xO .xH)

def LamBaseSort.reprPrec (b : LamBaseSort) (n : Nat) :=
  let str :=
    match b with
    | .prop => "prop"
    | .bool => "bool"
    | .nat  => "nat"
    | .int  => "int"
    | .isto0 p =>
      match p with
      | .xH => "string"
      | _   => "empty"
    | .bv n => s!"bv {n}"
  if n == 0 then
    f!"LamBaseSort." ++ str
  else
    f!"(.{str})"

instance : Repr LamBaseSort where
  reprPrec s n := s.reprPrec n

def LamBaseSort.toString : LamBaseSort → String
| .prop   => "Prop"
| .bool   => "Bool"
| .nat    => "Nat"
| .int    => "Int"
| .isto0 p =>
  match p with
  | .xH => "String"
  | _ => "Empty"
| .bv n   => s!"BitVec {n}"

instance : ToString LamBaseSort where
  toString := LamBaseSort.toString

def LamBaseSort.beq : LamBaseSort → LamBaseSort → Bool
| .prop,     .prop     => true
| .bool,     .bool     => true
| .nat,      .nat      => true
| .int,      .int      => true
| .isto0 p₁, .isto0 p₂ => p₁.beq p₂
| .bv n,     .bv m     => n.beq m
| _,         _         => false

instance : BEq LamBaseSort where
  beq := LamBaseSort.beq

theorem LamBaseSort.beq_def {a b : LamBaseSort} : (a == b) = a.beq b := rfl

theorem LamBaseSort.beq_refl : {b : LamBaseSort} → (b.beq b) = true
| .prop    => rfl
| .bool    => rfl
| .nat     => rfl
| .int     => rfl
| .isto0 _ => Pos.beq_refl
| .bv n    => Nat.beq_refl' n

theorem LamBaseSort.eq_of_beq_eq_true {b₁ b₂ : LamBaseSort} : b₁.beq b₂ → b₁ = b₂ :=
  match b₁, b₂ with
  | .prop,    .prop    => fun _ => rfl
  | .bool,    .bool    => fun _ => rfl
  | .nat,     .nat     => fun _ => rfl
  | .int,     .int     => fun _ => rfl
  | .isto0 p, .isto0 q => fun H => Pos.eq_of_beq_eq_true H ▸ rfl
  | .bv n,    .bv m    => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .prop,    .bool    => fun H => by cases H
  | .prop,    .nat     => fun H => by cases H
  | .prop,    .int     => fun H => by cases H
  | .prop,    .isto0 p => fun H => by cases H
  | .prop,    .bv m    => fun H => by cases H
  | .bool,    .prop    => fun H => by cases H
  | .bool,    .nat     => fun H => by cases H
  | .bool,    .int     => fun H => by cases H
  | .bool,    .isto0 p => fun H => by cases H
  | .bool,    .bv m    => fun H => by cases H
  | .nat,     .prop    => fun H => by cases H
  | .nat,     .bool    => fun H => by cases H
  | .nat,     .int     => fun H => by cases H
  | .nat,     .isto0 p => fun H => by cases H
  | .nat,     .bv m    => fun H => by cases H
  | .int,     .prop    => fun H => by cases H
  | .int,     .bool    => fun H => by cases H
  | .int,     .nat     => fun H => by cases H
  | .int,     .isto0 p => fun H => by cases H
  | .int,     .bv m    => fun H => by cases H
  | .isto0 p, .prop    => fun H => by cases H
  | .isto0 p, .bool    => fun H => by cases H
  | .isto0 p, .nat     => fun H => by cases H
  | .isto0 p, .int     => fun H => by cases H
  | .isto0 p, .bv m    => fun H => by cases H
  | .bv n,    .prop    => fun H => by cases H
  | .bv n,    .bool    => fun H => by cases H
  | .bv n,    .nat     => fun H => by cases H
  | .bv n,    .int     => fun H => by cases H
  | .bv n,    .isto0 p => fun H => by cases H

instance : LawfulBEq LamBaseSort where
  eq_of_beq := LamBaseSort.eq_of_beq_eq_true
  rfl := LamBaseSort.beq_refl

@[reducible] def LamBaseSort.isto0_interp.{u} : Pos → Type u
| .xH     => GLift String
| .xO .xH => GLift Empty
| _       => GLift Empty

@[reducible] def LamBaseSort.interp.{u} : LamBaseSort → Type u
| .prop    => GLift Prop
| .bool    => GLift Bool
| .nat     => GLift Nat
| .int     => GLift Int
| .isto0 p => isto0_interp p
| .bv n    => GLift (BitVec n)

inductive LamSort
| atom : Nat → LamSort
| base : LamBaseSort → LamSort
| func : LamSort → LamSort → LamSort
deriving Inhabited, Hashable, Lean.ToExpr

def LamSort.isAtom : LamSort → Bool
| .atom _ => true
| _       => false

def LamSort.isBase : LamSort → Bool
| .base _ => true
| _       => false

def LamSort.isFunc : LamSort → Bool
| .func _ _ => true
| _         => false

def LamSort.reprPrec (s : LamSort) (n : Nat) :=
  let str :=
    match s with
    | .atom n     => f!"atom {n}"
    | .base b     => f!"base {LamBaseSort.reprPrec b 1}"
    | .func s1 s2 => f!"func {LamSort.reprPrec s1 1} {LamSort.reprPrec s2 1}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamSort." ++ str
  else
    f!"(.{str})"

instance : Repr LamSort where
  reprPrec s n := s.reprPrec n

def LamSort.toString : LamSort → String
| .atom n => s!"#{n}"
| .base b => s!"{b}"
| .func s1 s2 => s!"({LamSort.toString s1} → {LamSort.toString s2})"

instance : ToString LamSort where
  toString := LamSort.toString

def LamSort.beq : LamSort → LamSort → Bool
| .atom m,     .atom n     => m.beq n
| .base m,     .base n     => m.beq n
| .func m₁ n₁, .func m₂ n₂ => LamSort.beq m₁ m₂ && LamSort.beq n₁ n₂
| _,           _           => false

instance : BEq LamSort where
  beq := LamSort.beq

theorem LamSort.beq_def {x y : LamSort} : (x == y) = x.beq y := rfl

theorem LamSort.beq_refl : {a : LamSort} → (a.beq a) = true
| .atom m => Nat.beq_refl' m
| .base b => LamBaseSort.beq_refl
| .func m₁ n₁ => by rw [beq]; rw [LamSort.beq_refl (a:=m₁)]; rw [LamSort.beq_refl (a:=n₁)]; rfl

theorem LamSort.eq_of_beq_eq_true {a b : LamSort} : (a.beq b = true) → a = b :=
  match a, b with
  | .atom m,     .atom n     => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .base m,     .base n     => fun H => LamBaseSort.eq_of_beq_eq_true H ▸ rfl
  | .func m₁ n₁, .func m₂ n₂ => fun H => by
    unfold beq at H; revert H;
    match h₁ : beq m₁ m₂, h₂ : beq n₁ n₂ with
    | true,  true  =>
      intro _;
      let eq₁ := LamSort.eq_of_beq_eq_true h₁
      let eq₂ := LamSort.eq_of_beq_eq_true h₂
      rw [eq₁, eq₂]
    | true,  false => intro H; cases H
    | false, _     => intro H; cases H
  | .atom m,     .base n     => fun H => by cases H
  | .atom m,     .func m₁ n₁ => fun H => by cases H
  | .base m,     .atom n     => fun H => by cases H
  | .base m,     .func m₁ n₁ => fun H => by cases H
  | .func m₁ n₁, .atom n     => fun H => by cases H
  | .func m₁ n₁, .base n     => fun H => by cases H

instance : LawfulBEq LamSort where
  eq_of_beq := LamSort.eq_of_beq_eq_true
  rfl := LamSort.beq_refl

theorem LamSort.beq_eq_true_eq (a b : LamSort) : (a.beq b = true) = (a = b) :=
  propext <| Iff.intro eq_of_beq_eq_true (fun h => by subst h; apply beq_refl)

theorem LamSort.beq_eq_false_eq_ne (a b : LamSort) : (a.beq b = false) = (a ≠ b) := by
  cases h : a.beq b
  case true =>
    cases (eq_of_beq_eq_true h); apply propext (Iff.intro (fun h => by cases h) (fun _ => by contradiction))
  case false =>
    apply propext (Iff.intro (fun _ h' => by cases h'; rw [beq_refl] at h; cases h) (fun _ => rfl))

def LamSort.contains (s : LamSort) (sub : LamSort) : Bool :=
  match s with
  | .func argTy resTy => s.beq sub || argTy.contains sub || resTy.contains sub
  | s => s.beq sub

/-- Given `a` and `[ty₀, ty₁, ⋯, tyᵢ₋₁]`, return `ty₀ → ty₁ → ⋯ → tyᵢ₋₁ → a` -/
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

/-- Given `a` and `[ty₀, ty₁, ⋯, tyᵢ₋₁]`, return `tyᵢ₋₁ → ⋯ → ty₁ → ty₀ → a` -/
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

/-- Given `ty₀ → ty₁ → ⋯ → tyᵢ₋₁ → a`, return `[ty₀, ty₁, ⋯, tyᵢ₋₁]` -/
def LamSort.getArgTys : LamSort → List LamSort
| .atom _ => .nil
| .base _ => .nil
| .func argTy resTy => argTy :: getArgTys resTy

/-- Given `ty₀ → ty₁ → ⋯ → tyᵢ₋₁ → a`, return `a` -/
def LamSort.getResTy : LamSort → LamSort
| .atom n => .atom n
| .base b => .base b
| .func _ resTy => resTy.getResTy

theorem LamSort.getArgTys_getResTy_eq :
  {s : LamSort} → .mkFuncs s.getResTy s.getArgTys = s
| .atom _ => rfl
| .base _ => rfl
| .func _ resTy => congrArg _ (@getArgTys_getResTy_eq resTy)

/-- Given `ty₀ → ty₁ → ⋯ → tyₙ₋₁ → a`, return `[ty₀, ty₁, ⋯, tyₙ₋₁]` -/
def LamSort.getArgTysN (n : Nat) (s : LamSort) : Option (List LamSort) :=
  match n with
  | .zero => .some .nil
  | .succ n =>
    match s with
    | .func argTy resTy => (getArgTysN n resTy).bind (argTy :: ·)
    | _ => .none

/-- Given `ty₀ → ty₁ → ⋯ → tyₙ₋₁ → a`, return `a` -/
def LamSort.getResTyN (n : Nat) (s : LamSort) : Option LamSort :=
  match n with
  | .zero => s
  | .succ n =>
    match s with
    | .func _ resTy => getResTyN n resTy
    | _ => .none

theorem LamSort.getArgTysN_getResTysN_eq_some :
  (getArgTysN n s).isSome = (getResTyN n s).isSome := by
  induction n generalizing s
  case zero => rfl
  case succ n IH =>
    dsimp [getArgTysN, getResTyN]; cases s <;> try rfl
    case func argTy resTy =>
      have IH' := @IH resTy; dsimp
      cases h₁ : getArgTysN n resTy <;> rw [h₁] at IH' <;> dsimp at IH'
        <;> cases h₂ : getResTyN n resTy <;> rw [h₂] at IH' <;> cases IH' <;> rfl

theorem LamSort.getArgTysN_eq_some_of_getResTysN_eq_some
  (heq : getResTyN n s = .some resTy) : ∃ l, getArgTysN n s = .some l := by
  apply Option.isSome_iff_exists.mp; rw [getArgTysN_getResTysN_eq_some]
  apply Option.isSome_iff_exists.mpr; exists resTy

theorem LamSort.getResTysN_eq_some_of_getArgTysN_eq_some
  (heq : getArgTysN n s = .some l) : ∃ resTy, getResTyN n s = .some resTy := by
  apply Option.isSome_iff_exists.mp; rw [← getArgTysN_getResTysN_eq_some]
  apply Option.isSome_iff_exists.mpr; exists l

theorem LamSort.getArgTysN_getResTysN_eq_none :
  (getArgTysN n s).isNone = (getResTyN n s).isNone := by
  rw [Option.isNone_eq_not_isSome, Option.isNone_eq_not_isSome]
  rw [getArgTysN_getResTysN_eq_some]

theorem LamSort.getArgTysN_getResTyN_eq
  (hArg : getArgTysN n s = .some l) (hRes : getResTyN n s = .some s') :
  s = s'.mkFuncs l := by
  induction n generalizing s s' l
  case zero =>
    cases hArg; cases hRes; rfl
  case succ n IH =>
    cases s <;> try cases hArg
    case func argTy resTy =>
      dsimp [getArgTysN] at hArg; dsimp [getResTyN] at hRes
      cases h₁ : getArgTysN n resTy <;> rw [h₁] at hArg <;> cases hArg
      case refl l' =>
        dsimp [mkFuncs]; apply congrArg; apply IH h₁ hRes

theorem LamSort.getArgTysN_mkFuncs_eq_l_iff :
  getArgTysN n (mkFuncs s l) = some l ↔ l.length = n := by
  induction n generalizing s l
  case zero =>
    dsimp [getArgTysN]; apply Iff.intro
    case mp => intro h; cases h; rfl
    case mpr => intro h; cases l <;> cases h; rfl
  case succ n IH =>
    dsimp [getArgTysN]; cases l
    case nil =>
      dsimp [mkFuncs]; apply Iff.intro
      case mp =>
        cases s <;> intro h <;> try cases h
        case func argTy resTy =>
          dsimp at h; cases h₁ : getArgTysN n resTy <;> rw [h₁] at h <;> cases h
      case mpr =>
        intro h; cases h
    case cons s' l =>
      rw [mkFuncs_cons]; dsimp; cases h₁ : getArgTysN n (mkFuncs s l)
      case none => simp; intro h; rw [IH.mpr h] at h₁; cases h₁
      case some l' =>
        simp; apply Iff.intro
        case mp => intro h; cases h; apply IH.mp h₁
        case mpr => intro h; have h₂ := (IH (s:=s)).mpr h; rw [h₁] at h₂; cases h₂; rfl

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

inductive PropConst
  | trueE    : PropConst -- Propositional `true`
  | falseE   : PropConst -- Propositional `false`
  | not      : PropConst -- Propositional `not`
  | and      : PropConst -- Propositional `and`
  | or       : PropConst -- Propositional `or`
  | imp      : PropConst -- Propositional `imp`
  | iff      : PropConst -- Propositional `iff`
deriving Inhabited, Hashable, Lean.ToExpr

def PropConst.reprAux : PropConst → String
| trueE  => "trueE"
| falseE => "falseE"
| not    => "not"
| and    => "and"
| or     => "or"
| imp    => "imp"
| iff    => "iff"

def PropConst.reprPrec (p : PropConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.PropConst.{p.reprAux}"
  | _ + 1 => f!"({p.reprAux})"

instance : Repr PropConst where
  reprPrec := PropConst.reprPrec

def PropConst.toString : PropConst → String
| trueE  => "True"
| falseE => "False"
| not    => "¬"
| and    => "∧"
| or     => "∨"
| imp    => "→"
| iff    => "↔"

instance : ToString PropConst where
  toString := PropConst.toString

def PropConst.beq : PropConst → PropConst → Bool
| trueE,  trueE  => true
| falseE, falseE => true
| not,    not    => true
| and,    and    => true
| or,     or     => true
| imp,    imp    => true
| iff,    iff    => true
| _,       _     => false

instance : BEq PropConst where
  beq := PropConst.beq

def PropConst.beq_refl {p : PropConst} : (p.beq p) = true := by
  cases p <;> rfl

def PropConst.eq_of_beq_eq_true {p₁ p₂ : PropConst} (H : p₁.beq p₂) : p₁ = p₂ := by
  cases p₁ <;> cases p₂ <;> first | contradiction | rfl

instance : LawfulBEq PropConst where
  eq_of_beq := PropConst.eq_of_beq_eq_true
  rfl := PropConst.beq_refl

def PropConst.lamCheck : PropConst → LamSort
| .trueE  => .base .prop
| .falseE => .base .prop
| .not    => .func (.base .prop) (.base .prop)
| .and | .or | .imp | .iff => .func (.base .prop) (.func (.base .prop) (.base .prop))

inductive PropConst.LamWF : PropConst → LamSort → Type
  | ofTrueE      : LamWF .trueE (.base .prop)
  | ofFalseE     : LamWF .falseE (.base .prop)
  | ofNot        : LamWF .not (.func (.base .prop) (.base .prop))
  | ofAnd        : LamWF .and (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofOr         : LamWF .or (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofImp        : LamWF .imp (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofIff        : LamWF .iff (.func (.base .prop) (.func (.base .prop) (.base .prop)))

def PropConst.LamWF.unique {p : PropConst} {s₁ s₂ : LamSort}
  (pcwf₁ : LamWF p s₁) (pcwf₂ : LamWF p s₂) : s₁ = s₂ ∧ HEq pcwf₁ pcwf₂ := by
  cases pcwf₁ <;> cases pcwf₂ <;> trivial

def PropConst.LamWF.ofPropConst : (p : PropConst) → (s : LamSort) × PropConst.LamWF p s
| .trueE      => ⟨.base .prop, .ofTrueE⟩
| .falseE     => ⟨.base .prop, .ofFalseE⟩
| .not        => ⟨.func (.base .prop) (.base .prop), .ofNot⟩
| .and        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofAnd⟩
| .or         => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofOr⟩
| .imp        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofImp⟩
| .iff        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofIff⟩

def PropConst.lamWF_complete (wf : LamWF p s) : LamWF.ofPropConst p = ⟨s, wf⟩ := by
  cases wf <;> rfl

def PropConst.lamCheck_of_LamWF (H : LamWF p s) : p.lamCheck = s := by
  cases H <;> rfl

def PropConst.LamWF.ofCheck (H : p.lamCheck = s) : LamWF p s := by
  cases H; cases p <;> constructor

inductive BoolConst
  | ofProp
  | trueb  -- Boolean `true`
  | falseb -- Boolean `false`
  | notb   -- Boolean `not`
  | andb   -- Boolean `and`
  | orb    -- Boolean `or`
deriving Inhabited, Hashable, Lean.ToExpr

def BoolConst.reprAux : BoolConst → String
| .ofProp => "ofProp"
| .trueb  => "trueb"
| .falseb => "falseb"
| .notb   => "notb"
| .andb   => "andb"
| .orb    => "orb"

def BoolConst.reprPrec (b : BoolConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.BoolConst.{b.reprAux}"
  | _ + 1 => f!"(.{b.reprAux})"

instance : Repr BoolConst where
  reprPrec := BoolConst.reprPrec

def BoolConst.toString : BoolConst → String
| .ofProp => "ofProp"
| .trueb  => "true"
| .falseb => "false"
| .notb   => "!"
| .andb   => "&&"
| .orb    => "||"

instance : ToString BoolConst where
  toString := BoolConst.toString

def BoolConst.beq : BoolConst → BoolConst → Bool
| .ofProp, .ofProp => true
| .trueb,  .trueb  => true
| .falseb, .falseb => true
| .notb,   .notb   => true
| .andb,   .andb   => true
| .orb,    .orb    => true
| _,       _       => false

instance : BEq BoolConst where
  beq := BoolConst.beq

def BoolConst.beq_refl {b : BoolConst} : (b.beq b) = true := by
  cases b <;> rfl

def BoolConst.eq_of_beq_eq_true {b₁ b₂ : BoolConst} (H : b₁.beq b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | contradiction | rfl

instance : LawfulBEq BoolConst where
  eq_of_beq := BoolConst.eq_of_beq_eq_true
  rfl := BoolConst.beq_refl

def BoolConst.lamCheck : BoolConst → LamSort
| .ofProp => .func (.base .prop) (.base .bool)
| .trueb => .base .bool
| .falseb => .base .bool
| .notb => .func (.base .bool) (.base .bool)
| .andb => .func (.base .bool) (.func (.base .bool) (.base .bool))
| .orb => .func (.base .bool) (.func (.base .bool) (.base .bool))

inductive BoolConst.LamWF : BoolConst → LamSort → Type
  | ofOfProp     : LamWF .ofProp (.func (.base .prop) (.base .bool))
  | ofTrueB      : LamWF .trueb (.base .bool)
  | ofFalseB     : LamWF .falseb (.base .bool)
  | ofNotB       : LamWF .notb (.func (.base .bool) (.base .bool))
  | ofAndB       : LamWF .andb (.func (.base .bool) (.func (.base .bool) (.base .bool)))
  | ofOrB        : LamWF .orb (.func (.base .bool) (.func (.base .bool) (.base .bool)))

def BoolConst.LamWF.unique {b : BoolConst} {s₁ s₂ : LamSort}
  (bcwf₁ : LamWF b s₁) (bcwf₂ : LamWF b s₂) : s₁ = s₂ ∧ HEq bcwf₁ bcwf₂ := by
  cases bcwf₁ <;> cases bcwf₂ <;> trivial

def BoolConst.LamWF.ofBoolConst : (b : BoolConst) → (s : LamSort) × BoolConst.LamWF b s
| .ofProp     => ⟨.func (.base .prop) (.base .bool), .ofOfProp⟩
| .trueb      => ⟨.base .bool, .ofTrueB⟩
| .falseb     => ⟨.base .bool, .ofFalseB⟩
| .notb       => ⟨.func (.base .bool) (.base .bool), .ofNotB⟩
| .andb       => ⟨.func (.base .bool) (.func (.base .bool) (.base .bool)), .ofAndB⟩
| .orb        => ⟨.func (.base .bool) (.func (.base .bool) (.base .bool)), .ofOrB⟩

def BoolConst.lamWF_complete (wf : LamWF b s) : LamWF.ofBoolConst b = ⟨s, wf⟩ := by
  cases wf <;> rfl

def BoolConst.lamCheck_of_LamWF (H : LamWF b s) : b.lamCheck = s := by
  cases H <;> rfl

def BoolConst.LamWF.ofCheck (H : b.lamCheck = s) : LamWF b s := by
  cases H; cases b <;> constructor

inductive NatConst
  | natVal (n : Nat)
  | nadd | nsub | nmul | ndiv | nmod
  | nle | nlt | nmax | nmin
deriving Inhabited, Hashable, Lean.ToExpr

def NatConst.reprAux : NatConst → String
| .natVal n => s!"natVal {n}"
| .nadd     => "nadd"
| .nsub     => "nsub"
| .nmul     => "nmul"
| .ndiv     => "ndiv"
| .nmod     => "nmod"
| .nle      => "nle"
| .nlt      => "nlt"
| .nmax     => "nmax"
| .nmin     => "nmin"

def NatConst.reprPrec (nc : NatConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.NatConst.{nc.reprAux}"
  | _ + 1 => f!"(.{nc.reprAux})"

instance : Repr NatConst where
  reprPrec := NatConst.reprPrec

def NatConst.toString : NatConst → String
| .natVal n => s!"{n} : Nat"
| .nadd     => "+"
| .nsub     => "-"
| .nmul     => "*"
| .ndiv     => "/"
| .nmod     => "%"
| .nle      => "≤"
| .nlt      => "<"
| .nmax     => "nmax"
| .nmin     => "nmin"

instance : ToString NatConst where
  toString := NatConst.toString

def NatConst.beq : NatConst → NatConst → Bool
| .natVal n, .natVal m => Nat.beq n m
| .nadd,     .nadd  => true
| .nsub,     .nsub  => true
| .nmul,     .nmul  => true
| .ndiv,     .ndiv  => true
| .nmod,     .nmod  => true
| .nle,      .nle   => true
| .nlt,      .nlt   => true
| .nmax,     .nmax  => true
| .nmin,     .nmin  => true
| _,         _      => false

instance : BEq NatConst where
  beq := NatConst.beq

def NatConst.beq_refl {n : NatConst} : (n.beq n) = true := by
  cases n <;> first | rfl | apply Nat.beq_refl

def NatConst.eq_of_beq_eq_true {n₁ n₂ : NatConst} (H : n₁.beq n₂) : n₁ = n₂ := by
  cases n₁ <;> cases n₂ <;> try (first | contradiction | rfl)
  case natVal.natVal n m => apply congrArg; apply Nat.eq_of_beq_eq_true H

instance : LawfulBEq NatConst where
  eq_of_beq := NatConst.eq_of_beq_eq_true
  rfl := NatConst.beq_refl

def NatConst.lamCheck : NatConst → LamSort
| .natVal _ => .base .nat
| .nadd     => .func (.base .nat) (.func (.base .nat) (.base .nat))
| .nsub     => .func (.base .nat) (.func (.base .nat) (.base .nat))
| .nmul     => .func (.base .nat) (.func (.base .nat) (.base .nat))
| .ndiv     => .func (.base .nat) (.func (.base .nat) (.base .nat))
| .nmod     => .func (.base .nat) (.func (.base .nat) (.base .nat))
| .nle      => .func (.base .nat) (.func (.base .nat) (.base .prop))
| .nlt      => .func (.base .nat) (.func (.base .nat) (.base .prop))
| .nmax     => .func (.base .nat) (.func (.base .nat) (.base .nat))
| .nmin     => .func (.base .nat) (.func (.base .nat) (.base .nat))

inductive NatConst.LamWF : NatConst → LamSort → Type
  | ofNatVal n : LamWF (.natVal n) (.base .nat)
  | ofNadd     : LamWF .nadd (.func (.base .nat) (.func (.base .nat) (.base .nat)))
  | ofNsub     : LamWF .nsub (.func (.base .nat) (.func (.base .nat) (.base .nat)))
  | ofNmul     : LamWF .nmul (.func (.base .nat) (.func (.base .nat) (.base .nat)))
  | ofNdiv     : LamWF .ndiv (.func (.base .nat) (.func (.base .nat) (.base .nat)))
  | ofNmod     : LamWF .nmod (.func (.base .nat) (.func (.base .nat) (.base .nat)))
  | ofNle      : LamWF .nle (.func (.base .nat) (.func (.base .nat) (.base .prop)))
  | ofNlt      : LamWF .nlt (.func (.base .nat) (.func (.base .nat) (.base .prop)))
  | ofNmax     : LamWF .nmax (.func (.base .nat) (.func (.base .nat) (.base .nat)))
  | ofNmin     : LamWF .nmin (.func (.base .nat) (.func (.base .nat) (.base .nat)))

def NatConst.LamWF.unique {n : NatConst} {s₁ s₂ : LamSort}
  (nwf₁ : LamWF n s₁) (nwf₂ : LamWF n s₂) : s₁ = s₂ ∧ HEq nwf₁ nwf₂ := by
  cases nwf₁ <;> cases nwf₂ <;> trivial

def NatConst.LamWF.ofNatConst : (n : NatConst) → (s : LamSort) × NatConst.LamWF n s
| .natVal n => ⟨.base .nat, .ofNatVal n⟩
| .nadd     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNadd⟩
| .nsub     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNsub⟩
| .nmul     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNmul⟩
| .ndiv     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNdiv⟩
| .nmod     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNmod⟩
| .nle      => ⟨.func (.base .nat) (.func (.base .nat) (.base .prop)), .ofNle⟩
| .nlt      => ⟨.func (.base .nat) (.func (.base .nat) (.base .prop)), .ofNlt⟩
| .nmax     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNmax⟩
| .nmin     => ⟨.func (.base .nat) (.func (.base .nat) (.base .nat)), .ofNmin⟩

def NatConst.lamWF_complete (wf : LamWF n s) : LamWF.ofNatConst n = ⟨s, wf⟩ := by
  cases wf <;> rfl

def NatConst.lamCheck_of_LamWF (H : LamWF n s) : n.lamCheck = s := by
  cases H <;> rfl

def NatConst.LamWF.ofCheck (H : n.lamCheck = s) : LamWF n s := by
  cases H; cases n <;> constructor

inductive IntConst
  | iofNat | inegSucc | ineg | iabs
  | iadd | isub | imul | idiv | imod | iediv | iemod
  | ile | ilt | imax | imin
deriving Inhabited, Hashable, Lean.ToExpr

def IntConst.reprAux : IntConst → String
| .iofNat   => "iofNat"
| .inegSucc => "inegSucc"
| .ineg     => "ineg"
| .iabs     => "iabs"
| .iadd     => "iadd"
| .isub     => "isub"
| .imul     => "imul"
| .idiv     => "idiv"
| .imod     => "imod"
| .iediv    => "iediv"
| .iemod    => "iemod"
| .ile      => "ile"
| .ilt      => "ilt"
| .imax     => "imax"
| .imin     => "imin"

def IntConst.reprPrec (i : IntConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.IntConst.{i.reprAux}"
  | _ + 1 => f!"(.{i.reprAux})"

instance : Repr IntConst where
  reprPrec := IntConst.reprPrec

def IntConst.toString : IntConst → String
| .iofNat   => "iofNat"
| .inegSucc => "inegSucc"
| .ineg     => "-"
| .iabs     => "iabs"
| .iadd     => "+"
| .isub     => "-"
| .imul     => "*"
| .idiv     => "/"
| .imod     => "%"
| .iediv    => "/?"
| .iemod    => "%?"
| .ile      => "≤"
| .ilt      => "<"
| .imax     => "imax"
| .imin     => "imin"

instance : ToString IntConst where
  toString := IntConst.toString

def IntConst.beq : IntConst → IntConst → Bool
| .iofNat,   .iofNat   => true
| .inegSucc, .inegSucc => true
| .ineg,     .ineg     => true
| .iabs,     .iabs     => true
| .iadd,     .iadd     => true
| .isub,     .isub     => true
| .imul,     .imul     => true
| .idiv,     .idiv     => true
| .imod,     .imod     => true
| .iediv,    .iediv    => true
| .iemod,    .iemod    => true
| .ile,      .ile      => true
| .ilt,      .ilt      => true
| .imax,     .imax     => true
| .imin,     .imin     => true
| _,         _         => false

instance : BEq IntConst where
  beq := IntConst.beq

def IntConst.beq_refl {i : IntConst} : (i.beq i) = true := by
  cases i <;> rfl

def IntConst.eq_of_beq_eq_true {i₁ i₂ : IntConst} (H : i₁.beq i₂) : i₁ = i₂ := by
  cases i₁ <;> cases i₂ <;> try (first | contradiction | rfl)

instance : LawfulBEq IntConst where
  eq_of_beq := IntConst.eq_of_beq_eq_true
  rfl := IntConst.beq_refl

def IntConst.lamCheck : IntConst → LamSort
| .iofNat   => .func (.base .nat) (.base .int)
| .inegSucc => .func (.base .nat) (.base .int)
| .ineg     => .func (.base .int) (.base .int)
| .iabs     => .func (.base .int) (.base .int)
| .iadd     => .func (.base .int) (.func (.base .int) (.base .int))
| .isub     => .func (.base .int) (.func (.base .int) (.base .int))
| .imul     => .func (.base .int) (.func (.base .int) (.base .int))
| .idiv     => .func (.base .int) (.func (.base .int) (.base .int))
| .imod     => .func (.base .int) (.func (.base .int) (.base .int))
| .iediv    => .func (.base .int) (.func (.base .int) (.base .int))
| .iemod    => .func (.base .int) (.func (.base .int) (.base .int))
| .ile      => .func (.base .int) (.func (.base .int) (.base .prop))
| .ilt      => .func (.base .int) (.func (.base .int) (.base .prop))
| .imax     => .func (.base .int) (.func (.base .int) (.base .int))
| .imin     => .func (.base .int) (.func (.base .int) (.base .int))

inductive IntConst.LamWF : IntConst → LamSort → Type
  | ofIOfNat   : LamWF .iofNat (.func (.base .nat) (.base .int))
  | ofINegSucc : LamWF .inegSucc (.func (.base .nat) (.base .int))
  | ofIneg     : LamWF .ineg (.func (.base .int) (.base .int))
  | ofIabs     : LamWF .iabs (.func (.base .int) (.base .int))
  | ofIadd     : LamWF .iadd (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofIsub     : LamWF .isub (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofImul     : LamWF .imul (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofIdiv     : LamWF .idiv (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofImod     : LamWF .imod (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofIediv    : LamWF .iediv (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofIemod    : LamWF .iemod (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofIle      : LamWF .ile (.func (.base .int) (.func (.base .int) (.base .prop)))
  | ofIlt      : LamWF .ilt (.func (.base .int) (.func (.base .int) (.base .prop)))
  | ofImax     : LamWF .imax (.func (.base .int) (.func (.base .int) (.base .int)))
  | ofImin     : LamWF .imin (.func (.base .int) (.func (.base .int) (.base .int)))

def IntConst.LamWF.unique {i : IntConst} {s₁ s₂ : LamSort}
  (iwf₁ : LamWF i s₁) (iwf₂ : LamWF i s₂) : s₁ = s₂ ∧ HEq iwf₁ iwf₂ := by
  cases iwf₁ <;> cases iwf₂ <;> trivial

def IntConst.LamWF.ofIntConst : (i : IntConst) → (s : LamSort) × IntConst.LamWF i s
| .iofNat   => ⟨.func (.base .nat) (.base .int), .ofIOfNat⟩
| .inegSucc => ⟨.func (.base .nat) (.base .int), .ofINegSucc⟩
| .ineg     => ⟨.func (.base .int) (.base .int), .ofIneg⟩
| .iabs     => ⟨.func (.base .int) (.base .int), .ofIabs⟩
| .iadd     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofIadd⟩
| .isub     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofIsub⟩
| .imul     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofImul⟩
| .idiv     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofIdiv⟩
| .imod     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofImod⟩
| .iediv    => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofIediv⟩
| .iemod    => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofIemod⟩
| .ile      => ⟨.func (.base .int) (.func (.base .int) (.base .prop)), .ofIle⟩
| .ilt      => ⟨.func (.base .int) (.func (.base .int) (.base .prop)), .ofIlt⟩
| .imax     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofImax⟩
| .imin     => ⟨.func (.base .int) (.func (.base .int) (.base .int)), .ofImin⟩

def IntConst.lamWF_complete (wf : LamWF i s) : LamWF.ofIntConst i = ⟨s, wf⟩ := by
  cases wf <;> rfl

def IntConst.lamCheck_of_LamWF (H : LamWF i s) : i.lamCheck = s := by
  cases H <;> rfl

def IntConst.LamWF.ofCheck (H : i.lamCheck = s) : LamWF i s := by
  cases H; cases i <;> constructor

inductive StringConst
  | strVal (s : String)
  | slength
  | sapp
  | sle
  | slt
  | sprefixof
  | srepall
deriving Inhabited, Hashable, Lean.ToExpr

def StringConst.reprAux : StringConst → String
| .strVal s  => s!"strVal \"{s}\""
| .slength   => "slength"
| .sapp      => "sapp"
| .sle       => "sle"
| .slt       => "slt"
| .sprefixof => "sprefixof"
| .srepall   => "srepall"

def StringConst.reprPrec (s : StringConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.StringConst.{s.reprAux}"
  | _ + 1 => f!"(.{s.reprAux})"

instance : Repr StringConst where
  reprPrec := StringConst.reprPrec

def StringConst.toString : StringConst → String
| .strVal s => s!"({s} : String)"
| .slength => "length"
| .sapp => "++"
| .sle => "≤"
| .slt => "<"
| .sprefixof => "is_prefix_of"
| .srepall => "replace_all"

instance : ToString StringConst where
  toString := StringConst.toString

def StringConst.beq : StringConst → StringConst → Bool
| .strVal m,  .strVal n  => m == n
| .slength,   .slength   => true
| .sapp,      .sapp      => true
| .sle,       .sle       => true
| .slt,       .slt       => true
| .sprefixof, .sprefixof => true
| .srepall,   .srepall   => true
| _,          _          => false

instance : BEq StringConst where
  beq := StringConst.beq

def StringConst.beq_refl {s : StringConst} : (s.beq s) = true := by
  cases s <;> try rfl
  case strVal s => apply BEq.rfl (α := String)

def StringConst.eq_of_beq_eq_true {s₁ s₂ : StringConst} (H : s₁.beq s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> try (first | contradiction | rfl)
  case strVal.strVal n m => apply congrArg; apply LawfulBEq.eq_of_beq (α := String) H

instance : LawfulBEq StringConst where
  eq_of_beq := StringConst.eq_of_beq_eq_true
  rfl := StringConst.beq_refl

def StringConst.lamCheck : StringConst → LamSort
| .strVal _  => .base .string
| .slength   => .func (.base .string) (.base .nat)
| .sapp      => .func (.base .string) (.func (.base .string) (.base .string))
| .sle       => .func (.base .string) (.func (.base .string) (.base .prop))
| .slt       => .func (.base .string) (.func (.base .string) (.base .prop))
| .sprefixof => .func (.base .string) (.func (.base .string) (.base .bool))
| .srepall   => .func (.base .string) (.func (.base .string) (.func (.base .string) (.base .string)))

inductive StringConst.LamWF : StringConst → LamSort → Type
  | ofStrVal s  : LamWF (.strVal s) (.base .string)
  | ofSlength   : LamWF .slength (.func (.base .string) (.base .nat))
  | ofSapp      : LamWF .sapp (.func (.base .string) (.func (.base .string) (.base .string)))
  | ofSle       : LamWF .sle (.func (.base .string) (.func (.base .string) (.base .prop)))
  | ofSlt       : LamWF .slt (.func (.base .string) (.func (.base .string) (.base .prop)))
  | ofSprefixof : LamWF .sprefixof (.func (.base .string) (.func (.base .string) (.base .bool)))
  | ofSrepall   : LamWF .srepall (.func (.base .string) (.func (.base .string) (.func (.base .string) (.base .string))))

def StringConst.LamWF.unique {s : StringConst} {s₁ s₂ : LamSort}
  (iwf₁ : LamWF s s₁) (iwf₂ : LamWF s s₂) : s₁ = s₂ ∧ HEq iwf₁ iwf₂ := by
  cases iwf₁ <;> cases iwf₂ <;> trivial

def StringConst.LamWF.ofStringConst : (sc : StringConst) → (s : LamSort) × StringConst.LamWF sc s
| .strVal s  => ⟨.base .string, .ofStrVal s⟩
| .slength   => ⟨.func (.base .string) (.base .nat), .ofSlength⟩
| .sapp      => ⟨.func (.base .string) (.func (.base .string) (.base .string)), .ofSapp⟩
| .sle       => ⟨.func (.base .string) (.func (.base .string) (.base .prop)), .ofSle⟩
| .slt       => ⟨.func (.base .string) (.func (.base .string) (.base .prop)), .ofSlt⟩
| .sprefixof => ⟨.func (.base .string) (.func (.base .string) (.base .bool)), .ofSprefixof⟩
| .srepall   => ⟨.func (.base .string) (.func (.base .string) (.func (.base .string) (.base .string))), .ofSrepall⟩

def StringConst.lamWF_complete (wf : LamWF sc s) : LamWF.ofStringConst sc = ⟨s, wf⟩ := by
  cases wf <;> rfl

def StringConst.lamCheck_of_LamWF (H : LamWF sc s) : sc.lamCheck = s := by
  cases H <;> rfl

def StringConst.LamWF.ofCheck (H : sc.lamCheck = s) : LamWF sc s := by
  cases H; cases sc <;> constructor

inductive BVAOp where
  | add
  | sub
  | mul
  -- `BitVec.smtUDiv`
  | udiv
  | urem
  -- `BitVec.smtSDiv`
  | sdiv
  | srem
  | smod
  deriving Inhabited, Hashable, Lean.ToExpr

def BVAOp.repr (n : Nat) : BVAOp → String
| .add  => s!"bvadd {n}"
| .sub  => s!"bvsub {n}"
| .mul  => s!"bvmul {n}"
| .udiv => s!"bvudiv {n}"
| .urem => s!"bvurem {n}"
| .sdiv => s!"bvsdiv {n}"
| .srem => s!"bvsrem {n}"
| .smod => s!"bvsmod {n}"

def BVAOp.toString : BVAOp → String
| .add  => s!"+"
| .sub  => s!"-"
| .mul  => s!"*"
| .udiv => s!"/ᵤ"
| .urem => s!"%ᵤ"
| .sdiv => s!"/"
| .srem => s!"%ᵣ"
| .smod => s!"%"

def BVAOp.beq : BVAOp → BVAOp → Bool
| add,  add  => true
| sub,  sub  => true
| mul,  mul  => true
| udiv, udiv => true
| urem, urem => true
| sdiv, sdiv => true
| srem, srem => true
| smod, smod => true
| _,    _    => false

instance : BEq BVAOp where
  beq := BVAOp.beq

def BVAOp.beq_refl {a : BVAOp} : (a.beq a) = true := by
  cases a <;> rfl

def BVAOp.eq_of_beq_eq_true {a₁ a₂ : BVAOp} (H : a₁.beq a₂) : a₁ = a₂ := by
  cases a₁ <;> cases a₂ <;> first | contradiction | rfl

instance : LawfulBEq BVAOp where
  eq_of_beq := BVAOp.eq_of_beq_eq_true
  rfl := BVAOp.beq_refl

inductive BVCmp where
  | ult
  | ule
  | slt
  | sle
  deriving Inhabited, Hashable, Lean.ToExpr

def BVCmp.repr (n : Nat) (prop? : Bool) (cmp : BVCmp) : String :=
  let pStr := if prop? then "p" else ""
  match cmp with
  | .ult => s!"bv{pStr}ult {n}"
  | .ule => s!"bv{pStr}ule {n}"
  | .slt => s!"bv{pStr}slt {n}"
  | .sle => s!"bv{pStr}sle {n}"

def BVCmp.toString (prop? : Bool) (cmp : BVCmp) : String :=
  let pStr := if prop? then "ₚ" else ""
  match cmp with
  | .ult => s!"{pStr}<ᵤ"
  | .ule => s!"{pStr}≤ᵤ"
  | .slt => s!"{pStr}<"
  | .sle => s!"{pStr}≤"

def BVCmp.beq : BVCmp → BVCmp → Bool
| .ult, .ult => true
| .ule, .ule => true
| .slt, .slt => true
| .sle, .sle => true
| _,    _    => false

instance : BEq BVCmp where
  beq := BVCmp.beq

def BVCmp.beq_refl {c : BVCmp} : (c.beq c) = true := by
  cases c <;> rfl

def BVCmp.eq_of_beq_eq_true {c₁ c₂ : BVCmp} (H : c₁.beq c₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> first | contradiction | rfl

instance : LawfulBEq BVCmp where
  eq_of_beq := BVCmp.eq_of_beq_eq_true
  rfl := BVCmp.beq_refl

inductive BVShOp where
  | shl
  | lshr
  | ashr
  deriving Inhabited, Hashable, Lean.ToExpr

def BVShOp.repr (n : Nat) (smt? : Bool) (shOp : BVShOp) : String :=
  let smtStr := if smt? then "smt" else ""
  match shOp with
  | .shl  => s!"bv{smtStr}shl {n}"
  | .lshr => s!"bv{smtStr}lshr {n}"
  | .ashr => s!"bv{smtStr}ashr {n}"

def BVShOp.toString (smt? : Bool) (shOp : BVShOp) : String :=
  let smtStr := if smt? then "ₛ" else ""
  match shOp with
  | .shl => s!"<<<{smtStr}"
  | .lshr => s!">>>{smtStr}"
  | .ashr => s!">>>ₐ{smtStr}"

def BVShOp.beq : BVShOp → BVShOp → Bool
| shl,  shl  => true
| lshr, lshr => true
| ashr, ashr => true
| _,    _    => false

instance : BEq BVShOp where
  beq := BVShOp.beq

def BVShOp.beq_refl {s : BVShOp} : (s.beq s) = true := by
  cases s <;> rfl

def BVShOp.eq_of_beq_eq_true {s₁ s₂ : BVShOp} (H : s₁.beq s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> first | contradiction | rfl

instance : LawfulBEq BVShOp where
  eq_of_beq := BVShOp.eq_of_beq_eq_true
  rfl := BVShOp.beq_refl

/--
  Following `https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV`
-/
inductive BitVecConst
  -- `BitVec.ofNat n i, but requires both arguments to be nat literals`
  | bvVal (n : Nat) (i : Nat)
  | bvofNat (n : Nat)
  | bvtoNat (n : Nat)
  | bvofInt (n : Nat)
  | bvtoInt (n : Nat)
  | bvmsb (n : Nat)
  -- zero : Use `bvofNat`
  -- allones : Use `bvneg`
  | bvaOp (n : Nat) (op : BVAOp)
  | bvneg (n : Nat)
  | bvabs (n : Nat)
  | bvcmp (n : Nat) (prop? : Bool) (op : BVCmp)
  | bvand (n : Nat)
  | bvor (n : Nat)
  | bvxor (n : Nat)
  | bvnot (n : Nat)
  -- `smt? = true => smt version (BitVec n → BitVec n → BitVec n)`
  -- `smt? = false => Lean version (BitVec n → Nat → BitVec n)`
  | bvshOp (n : Nat) (smt? : Bool) (op : BVShOp)
  | bvappend (n m : Nat)
  | bvextract (n hi lo : Nat)
  -- `BitVec.replicate`
  | bvrepeat (w i : Nat)
  | bvzeroExtend (w v : Nat)
  | bvsignExtend (w v : Nat)
deriving Inhabited, Hashable, Lean.ToExpr

def BitVecConst.bvadd (n : Nat) := BitVecConst.bvaOp n .add

def BitVecConst.bvsub (n : Nat) := BitVecConst.bvaOp n .sub

def BitVecConst.bvmul (n : Nat) := BitVecConst.bvaOp n .mul

def BitVecConst.bvudiv (n : Nat) := BitVecConst.bvaOp n .udiv

def BitVecConst.bvurem (n : Nat) := BitVecConst.bvaOp n .urem

def BitVecConst.bvsdiv (n : Nat) := BitVecConst.bvaOp n .sdiv

def BitVecConst.bvsrem (n : Nat) := BitVecConst.bvaOp n .srem

def BitVecConst.bvsmod (n : Nat) := BitVecConst.bvaOp n .smod

def BitVecConst.bvult (n : Nat) := BitVecConst.bvcmp n false .ult

def BitVecConst.bvule (n : Nat) := BitVecConst.bvcmp n false .ule

def BitVecConst.bvslt (n : Nat) := BitVecConst.bvcmp n false .slt

def BitVecConst.bvsle (n : Nat) := BitVecConst.bvcmp n false .sle

def BitVecConst.bvpropult (n : Nat) := BitVecConst.bvcmp n true .ult

def BitVecConst.bvpropule (n : Nat) := BitVecConst.bvcmp n true .ule

def BitVecConst.bvpropslt (n : Nat) := BitVecConst.bvcmp n true .slt

def BitVecConst.bvpropsle (n : Nat) := BitVecConst.bvcmp n true .sle

def BitVecConst.bvshl (n : Nat) := BitVecConst.bvshOp n false .shl

def BitVecConst.bvlshr (n : Nat) := BitVecConst.bvshOp n false .lshr

def BitVecConst.bvashr (n : Nat) := BitVecConst.bvshOp n false .ashr

def BitVecConst.bvsmtshl (n : Nat) := BitVecConst.bvshOp n true .shl

def BitVecConst.bvsmtlshr (n : Nat) := BitVecConst.bvshOp n true .lshr

def BitVecConst.bvsmtashr (n : Nat) := BitVecConst.bvshOp n true .ashr

def BitVecConst.reprAux : BitVecConst → String
| .bvVal n i => s!"bvVal {n} {i}"
| .bvofNat n => s!"bvofNat {n}"
| .bvtoNat n => s!"bvtoNat {n}"
| .bvofInt n => s!"bvofInt {n}"
| .bvtoInt n => s!"bvtoInt {n}"
| .bvmsb n   => s!"bvmsb {n}"
| .bvaOp n op => op.repr n
| .bvneg n   => s!"bvneg {n}"
| .bvabs n   => s!"bvabs {n}"
| .bvcmp n prop? cmp => cmp.repr n prop?
| .bvand n   => s!"bvand {n}"
| .bvor n    => s!"bvor {n}"
| .bvxor n   => s!"bvxor {n}"
| .bvnot n   => s!"bvnot {n}"
| .bvshOp n smt? shOp => shOp.repr n smt?
| .bvappend n m      => s!"bvappend {n} {m}"
| .bvextract n hi lo => s!"bvextract {n} {hi} {lo}"
| .bvrepeat w i      => s!"bvrepeat {w} {i}"
| .bvzeroExtend w v  => s!"bvzeroExtend {w} {v}"
| .bvsignExtend w v  => s!"bvsignExtend {w} {v}"

def BitVecConst.reprPrec (b : BitVecConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.BitVecConst.{b.reprAux}"
  | _ + 1 => f!"(.{b.reprAux})"

instance : Repr BitVecConst where
  reprPrec := BitVecConst.reprPrec

def BitVecConst.toString : BitVecConst → String
| .bvVal n i => ToString.toString <| repr (BitVec.ofNat n i)
| .bvofNat n => s!"bvofNat {n}"
| .bvtoNat n => s!"bvtoNat {n}"
| .bvofInt n => s!"bvofInt {n}"
| .bvtoInt n => s!"bvtoInt {n}"
| .bvmsb n => s!"bvmsb {n}"
| .bvaOp _ op => op.toString
| .bvneg _ => s!"-"
| .bvabs _ => s!"bvabs"
| .bvcmp _ prop? op => op.toString prop?
| .bvand _ => s!"&&&"
| .bvor _ => s!"|||"
| .bvxor _ => s!"^^^"
| .bvnot _ => s!"!"
| .bvshOp _ smt? shOp => shOp.toString smt?
| .bvappend _ _ => s!"++"
| .bvextract _ hi lo => s!"bvextract {hi} {lo}"
| .bvrepeat _ i => s!"bvrepeat {i}"
| .bvzeroExtend _ v => s!"bvzeroExtend {v}"
| .bvsignExtend _ v => s!"bvsignExtend {v}"

instance : ToString BitVecConst where
  toString := BitVecConst.toString

def BitVecConst.beq : BitVecConst → BitVecConst → Bool
| .bvVal n₁ i₁,        .bvVal n₂ i₂        => n₁.beq n₂ && i₁.beq i₂
| .bvofNat n₁,         .bvofNat n₂         => n₁.beq n₂
| .bvtoNat n₁,         .bvtoNat n₂         => n₁.beq n₂
| .bvofInt n₁,         .bvofInt n₂         => n₁.beq n₂
| .bvtoInt n₁,         .bvtoInt n₂         => n₁.beq n₂
| .bvmsb n₁,           .bvmsb n₂           => n₁.beq n₂
| .bvaOp n₁ op₁,       .bvaOp n₂ op₂       => n₁.beq n₂ && op₁.beq op₂
| .bvneg n₁,           .bvneg n₂           => n₁.beq n₂
| .bvabs n₁,           .bvabs n₂           => n₁.beq n₂
| .bvcmp n₁ prop₁ op₁, .bvcmp n₂ prop₂ op₂ => n₁.beq n₂ && prop₁ == prop₂ && op₁.beq op₂
| .bvand n₁,           .bvand n₂           => n₁.beq n₂
| .bvor n₁,            .bvor n₂            => n₁.beq n₂
| .bvxor n₁,           .bvxor n₂           => n₁.beq n₂
| .bvnot n₁,           .bvnot n₂           => n₁.beq n₂
| .bvshOp n₁ s₁ op₁,   .bvshOp n₂ s₂ op₂   => n₁.beq n₂ && s₁ == s₂ && op₁.beq op₂
| .bvappend n₁ m₁,     .bvappend n₂ m₂     => n₁.beq n₂ && m₁.beq m₂
| .bvextract n₁ h₁ l₁, .bvextract n₂ h₂ l₂ => n₁.beq n₂ && h₁.beq h₂ && l₁.beq l₂
| .bvrepeat w₁ i₁,     .bvrepeat w₂ i₂     => w₁.beq w₂ && i₁.beq i₂
| .bvzeroExtend w₁ v₁, .bvzeroExtend w₂ v₂ => w₁.beq w₂ && v₁.beq v₂
| .bvsignExtend w₁ v₁, .bvsignExtend w₂ v₂ => w₁.beq w₂ && v₁.beq v₂
| _,       _       => false

instance : BEq BitVecConst where
  beq := BitVecConst.beq

def BitVecConst.beq_refl {b : BitVecConst} : (b.beq b) = true := by
  cases b <;> dsimp [beq] <;> rw [Nat.beq_refl] <;> (try rw [Nat.beq_refl]) <;> (try rfl) <;>
    (try rw [Nat.beq_refl]) <;> (try rfl)
  case bvaOp => rw [BVAOp.beq_refl]; rfl
  case bvcmp => rw [BEq.rfl (α := Bool)]; rw [BVCmp.beq_refl]; rfl
  case bvshOp => rw [BEq.rfl (α := Bool)]; rw [BVShOp.beq_refl]; rfl

def BitVecConst.eq_of_beq_eq_true {b₁ b₂ : BitVecConst} (H : b₁.beq b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> (try contradiction) <;> (try rw [Nat.eq_of_beq_eq_true H]) <;>
    dsimp [beq] at H <;> rw [Bool.and_eq_true] at H <;> (try rw [Bool.and_eq_true] at H) <;>
    (try rw [Nat.eq_of_beq_eq_true H.right]) <;> (try rw [Nat.eq_of_beq_eq_true H.left]) <;>
    (try rw [Nat.eq_of_beq_eq_true H.left.left])
  case bvaOp.bvaOp =>
    rw [BVAOp.eq_of_beq_eq_true H.right]
  case bvcmp.bvcmp =>
    rw [LawfulBEq.eq_of_beq H.left.right, BVCmp.eq_of_beq_eq_true H.right]
  case bvshOp.bvshOp =>
    rw [LawfulBEq.eq_of_beq H.left.right, BVShOp.eq_of_beq_eq_true H.right]
  case bvextract.bvextract =>
    rw [Nat.eq_of_beq_eq_true H.left.right]

instance : LawfulBEq BitVecConst where
  eq_of_beq := BitVecConst.eq_of_beq_eq_true
  rfl := BitVecConst.beq_refl

def BitVecConst.lamCheck : BitVecConst → LamSort
| .bvVal n _        => .base (.bv n)
| .bvofNat n        => .func (.base .nat) (.base (.bv n))
| .bvtoNat n        => .func (.base (.bv n)) (.base .nat)
| .bvofInt n        => .func (.base .int) (.base (.bv n))
| .bvtoInt n        => .func (.base (.bv n)) (.base .int)
| .bvmsb n          => .func (.base (.bv n)) (.base .bool)
| .bvaOp n _        => .func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n)))
| .bvneg n          => .func (.base (.bv n)) (.base (.bv n))
| .bvabs n          => .func (.base (.bv n)) (.base (.bv n))
| .bvcmp n prop? _ =>
  match prop? with
  | false => .func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool))
  | true => .func (.base (.bv n)) (.func (.base (.bv n)) (.base .prop))
| .bvand n          => .func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n)))
| .bvor n           => .func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n)))
| .bvxor n          => .func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n)))
| .bvnot n          => .func (.base (.bv n)) (.base (.bv n))
| .bvshOp n smt? _ =>
  match smt? with
  | false => .func (.base (.bv n)) (.func (.base .nat) (.base (.bv n)))
  | true  => .func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n)))
| .bvappend n m     => .func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv (Nat.add n m))))
| .bvextract n h l  => .func (.base (.bv n)) (.base (.bv (Nat.add (Nat.sub h l) 1)))
| .bvrepeat w i     => .func (.base (.bv w)) (.base (.bv (Nat.mul w i)))
| .bvzeroExtend w v => .func (.base (.bv w)) (.base (.bv v))
| .bvsignExtend w v => .func (.base (.bv w)) (.base (.bv v))

inductive BitVecConst.LamWF : BitVecConst → LamSort → Type
  | ofBvVal n i        : LamWF (.bvVal n i) (.base (.bv n))
  | ofBvofNat n        : LamWF (.bvofNat n) (.func (.base .nat) (.base (.bv n)))
  | ofBvtoNat n        : LamWF (.bvtoNat n) (.func (.base (.bv n)) (.base .nat))
  | ofBvofInt n        : LamWF (.bvofInt n) (.func (.base .int) (.base (.bv n)))
  | ofBvtoInt n        : LamWF (.bvtoInt n) (.func (.base (.bv n)) (.base .int))
  | ofBvmsb n          : LamWF (.bvmsb n) (.func (.base (.bv n)) (.base .bool))
  | ofBvaOp n op       : LamWF (.bvaOp n op) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))
  | ofBvneg n          : LamWF (.bvneg n) (.func (.base (.bv n)) (.base (.bv n)))
  | ofBvabs n          : LamWF (.bvabs n) (.func (.base (.bv n)) (.base (.bv n)))
  | ofBvcmp n op       : LamWF (.bvcmp n false op) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool)))
  | ofBvpropcmp n op   : LamWF (.bvcmp n true op) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base .prop)))
  | ofBvand n          : LamWF (.bvand n) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))
  | ofBvor n           : LamWF (.bvor n) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))
  | ofBvxor n          : LamWF (.bvxor n) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))
  | ofBvnot n          : LamWF (.bvnot n) (.func (.base (.bv n)) (.base (.bv n)))
  | ofBvshOp n op      : LamWF (.bvshOp n false op) (.func (.base (.bv n)) (.func (.base .nat) (.base (.bv n))))
  | ofBvsmtshOp n op   : LamWF (.bvshOp n true op) (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))
  | ofBvappend n m     : LamWF (.bvappend n m) (.func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv (Nat.add n m)))))
  | ofBvextract n h l  : LamWF (.bvextract n h l) (.func (.base (.bv n)) (.base (.bv (Nat.add (Nat.sub h l) 1))))
  | ofBvrepeat w i     : LamWF (.bvrepeat w i) (.func (.base (.bv w)) (.base (.bv (Nat.mul w i))))
  | ofBvzeroExtend w v : LamWF (.bvzeroExtend w v) (.func (.base (.bv w)) (.base (.bv v)))
  | ofBvsignExtend w v : LamWF (.bvsignExtend w v) (.func (.base (.bv w)) (.base (.bv v)))

def BitVecConst.LamWF.ofBvadd (n : Nat) := LamWF.ofBvaOp n .add

def BitVecConst.LamWF.ofBvsub (n : Nat) := LamWF.ofBvaOp n .sub

def BitVecConst.LamWF.ofBvmul (n : Nat) := LamWF.ofBvaOp n .mul

def BitVecConst.LamWF.ofBvudiv (n : Nat) := LamWF.ofBvaOp n .udiv

def BitVecConst.LamWF.ofBvurem (n : Nat) := LamWF.ofBvaOp n .urem

def BitVecConst.LamWF.ofBvsdiv (n : Nat) := LamWF.ofBvaOp n .sdiv

def BitVecConst.LamWF.ofBvsrem (n : Nat) := LamWF.ofBvaOp n .srem

def BitVecConst.LamWF.ofBvsmod (n : Nat) := LamWF.ofBvaOp n .smod

def BitVecConst.LamWF.ofBvult (n : Nat) := LamWF.ofBvcmp n .ult

def BitVecConst.LamWF.ofBvule (n : Nat) := LamWF.ofBvcmp n .ule

def BitVecConst.LamWF.ofBvslt (n : Nat) := LamWF.ofBvcmp n .slt

def BitVecConst.LamWF.ofBvsle (n : Nat) := LamWF.ofBvcmp n .sle

def BitVecConst.LamWF.ofBvpropult (n : Nat) := LamWF.ofBvpropcmp n .ult

def BitVecConst.LamWF.ofBvpropule (n : Nat) := LamWF.ofBvpropcmp n .ule

def BitVecConst.LamWF.ofBvpropslt (n : Nat) := LamWF.ofBvpropcmp n .slt

def BitVecConst.LamWF.ofBvpropsle (n : Nat) := LamWF.ofBvpropcmp n .sle

def BitVecConst.LamWF.ofBvshl (n : Nat) := LamWF.ofBvshOp n .shl

def BitVecConst.LamWF.ofBvlshr (n : Nat) := LamWF.ofBvshOp n .lshr

def BitVecConst.LamWF.ofBvashr (n : Nat) := LamWF.ofBvshOp n .ashr

def BitVecConst.LamWF.ofBvsmtshl (n : Nat) := LamWF.ofBvsmtshOp n .shl

def BitVecConst.LamWF.ofBvsmtlshr (n : Nat) := LamWF.ofBvsmtshOp n .lshr

def BitVecConst.LamWF.ofBvsmtashr (n : Nat) := LamWF.ofBvsmtshOp n .ashr

def BitVecConst.LamWF.unique {b : BitVecConst} {s₁ s₂ : LamSort}
  (bcwf₁ : LamWF b s₁) (bcwf₂ : LamWF b s₂) : s₁ = s₂ ∧ HEq bcwf₁ bcwf₂ := by
  cases bcwf₁ <;> cases bcwf₂ <;> trivial

def BitVecConst.LamWF.ofBitVecConst : (b : BitVecConst) → (s : LamSort) × BitVecConst.LamWF b s
| .bvVal n i        => ⟨.base (.bv n), .ofBvVal n i⟩
| .bvofNat n        => ⟨.func (.base .nat) (.base (.bv n)), .ofBvofNat n⟩
| .bvtoNat n        => ⟨.func (.base (.bv n)) (.base .nat), .ofBvtoNat n⟩
| .bvofInt n        => ⟨.func (.base .int) (.base (.bv n)), .ofBvofInt n⟩
| .bvtoInt n        => ⟨.func (.base (.bv n)) (.base .int), .ofBvtoInt n⟩
| .bvmsb n          => ⟨.func (.base (.bv n)) (.base .bool), .ofBvmsb n⟩
| .bvaOp n op       => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))), .ofBvaOp n op⟩
| .bvneg n          => ⟨.func (.base (.bv n)) (.base (.bv n)), .ofBvneg n⟩
| .bvabs n          => ⟨.func (.base (.bv n)) (.base (.bv n)), .ofBvabs n⟩
| .bvcmp n prop? op =>
  match prop? with
  | false => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool)), .ofBvcmp n op⟩
  | true => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base .prop)), .ofBvpropcmp n op⟩
| .bvand n          => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))), .ofBvand n⟩
| .bvor n           => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))), .ofBvor n⟩
| .bvxor n          => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))), .ofBvxor n⟩
| .bvnot n          => ⟨.func (.base (.bv n)) (.base (.bv n)), .ofBvnot n⟩
| .bvshOp n smt? op =>
  match smt? with
  | false => ⟨.func (.base (.bv n)) (.func (.base .nat) (.base (.bv n))), .ofBvshOp n op⟩
  | true  => ⟨.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))), .ofBvsmtshOp n op⟩
| .bvappend n m     => ⟨.func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv (Nat.add n m)))), .ofBvappend n m⟩
| .bvextract n h l  => ⟨.func (.base (.bv n)) (.base (.bv (Nat.add (Nat.sub h l) 1))), .ofBvextract n h l⟩
| .bvrepeat w i     => ⟨.func (.base (.bv w)) (.base (.bv (Nat.mul w i))), .ofBvrepeat w i⟩
| .bvzeroExtend w v => ⟨.func (.base (.bv w)) (.base (.bv v)), .ofBvzeroExtend w v⟩
| .bvsignExtend w v => ⟨.func (.base (.bv w)) (.base (.bv v)), .ofBvsignExtend w v⟩

def BitVecConst.lamWF_complete (wf : LamWF b s) : LamWF.ofBitVecConst b = ⟨s, wf⟩ := by
  cases wf <;> rfl

def BitVecConst.lamCheck_of_LamWF (H : LamWF b s) : b.lamCheck = s := by
  cases H <;> rfl

def BitVecConst.LamWF.ofCheck (H : b.lamCheck = s) : LamWF b s := by
  cases H; cases b <;> try constructor
  case bvcmp n prop? op => cases prop? <;> constructor
  case bvshOp n smt? op => cases smt? <;> constructor

inductive OtherConst
  /--
    SMT attribute application, with one term as ⟨attribute_value⟩
    `.app _ (attribute ⟨keyword⟩ ⟨attr_term⟩) ⟨term⟩ ⇔ ⟨term⟩ ⟨keyword⟩ (⟨attr_term⟩)`

    `smtAttr1T n s₁ s₂` is interpreted as `fun (_ : s₁) (x₂ : s₂) => x₂`,
    which we'll denote as `constId`. Note that the interpretation is
    polymorphic. However, it does not need special treatment like
    `∀, ∃, =`. This is because `constId A↑ B↑ = (constId A B)↑`, where
    `↑` stands for universe level lifting.
  -/
  | smtAttr1T : String → LamSort → LamSort → OtherConst
deriving Inhabited, Hashable, Lean.ToExpr

def OtherConst.reprAux : OtherConst → String
| .smtAttr1T n sattr s₂ => s!"smtAttr1T {n} {sattr} {s₂}"

def OtherConst.reprPrec (p : OtherConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.OtherConst.{p.reprAux}"
  | _ + 1 => f!"(.{p.reprAux})"

instance : Repr OtherConst where
reprPrec := OtherConst.reprPrec

inductive OtherConst.LamWF : OtherConst → LamSort → Type
  | ofSmtAttr1T n sattr sterm : LamWF (.smtAttr1T n sattr sterm) (.func sattr (.func sterm sterm))

def OtherConst.LamWF.ofOtherConst : (oc : OtherConst) → (s : LamSort) × OtherConst.LamWF oc s
| .smtAttr1T n sattr sterm => ⟨.func sattr (.func sterm sterm), .ofSmtAttr1T n sattr sterm⟩

def OtherConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF p s) → s.interp tyVal
| .ofSmtAttr1T _ sattr sterm => constId (a:=LamSort.interp tyVal sattr) (b:=LamSort.interp tyVal sterm)

def OtherConst.toString : OtherConst → String
| .smtAttr1T n _ _ => s!"attr[{n}]"

instance : ToString OtherConst where
  toString := OtherConst.toString

def OtherConst.beq : OtherConst → OtherConst → Bool
| .smtAttr1T n₁ sattr₁ sterm₁, .smtAttr1T n₂ sattr₂ sterm₂ =>
  n₁ == n₂ && sattr₁.beq sattr₂ && sterm₁.beq sterm₂

instance : BEq OtherConst where
  beq := OtherConst.beq

theorem OtherConst.beq_def {x y : OtherConst} : (x == y) = x.beq y := rfl

def OtherConst.beq_refl {o : OtherConst} : (o.beq o) = true := by
  cases o <;> unfold OtherConst.beq <;> simp [LamSort.beq_refl]

def OtherConst.eq_of_beq_eq_true {o₁ o₂ : OtherConst} (H : o₁.beq o₂) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> dsimp [beq] at H <;>
    rw [Bool.and_eq_true] at H <;> rw [Bool.and_eq_true] at H <;>
    try rw [LawfulBEq.eq_of_beq H.left.left]
  case smtAttr1T.smtAttr1T =>
    rw [LamSort.eq_of_beq_eq_true H.left.right, LamSort.eq_of_beq_eq_true H.right]

instance : LawfulBEq OtherConst where
  eq_of_beq := OtherConst.eq_of_beq_eq_true
  rfl := OtherConst.beq_refl

def OtherConst.lamCheck : OtherConst → LamSort
| .smtAttr1T _ sattr sterm => .func sattr (.func sterm sterm)

def OtherConst.interp (tyVal : Nat → Type u) : (o : OtherConst) → o.lamCheck.interp tyVal
| .smtAttr1T _ sattr sterm => fun (_ : sattr.interp tyVal) (term : sterm.interp tyVal) => term

def OtherConst.interp_equiv (tyVal : Nat → Type u) (ocwf : LamWF p s) :
  HEq (LamWF.interp tyVal ocwf) (interp tyVal p) := by
  cases ocwf <;> rfl

def OtherConst.LamWF.unique {o : OtherConst} {s₁ s₂ : LamSort}
  (ocwf₁ : LamWF o s₁) (ocwf₂ : LamWF o s₂) : s₁ = s₂ ∧ HEq ocwf₁ ocwf₂ := by
  cases ocwf₁ <;> cases ocwf₂ <;> trivial

theorem OtherConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (ocwf₁ : LamWF b₁ s₁) (ocwf₂ : LamWF b₂ s₂)
  (HBeq : b₁ = b₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (ocwf₁.interp tyVal₁) (ocwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases OtherConst.LamWF.unique ocwf₁ ocwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def OtherConst.lamWF_complete (wf : LamWF sc s) : LamWF.ofOtherConst sc = ⟨s, wf⟩ := by
  cases wf <;> rfl

def OtherConst.lamCheck_of_LamWF (H : LamWF sc s) : sc.lamCheck = s := by
  cases H <;> rfl

def OtherConst.LamWF.ofCheck (H : sc.lamCheck = s) : LamWF sc s := by
  cases H; cases sc <;> constructor

/--
  Interpreted constants
  Note that `eq`, `forallE`, `existE` have `ilVal/lamILTy`
    associated with them. During proof reconstruction, we should collect
    the sort arguments of all `eq, forallE, existE` that occurs in the
    proof into `ilVal`.
  For `ilVal`, we need to use `ILLift.ofIsomTy` to construct
    `ILLift` structures. The idea is that we want the interpretation
    of reified assumptions to be definitionally
    equal to the assumption (or `GLift.up` applied to the assumption, to
    be precise), so we'll have to use the specially designed
    `of(Eq/Forall/Exist)Lift` function.
  Note that at the end of the proof, we'll have a `LamTerm.base .falseE`,
    no `=, ∀, ∃` left, so whatever `(Eq/Forall/Exist)Lift`
    structure are within the `(eq/forall/lam)Val`, the final result
    will always interpret to `GLift.up False`.
-/
inductive LamBaseTerm
  | pcst     : PropConst   → LamBaseTerm
  | bcst     : BoolConst   → LamBaseTerm
  | ncst     : NatConst    → LamBaseTerm
  | icst     : IntConst    → LamBaseTerm
  | scst     : StringConst → LamBaseTerm
  | bvcst    : BitVecConst → LamBaseTerm
  | ocst     : OtherConst  → LamBaseTerm
  -- Versions of `eq, ∀, ∃, ite'` when we're importing external facts
  -- Note that the [import versions] of `eq, ∀, ∃, ite'` should only be used when
  --   we're importing external facts. When facts are imported, we call
  --   `resolveImport` on them and these [import versions] are turned into
  --   [non-import versions]
  | eqI      : Nat → LamBaseTerm
  | forallEI : Nat → LamBaseTerm
  | existEI  : Nat → LamBaseTerm
  | iteI     : Nat → LamBaseTerm
  -- Non-import versions of `eq, ∀, ∃`
  | eq       : LamSort → LamBaseTerm
  | forallE  : LamSort → LamBaseTerm
  | existE   : LamSort → LamBaseTerm
  | ite      : LamSort → LamBaseTerm
deriving Inhabited, Hashable, Lean.ToExpr

def LamBaseTerm.trueE := LamBaseTerm.pcst .trueE
def LamBaseTerm.falseE := LamBaseTerm.pcst .falseE
def LamBaseTerm.not := LamBaseTerm.pcst .not
def LamBaseTerm.and := LamBaseTerm.pcst .and
def LamBaseTerm.or := LamBaseTerm.pcst .or
def LamBaseTerm.imp := LamBaseTerm.pcst .imp
def LamBaseTerm.iff := LamBaseTerm.pcst .iff
def LamBaseTerm.ofProp := LamBaseTerm.bcst .ofProp
def LamBaseTerm.trueb := LamBaseTerm.bcst .trueb
def LamBaseTerm.falseb := LamBaseTerm.bcst .falseb
def LamBaseTerm.notb := LamBaseTerm.bcst .notb
def LamBaseTerm.andb := LamBaseTerm.bcst .andb
def LamBaseTerm.orb := LamBaseTerm.bcst .orb
def LamBaseTerm.natVal (n : Nat) := LamBaseTerm.ncst (.natVal n)
def LamBaseTerm.nadd := LamBaseTerm.ncst .nadd
def LamBaseTerm.nsub := LamBaseTerm.ncst .nsub
def LamBaseTerm.nmul := LamBaseTerm.ncst .nmul
def LamBaseTerm.ndiv := LamBaseTerm.ncst .ndiv
def LamBaseTerm.nmod := LamBaseTerm.ncst .nmod
def LamBaseTerm.nle := LamBaseTerm.ncst .nle
def LamBaseTerm.nlt := LamBaseTerm.ncst .nlt
def LamBaseTerm.nmax := LamBaseTerm.ncst .nmax
def LamBaseTerm.nmin := LamBaseTerm.ncst .nmin
def LamBaseTerm.iofNat := LamBaseTerm.icst .iofNat
def LamBaseTerm.inegSucc := LamBaseTerm.icst .inegSucc
def LamBaseTerm.ineg := LamBaseTerm.icst .ineg
def LamBaseTerm.iabs := LamBaseTerm.icst .iabs
def LamBaseTerm.iadd := LamBaseTerm.icst .iadd
def LamBaseTerm.isub := LamBaseTerm.icst .isub
def LamBaseTerm.imul := LamBaseTerm.icst .imul
def LamBaseTerm.idiv := LamBaseTerm.icst .idiv
def LamBaseTerm.imod := LamBaseTerm.icst .imod
def LamBaseTerm.iediv := LamBaseTerm.icst .iediv
def LamBaseTerm.iemod := LamBaseTerm.icst .iemod
def LamBaseTerm.ile := LamBaseTerm.icst .ile
def LamBaseTerm.ilt := LamBaseTerm.icst .ilt
def LamBaseTerm.imax := LamBaseTerm.icst .imax
def LamBaseTerm.imin := LamBaseTerm.icst .imin
def LamBaseTerm.strVal (s : String) := LamBaseTerm.scst (.strVal s)
def LamBaseTerm.slength := LamBaseTerm.scst .slength
def LamBaseTerm.sapp := LamBaseTerm.scst .sapp
def LamBaseTerm.sle := LamBaseTerm.scst .sle
def LamBaseTerm.slt := LamBaseTerm.scst .slt
def LamBaseTerm.sprefixof := LamBaseTerm.scst .sprefixof
def LamBaseTerm.srepall := LamBaseTerm.scst .srepall
def LamBaseTerm.bvVal (n i : Nat) := LamBaseTerm.bvcst (.bvVal n i)
def LamBaseTerm.bvofNat (n : Nat) := LamBaseTerm.bvcst (.bvofNat n)
def LamBaseTerm.bvtoNat (n : Nat) := LamBaseTerm.bvcst (.bvtoNat n)
def LamBaseTerm.bvofInt (n : Nat) := LamBaseTerm.bvcst (.bvofInt n)
def LamBaseTerm.bvtoInt (n : Nat) := LamBaseTerm.bvcst (.bvtoInt n)
def LamBaseTerm.bvmsb (n : Nat) := LamBaseTerm.bvcst (.bvmsb n)
def LamBaseTerm.bvadd (n : Nat) := LamBaseTerm.bvcst (.bvadd n)
def LamBaseTerm.bvsub (n : Nat) := LamBaseTerm.bvcst (.bvsub n)
def LamBaseTerm.bvneg (n : Nat) := LamBaseTerm.bvcst (.bvneg n)
def LamBaseTerm.bvabs (n : Nat) := LamBaseTerm.bvcst (.bvabs n)
def LamBaseTerm.bvmul (n : Nat) := LamBaseTerm.bvcst (.bvmul n)
def LamBaseTerm.bvudiv (n : Nat) := LamBaseTerm.bvcst (.bvudiv n)
def LamBaseTerm.bvurem (n : Nat) := LamBaseTerm.bvcst (.bvurem n)
def LamBaseTerm.bvsdiv (n : Nat) := LamBaseTerm.bvcst (.bvsdiv n)
def LamBaseTerm.bvsrem (n : Nat) := LamBaseTerm.bvcst (.bvsrem n)
def LamBaseTerm.bvsmod (n : Nat) := LamBaseTerm.bvcst (.bvsmod n)
def LamBaseTerm.bvult (n : Nat) := LamBaseTerm.bvcst (.bvult n)
def LamBaseTerm.bvule (n : Nat) := LamBaseTerm.bvcst (.bvule n)
def LamBaseTerm.bvslt (n : Nat) := LamBaseTerm.bvcst (.bvslt n)
def LamBaseTerm.bvsle (n : Nat) := LamBaseTerm.bvcst (.bvsle n)
def LamBaseTerm.bvpropult (n : Nat) := LamBaseTerm.bvcst (.bvpropult n)
def LamBaseTerm.bvpropule (n : Nat) := LamBaseTerm.bvcst (.bvpropule n)
def LamBaseTerm.bvpropslt (n : Nat) := LamBaseTerm.bvcst (.bvpropslt n)
def LamBaseTerm.bvpropsle (n : Nat) := LamBaseTerm.bvcst (.bvpropsle n)
def LamBaseTerm.bvand (n : Nat) := LamBaseTerm.bvcst (.bvand n)
def LamBaseTerm.bvor (n : Nat) := LamBaseTerm.bvcst (.bvor n)
def LamBaseTerm.bvxor (n : Nat) := LamBaseTerm.bvcst (.bvxor n)
def LamBaseTerm.bvnot (n : Nat) := LamBaseTerm.bvcst (.bvnot n)
def LamBaseTerm.bvshl (n : Nat) := LamBaseTerm.bvcst (.bvshl n)
def LamBaseTerm.bvlshr (n : Nat) := LamBaseTerm.bvcst (.bvlshr n)
def LamBaseTerm.bvashr (n : Nat) := LamBaseTerm.bvcst (.bvashr n)
def LamBaseTerm.bvsmtshl (n : Nat) := LamBaseTerm.bvcst (.bvsmtshl n)
def LamBaseTerm.bvsmtlshr (n : Nat) := LamBaseTerm.bvcst (.bvsmtlshr n)
def LamBaseTerm.bvsmtashr (n : Nat) := LamBaseTerm.bvcst (.bvsmtashr n)
def LamBaseTerm.bvappend (n m : Nat) := LamBaseTerm.bvcst (.bvappend n m)
def LamBaseTerm.bvextract (n h l : Nat) := LamBaseTerm.bvcst (.bvextract n h l)
def LamBaseTerm.bvrepeat (w i : Nat) := LamBaseTerm.bvcst (.bvrepeat w i)
def LamBaseTerm.bvzeroExtend (w v : Nat) := LamBaseTerm.bvcst (.bvzeroExtend w v)
def LamBaseTerm.bvsignExtend (w v : Nat) := LamBaseTerm.bvcst (.bvsignExtend w v)

def LamBaseTerm.isBcst : LamBaseTerm → Bool
| .bcst _ => true
| _       => false

def LamBaseTerm.isNcst : LamBaseTerm → Bool
| .ncst _ => true
| _       => false

def LamBaseTerm.isIcst : LamBaseTerm → Bool
| .icst _ => true
| _       => false

def LamBaseTerm.isScst : LamBaseTerm → Bool
| .scst _ => true
| _       => false

def LamBaseTerm.isBvcst : LamBaseTerm → Bool
| .bvcst _ => true
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

def LamBaseTerm.isIteI : LamBaseTerm → Bool
| .iteI _ => true
| _       => false

def LamBaseTerm.isEq : LamBaseTerm → Bool
| .eq _ => true
| _     => false

def LamBaseTerm.isForallE : LamBaseTerm → Bool
| .forallE _ => true
| _          => false

def LamBaseTerm.isExistE : LamBaseTerm → Bool
| .existE _ => true
| _         => false

def LamBaseTerm.isIte : LamBaseTerm → Bool
| .ite _ => true
| _      => false

def LamBaseTerm.reprPrec (l : LamBaseTerm) (n : Nat) :=
  let s :=
    match l with
    | .pcst pc    => f!"pcst {PropConst.reprPrec pc 1}"
    | .bcst bc    => f!"bcst {BoolConst.reprPrec bc 1}"
    | .ncst nc    => f!"ncst {NatConst.reprPrec nc 1}"
    | .icst ic    => f!"icst {IntConst.reprPrec ic 1}"
    | .scst sc    => f!"scst {StringConst.reprPrec sc 1}"
    | .bvcst bvc  => f!"bvcst {BitVecConst.reprPrec bvc 1}"
    | .ocst oc    => f!"ocst {OtherConst.reprPrec oc 1}"
    | .eqI n      => f!"eqI {n}"
    | .forallEI n => f!"forallEI {n}"
    | .existEI n  => f!"existEI {n}"
    | .iteI n     => f!"iteI {n}"
    | .eq s       => f!"eq {LamSort.reprPrec s 1}"
    | .forallE s  => f!"forallE {LamSort.reprPrec s 1}"
    | .existE s   => f!"existE {LamSort.reprPrec s 1}"
    | .ite n      => f!"ite {n}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamBaseTerm." ++ s
  else
    f!"(.{s})"

instance : Repr LamBaseTerm where
  reprPrec := LamBaseTerm.reprPrec

def LamBaseTerm.toString : LamBaseTerm → String
| .pcst pc    => s!"{pc}"
| .bcst bc    => s!"{bc}"
| .ncst nc    => s!"{nc}"
| .icst ic    => s!"{ic}"
| .scst sc    => s!"{sc}"
| .bvcst bvc  => s!"{bvc}"
| .ocst oc    => s!"{oc}"
| .eqI _      => "="
| .forallEI _ => "∀"
| .existEI _  => "∃"
| .iteI _     => "ite"
| .eq _       => "="
| .forallE _  => "∀"
| .existE _   => "∃"
| .ite _      => "ite"

instance : ToString LamBaseTerm where
  toString := LamBaseTerm.toString

def LamBaseTerm.beq : LamBaseTerm → LamBaseTerm → Bool
| .pcst pc₁,    .pcst pc₂    => pc₁.beq pc₂
| .bcst bc₁,    .bcst bc₂    => bc₁.beq bc₂
| .ncst nc₁,    .ncst nc₂    => NatConst.beq nc₁ nc₂
| .icst ic₁,    .icst ic₂    => IntConst.beq ic₁ ic₂
| .scst sc₁,    .scst sc₂    => StringConst.beq sc₁ sc₂
| .bvcst l₁,    .bvcst l₂    => BitVecConst.beq l₁ l₂
| .ocst o₁,     .ocst o₂     => OtherConst.beq o₁ o₂
| .eqI n₁,      .eqI n₂      => n₁.beq n₂
| .forallEI n₁, .forallEI n₂ => n₁.beq n₂
| .existEI n₁,  .existEI n₂  => n₁.beq n₂
| .iteI n₁,     .iteI n₂     => n₁.beq n₂
| .eq s₁,       .eq s₂       => s₁.beq s₂
| .forallE s₁,  .forallE s₂  => s₁.beq s₂
| .existE s₁,   .existE s₂   => s₁.beq s₂
| .ite s₁,      .ite s₂      => s₁.beq s₂
| _,            _            => false

instance : BEq LamBaseTerm where
  beq := LamBaseTerm.beq

def LamBaseTerm.beq_refl {b : LamBaseTerm} : (b.beq b) = true := by
  cases b <;> first | rfl | apply LamSort.beq_refl | apply Nat.beq_refl | skip
  case pcst pc => apply BEq.rfl (α := PropConst)
  case bcst bc => apply BEq.rfl (α := BoolConst)
  case ncst n => apply BEq.rfl (α := NatConst)
  case icst i => apply BEq.rfl (α := IntConst)
  case scst s => apply BEq.rfl (α := StringConst)
  case bvcst s => apply BEq.rfl (α := BitVecConst)
  case ocst o => apply BEq.rfl (α := OtherConst)

def LamBaseTerm.eq_of_beq_eq_true {b₁ b₂ : LamBaseTerm} (H : b₁.beq b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> (first | contradiction | rfl | apply congrArg) <;>
    (try apply LamSort.eq_of_beq_eq_true H) <;> (try apply Nat.eq_of_beq_eq_true H)
  case pcst.pcst.h pc₁ pc₂ => apply LawfulBEq.eq_of_beq (α := PropConst) H
  case bcst.bcst.h bc₁ bc₂ => apply LawfulBEq.eq_of_beq (α := BoolConst) H
  case ncst.ncst.h nc₁ nc₂ => apply LawfulBEq.eq_of_beq (α := NatConst) H
  case icst.icst.h n₁ n₂ => apply LawfulBEq.eq_of_beq (α := IntConst) H
  case scst.scst.h s₁ s₂ => apply LawfulBEq.eq_of_beq (α := StringConst) H
  case bvcst.bvcst.h v₁ v₂ => apply LawfulBEq.eq_of_beq (α := BitVecConst) H
  case ocst.ocst.h o₁ o₂ => apply LawfulBEq.eq_of_beq (α := OtherConst) H

instance : LawfulBEq LamBaseTerm where
  eq_of_beq := LamBaseTerm.eq_of_beq_eq_true
  rfl := LamBaseTerm.beq_refl

def LamBaseTerm.containsSort (b : LamBaseTerm) (s : LamSort) : Bool :=
  match b with
  | .pcst _     => false
  | .bcst _     => false
  | .ncst _     => false
  | .icst _     => false
  | .scst _     => false
  | .bvcst _    => false
  | .ocst _     => false
  | .eqI _      => false
  | .forallEI _ => false
  | .existEI _  => false
  | .iteI _     => false
  | .eq s'      => s'.contains s
  | .forallE s' => s'.contains s
  | .existE s'  => s'.contains s
  | .ite s'     => s'.contains s

structure LamTyVal where
  lamVarTy     : Nat → LamSort
  lamILTy      : Nat → LamSort
  lamEVarTy    : Nat → LamSort

instance : Inhabited LamTyVal where
  default := let func := fun _ => .atom 0; ⟨func, func, func⟩

def LamBaseTerm.lamCheck (ltv : LamTyVal) : LamBaseTerm → LamSort
| .pcst pc    => pc.lamCheck
| .bcst bc    => bc.lamCheck
| .ncst nc    => nc.lamCheck
| .icst ic    => ic.lamCheck
| .scst sc    => sc.lamCheck
| .bvcst bvc  => bvc.lamCheck
| .ocst oc    => oc.lamCheck
| .eqI n      =>
  let s := ltv.lamILTy n
  .func s (.func s (.base .prop))
| .forallEI n =>
  let s := ltv.lamILTy n
  .func (.func s (.base .prop)) (.base .prop)
| .existEI n  =>
  let s := ltv.lamILTy n
  .func (.func s (.base .prop)) (.base .prop)
| .iteI n     =>
  let s := ltv.lamILTy n
  .func (.base .prop) (.func s (.func s s))
| .eq s       => .func s (.func s (.base .prop))
| .forallE s  => .func (.func s (.base .prop)) (.base .prop)
| .existE s   => .func (.func s (.base .prop)) (.base .prop)
| .ite s      => .func (.base .prop) (.func s (.func s s))

inductive LamBaseTerm.LamWF (ltv : LamTyVal) : LamBaseTerm → LamSort → Type
  | ofPcst       : (pcwf : PropConst.LamWF pc s) → LamWF ltv (.pcst pc) s
  | ofBcst       : (bcwf : BoolConst.LamWF bc s) → LamWF ltv (.bcst bc) s
  | ofNcst       : (ncwf : NatConst.LamWF nc s) → LamWF ltv (.ncst nc) s
  | ofIcst       : (icwf : IntConst.LamWF ic s) → LamWF ltv (.icst ic) s
  | ofScst       : (scwf : StringConst.LamWF sc s) → LamWF ltv (.scst sc) s
  | ofBvcst      : (bvcwf : BitVecConst.LamWF bvc s) → LamWF ltv (.bvcst bvc) s
  | ofOcst       : (ocwf : OtherConst.LamWF oc s) → LamWF ltv (.ocst oc) s
  | ofEqI n      : LamWF ltv (.eqI n) (.func (ltv.lamILTy n) (.func (ltv.lamILTy n) (.base .prop)))
  | ofForallEI n : LamWF ltv (.forallEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
  | ofExistEI n  : LamWF ltv (.existEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
  | ofIteI n     : LamWF ltv (.iteI n) (.func (.base .prop) (.func (ltv.lamILTy n) (.func (ltv.lamILTy n) (ltv.lamILTy n))))
  | ofEq s       : LamWF ltv (.eq s) (.func s (.func s (.base .prop)))
  | ofForallE s  : LamWF ltv (.forallE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofExistE s   : LamWF ltv (.existE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofIte s      : LamWF ltv (.ite s) (.func (.base .prop) (.func s (.func s s)))

def LamBaseTerm.LamWF.unique {ltv : LamTyVal} {b : LamBaseTerm} {s₁ s₂ : LamSort}
  (lbwf₁ : LamWF ltv b s₁) (lbwf₂ : LamWF ltv b s₂) : s₁ = s₂ ∧ HEq lbwf₁ lbwf₂ := by
  cases lbwf₁ <;> cases lbwf₂ <;> try trivial
  case ofPcst.ofPcst pc wf₁ wf₂ =>
    rcases PropConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofBcst.ofBcst bc wf₁ wf₂ =>
    rcases BoolConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofNcst.ofNcst bc wf₁ wf₂ =>
    rcases NatConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofIcst.ofIcst ic wf₁ wf₂ =>
    rcases IntConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofScst.ofScst sc wf₁ wf₂ =>
    rcases StringConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofBvcst.ofBvcst bvc wf₁ wf₂ =>
    rcases BitVecConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofOcst.ofOcst oc wf₁ wf₂ =>
    rcases OtherConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial

def LamBaseTerm.LamWF.eVarIrrelevance
  (hLamVarTy : ltv₁.lamVarTy = ltv₂.lamVarTy)
  (hLamILTy : ltv₁.lamILTy = ltv₂.lamILTy)
  (lbwf : LamWF ltv₁ b s) : LamWF ltv₂ b s := by
  cases b <;> cases lbwf <;> (try constructor) <;> cases ltv₁ <;> cases ltv₂ <;>
    cases hLamVarTy <;> cases hLamILTy <;> first | constructor | assumption

abbrev LamBaseTerm.LamWF.ofTrueE {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofTrueE
abbrev LamBaseTerm.LamWF.ofFalseE {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofFalseE
abbrev LamBaseTerm.LamWF.ofNot {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofNot
abbrev LamBaseTerm.LamWF.ofAnd {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofAnd
abbrev LamBaseTerm.LamWF.ofOr {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofOr
abbrev LamBaseTerm.LamWF.ofImp {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofImp
abbrev LamBaseTerm.LamWF.ofIff {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofIff
abbrev LamBaseTerm.LamWF.ofOfProp {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofOfProp
abbrev LamBaseTerm.LamWF.ofTrueB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofTrueB
abbrev LamBaseTerm.LamWF.ofFalseB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofFalseB
abbrev LamBaseTerm.LamWF.ofNotB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofNotB
abbrev LamBaseTerm.LamWF.ofAndB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofAndB
abbrev LamBaseTerm.LamWF.ofOrB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofOrB
abbrev LamBaseTerm.LamWF.ofNatVal {ltv : LamTyVal} (n : Nat) := LamWF.ofNcst (ltv:=ltv) (.ofNatVal n)
abbrev LamBaseTerm.LamWF.ofNadd {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNadd
abbrev LamBaseTerm.LamWF.ofNsub {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNsub
abbrev LamBaseTerm.LamWF.ofNmul {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmul
abbrev LamBaseTerm.LamWF.ofNdiv {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNdiv
abbrev LamBaseTerm.LamWF.ofNmod {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmod
abbrev LamBaseTerm.LamWF.ofNle {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNle
abbrev LamBaseTerm.LamWF.ofNlt {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNlt
abbrev LamBaseTerm.LamWF.ofNmax {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmax
abbrev LamBaseTerm.LamWF.ofNmin {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmin
abbrev LamBaseTerm.LamWF.ofIOfNat {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIOfNat
abbrev LamBaseTerm.LamWF.ofINegSucc {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofINegSucc
abbrev LamBaseTerm.LamWF.ofIneg {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIneg
abbrev LamBaseTerm.LamWF.ofIabs {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIabs
abbrev LamBaseTerm.LamWF.ofIadd {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIadd
abbrev LamBaseTerm.LamWF.ofIsub {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIsub
abbrev LamBaseTerm.LamWF.ofImul {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImul
abbrev LamBaseTerm.LamWF.ofIdiv {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIdiv
abbrev LamBaseTerm.LamWF.ofImod {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImod
abbrev LamBaseTerm.LamWF.ofIediv {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIediv
abbrev LamBaseTerm.LamWF.ofIemod {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIemod
abbrev LamBaseTerm.LamWF.ofIle {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIle
abbrev LamBaseTerm.LamWF.ofIlt {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIlt
abbrev LamBaseTerm.LamWF.ofImax {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImax
abbrev LamBaseTerm.LamWF.ofImin {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImin
abbrev LamBaseTerm.LamWF.ofStrVal {ltv : LamTyVal} (s : String) := LamWF.ofScst (ltv:=ltv) (.ofStrVal s)
abbrev LamBaseTerm.LamWF.ofSlength {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSlength
abbrev LamBaseTerm.LamWF.ofSapp {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSapp
abbrev LamBaseTerm.LamWF.ofSle {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSle
abbrev LamBaseTerm.LamWF.ofSlt {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSlt
abbrev LamBaseTerm.LamWF.ofSprefixof {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSprefixof
abbrev LamBaseTerm.LamWF.ofSrepall {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSrepall
abbrev LamBaseTerm.LamWF.ofBvVal {ltv : LamTyVal} (n i : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvVal n i)
abbrev LamBaseTerm.LamWF.ofBvofNat {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvofNat n)
abbrev LamBaseTerm.LamWF.ofBvtoNat {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvtoNat n)
abbrev LamBaseTerm.LamWF.ofBvofInt {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvofInt n)
abbrev LamBaseTerm.LamWF.ofBvtoInt {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvtoInt n)
abbrev LamBaseTerm.LamWF.ofBvmsb {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvmsb n)
abbrev LamBaseTerm.LamWF.ofBvadd {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvadd n)
abbrev LamBaseTerm.LamWF.ofBvsub {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsub n)
abbrev LamBaseTerm.LamWF.ofBvneg {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvneg n)
abbrev LamBaseTerm.LamWF.ofBvabs {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvabs n)
abbrev LamBaseTerm.LamWF.ofBvmul {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvmul n)
abbrev LamBaseTerm.LamWF.ofBvudiv {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvudiv n)
abbrev LamBaseTerm.LamWF.ofBvurem {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvurem n)
abbrev LamBaseTerm.LamWF.ofBvsdiv {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsdiv n)
abbrev LamBaseTerm.LamWF.ofBvsrem {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsrem n)
abbrev LamBaseTerm.LamWF.ofBvsmod {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmod n)
abbrev LamBaseTerm.LamWF.ofBvult {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvult n)
abbrev LamBaseTerm.LamWF.ofBvule {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvule n)
abbrev LamBaseTerm.LamWF.ofBvslt {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvslt n)
abbrev LamBaseTerm.LamWF.ofBvsle {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsle n)
abbrev LamBaseTerm.LamWF.ofBvand {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvand n)
abbrev LamBaseTerm.LamWF.ofBvor {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvor n)
abbrev LamBaseTerm.LamWF.ofBvxor {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvxor n)
abbrev LamBaseTerm.LamWF.ofBvnot {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvnot n)
abbrev LamBaseTerm.LamWF.ofBvshl {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvshl n)
abbrev LamBaseTerm.LamWF.ofBvlshr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvlshr n)
abbrev LamBaseTerm.LamWF.ofBvashr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvashr n)
abbrev LamBaseTerm.LamWF.ofBvsmtshl {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmtshl n)
abbrev LamBaseTerm.LamWF.ofBvsmtlshr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmtlshr n)
abbrev LamBaseTerm.LamWF.ofBvsmtashr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmtashr n)
abbrev LamBaseTerm.LamWF.ofBvappend {ltv : LamTyVal} (n m : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvappend n m)
abbrev LamBaseTerm.LamWF.ofBvextract {ltv : LamTyVal} (n h l : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvextract n h l)
abbrev LamBaseTerm.LamWF.ofBvrepeat {ltv : LamTyVal} (w i : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvrepeat w i)
abbrev LamBaseTerm.LamWF.ofBvzeroExtend {ltv : LamTyVal} (w v : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvzeroExtend w v)
abbrev LamBaseTerm.LamWF.ofBvsignExtend {ltv : LamTyVal} (w v : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsignExtend w v)

def LamBaseTerm.LamWF.getPcst (wf : LamWF ltv (.pcst pc) s) : PropConst.LamWF pc s :=
  match wf with | .ofPcst pcwf => pcwf

def LamBaseTerm.LamWF.getBcst (wf : LamWF ltv (.bcst bc) s) : BoolConst.LamWF bc s :=
  match wf with | .ofBcst bcwf => bcwf

def LamBaseTerm.LamWF.getNcst (wf : LamWF ltv (.ncst nc) s) : NatConst.LamWF nc s :=
  match wf with | .ofNcst ncwf => ncwf

def LamBaseTerm.LamWF.getIcst (wf : LamWF ltv (.icst ic) s) : IntConst.LamWF ic s :=
  match wf with | .ofIcst icwf => icwf

def LamBaseTerm.LamWF.getScst (wf : LamWF ltv (.scst sc) s) : StringConst.LamWF sc s :=
  match wf with | .ofScst scwf => scwf

def LamBaseTerm.LamWF.getBvcst (wf : LamWF ltv (.bvcst bvc) s) : BitVecConst.LamWF bvc s :=
  match wf with | .ofBvcst bvcwf => bvcwf

def LamBaseTerm.LamWF.ofLamBaseTerm (ltv : LamTyVal) : (b : LamBaseTerm) → (s : LamSort) × LamBaseTerm.LamWF ltv b s
| .pcst pc    => have ⟨s, wf⟩ := PropConst.LamWF.ofPropConst pc; ⟨s, .ofPcst wf⟩
| .bcst bc    => have ⟨s, wf⟩ := BoolConst.LamWF.ofBoolConst bc; ⟨s, .ofBcst wf⟩
| .ncst nc    => have ⟨s, wf⟩ := NatConst.LamWF.ofNatConst nc; ⟨s, .ofNcst wf⟩
| .icst ic    => have ⟨s, wf⟩ := IntConst.LamWF.ofIntConst ic; ⟨s, .ofIcst wf⟩
| .scst sc    => have ⟨s, wf⟩ := StringConst.LamWF.ofStringConst sc; ⟨s, .ofScst wf⟩
| .bvcst bvc  => have ⟨s, wf⟩ := BitVecConst.LamWF.ofBitVecConst bvc; ⟨s, .ofBvcst wf⟩
| .ocst oc    => have ⟨s, wf⟩ := OtherConst.LamWF.ofOtherConst oc; ⟨s, .ofOcst wf⟩
| .eqI n      => ⟨.func _ (.func _ (.base .prop)), .ofEqI n⟩
| .forallEI n => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallEI n⟩
| .existEI n  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistEI n⟩
| .iteI n     => ⟨.func (.base .prop) (.func _ (.func _ _)), .ofIteI n⟩
| .eq s       => ⟨.func _ (.func _ (.base .prop)), .ofEq s⟩
| .forallE s  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallE s⟩
| .existE s   => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistE s⟩
| .ite s      => ⟨.func (.base .prop) (.func _ (.func _ _)), .ofIte s⟩

def LamBaseTerm.lamWF_complete (wf : LamWF ltv b s) : LamWF.ofLamBaseTerm ltv b = ⟨s, wf⟩ := by
  cases wf <;> try rfl
  case ofPcst pc wf => dsimp [LamWF.ofLamBaseTerm]; rw [PropConst.lamWF_complete wf]
  case ofBcst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [BoolConst.lamWF_complete wf]
  case ofNcst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [NatConst.lamWF_complete wf]
  case ofIcst ic wf => dsimp [LamWF.ofLamBaseTerm]; rw [IntConst.lamWF_complete]
  case ofScst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [StringConst.lamWF_complete wf]
  case ofBvcst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [BitVecConst.lamWF_complete wf]
  case ofOcst oc wf => dsimp [LamWF.ofLamBaseTerm]; rw [OtherConst.lamWF_complete wf]

def LamBaseTerm.lamCheck_of_LamWF (H : LamWF ltv b s) : b.lamCheck ltv = s := by
  cases H <;> try rfl
  case ofPcst bc wf => apply PropConst.lamCheck_of_LamWF wf
  case ofBcst bc wf => apply BoolConst.lamCheck_of_LamWF wf
  case ofNcst bc wf => apply NatConst.lamCheck_of_LamWF wf
  case ofIcst bc wf => apply IntConst.lamCheck_of_LamWF wf
  case ofScst sc wf => apply StringConst.lamCheck_of_LamWF wf
  case ofBvcst sc wf => apply BitVecConst.lamCheck_of_LamWF wf
  case ofOcst oc wf => apply OtherConst.lamCheck_of_LamWF wf

def LamBaseTerm.LamWF.ofCheck (H : b.lamCheck ltv = s) : LamWF ltv b s := by
  cases H; cases b <;> constructor
  case refl.pcst.pcwf => apply PropConst.LamWF.ofCheck; rfl
  case refl.bcst.bcwf => apply BoolConst.LamWF.ofCheck; rfl
  case refl.ncst.ncwf => apply NatConst.LamWF.ofCheck; rfl
  case refl.icst.icwf => apply IntConst.LamWF.ofCheck; rfl
  case refl.scst.scwf => apply StringConst.LamWF.ofCheck; rfl
  case refl.bvcst.bvcwf => apply BitVecConst.LamWF.ofCheck; rfl
  case refl.ocst.ocwf => apply OtherConst.LamWF.ofCheck; rfl

structure ILLift (β : Type u) where
  eqL     : EqLift.{u + 1, u} β
  forallL : ForallLift.{u + 1, u, 0, 0} β
  existL  : ExistLift.{u + 1, u} β
  iteL    : IteLift.{u + 1, u} β

noncomputable def ILLift.ofIsomTy {α : Sort u} {β : Type v} (I : IsomType α β) : ILLift β :=
  ⟨EqLift.ofIsomTy I, ForallLift.ofIsomTy I, ExistLift.ofIsomTy I, IteLift.ofIsomTy I⟩

noncomputable def ILLift.default (β : Type u) : ILLift β :=
  ⟨EqLift.default β, ForallLift.default β, ExistLift.default β, IteLift.default β⟩

structure LamValuation extends LamTyVal where
  tyVal    : Nat → Type u
  varVal   : ∀ (n : Nat), (lamVarTy n).interp tyVal
  ilVal    : ∀ (n : Nat), ILLift.{u} ((lamILTy n).interp tyVal)
  eVarVal  : ∀ (n : Nat), (lamEVarTy n).interp tyVal

def PropConst.interp (tyVal : Nat → Type u) : (p : PropConst) → p.lamCheck.interp tyVal
| .trueE      => GLift.up True
| .falseE     => GLift.up False
| .not        => notLift
| .and        => andLift
| .or         => orLift
| .imp        => impLift
| .iff        => iffLift

def PropConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF p s) → s.interp tyVal
| .ofTrueE      => GLift.up True
| .ofFalseE     => GLift.up False
| .ofNot        => notLift
| .ofAnd        => andLift
| .ofOr         => orLift
| .ofImp        => impLift
| .ofIff        => iffLift

theorem PropConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (pcwf₁ : LamWF p₁ s₁) (pcwf₂ : LamWF p₂ s₂)
  (HBeq : p₁ = p₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (pcwf₁.interp tyVal₁) (pcwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases PropConst.LamWF.unique pcwf₁ pcwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def PropConst.interp_equiv (tyVal : Nat → Type u) (pcwf : LamWF p s) :
  HEq (LamWF.interp tyVal pcwf) (interp tyVal p) := by
  cases pcwf <;> rfl

noncomputable def BoolConst.interp (tyVal : Nat → Type u) : (b : BoolConst) → b.lamCheck.interp tyVal
| .ofProp => ofPropLift
| .trueb  => GLift.up true
| .falseb => GLift.up false
| .notb   => notbLift
| .andb   => andbLift
| .orb    => orbLift

noncomputable def BoolConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF b s) → s.interp tyVal
| .ofOfProp => ofPropLift
| .ofTrueB  => GLift.up true
| .ofFalseB => GLift.up false
| .ofNotB   => notbLift
| .ofAndB   => andbLift
| .ofOrB    => orbLift

theorem BoolConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (bcwf₁ : LamWF b₁ s₁) (bcwf₂ : LamWF b₂ s₂)
  (HBeq : b₁ = b₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (bcwf₁.interp tyVal₁) (bcwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases BoolConst.LamWF.unique bcwf₁ bcwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def BoolConst.interp_equiv (tyVal : Nat → Type u) (bcwf : LamWF b s) :
  HEq (LamWF.interp tyVal bcwf) (interp tyVal b) := by
  cases bcwf <;> rfl

def NatConst.interp (tyVal : Nat → Type u) : (n : NatConst) → n.lamCheck.interp tyVal
| .natVal n => GLift.up n
| .nadd     => naddLift
| .nsub     => nsubLift
| .nmul     => nmulLift
| .ndiv     => ndivLift
| .nmod     => nmodLift
| .nle      => nleLift
| .nlt      => nltLift
| .nmax     => nmaxLift
| .nmin     => nminLift

def NatConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF i s) → s.interp tyVal
| .ofNatVal n => GLift.up n
| .ofNadd     => naddLift
| .ofNsub     => nsubLift
| .ofNmul     => nmulLift
| .ofNdiv     => ndivLift
| .ofNmod     => nmodLift
| .ofNle      => nleLift
| .ofNlt      => nltLift
| .ofNmax     => nmaxLift
| .ofNmin     => nminLift

theorem NatConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (ncwf₁ : LamWF n₁ s₁) (ncwf₂ : LamWF n₂ s₂)
  (HBeq : n₁ = n₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (ncwf₁.interp tyVal₁) (ncwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases NatConst.LamWF.unique ncwf₁ ncwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def NatConst.interp_equiv (tyVal : Nat → Type u) (ncwf : LamWF n s) :
  HEq (LamWF.interp tyVal ncwf) (interp tyVal n) := by
  cases ncwf <;> rfl

def IntConst.interp (tyVal : Nat → Type u) : (i : IntConst) → i.lamCheck.interp tyVal
| .iofNat   => iofNatLift
| .inegSucc => inegSuccLift
| .ineg     => inegLift
| .iabs     => iabsLift
| .iadd     => iaddLift
| .isub     => isubLift
| .imul     => imulLift
| .idiv     => idivLift
| .imod     => imodLift
| .iediv    => iedivLift
| .iemod    => iemodLift
| .ile      => ileLift
| .ilt      => iltLift
| .imax     => imaxLift
| .imin     => iminLift

def IntConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF i s) → s.interp tyVal
| .ofIOfNat   => iofNatLift
| .ofINegSucc => inegSuccLift
| .ofIneg     => inegLift
| .ofIabs     => iabsLift
| .ofIadd     => iaddLift
| .ofIsub     => isubLift
| .ofImul     => imulLift
| .ofIdiv     => idivLift
| .ofImod     => imodLift
| .ofIediv    => iedivLift
| .ofIemod    => iemodLift
| .ofIle      => ileLift
| .ofIlt      => iltLift
| .ofImax     => imaxLift
| .ofImin     => iminLift

theorem IntConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (icwf₁ : LamWF i₁ s₁) (icwf₂ : LamWF i₂ s₂)
  (HBeq : i₁ = i₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (icwf₁.interp tyVal₁) (icwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases IntConst.LamWF.unique icwf₁ icwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def IntConst.interp_equiv (tyVal : Nat → Type u) (icwf : LamWF i s) :
  HEq (LamWF.interp tyVal icwf) (interp tyVal i) := by
  cases icwf <;> rfl

def StringConst.interp (tyVal : Nat → Type u) : (b : StringConst) → b.lamCheck.interp tyVal
| .strVal s  => GLift.up s
| .slength   => slengthLift
| .sapp      => sappLift
| .sle       => sleLift
| .slt       => sltLift
| .sprefixof => sprefixofLift
| .srepall   => srepallLift

def StringConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF i s) → s.interp tyVal
| .ofStrVal s  => GLift.up s
| .ofSlength   => slengthLift
| .ofSapp      => sappLift
| .ofSle       => sleLift
| .ofSlt       => sltLift
| .ofSprefixof => sprefixofLift
| .ofSrepall   => srepallLift

theorem StringConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (scwf₁ : LamWF sc₁ s₁) (scwf₂ : LamWF sc₂ s₂)
  (HBeq : sc₁ = sc₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (scwf₁.interp tyVal₁) (scwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases StringConst.LamWF.unique scwf₁ scwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def StringConst.interp_equiv (tyVal : Nat → Type u) (scwf : LamWF sc s) :
  HEq (LamWF.interp tyVal scwf) (interp tyVal sc) := by
  cases scwf <;> rfl

def BVAOp.interp (n : Nat) : (op : BVAOp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n)
| .add  => bvaddLift n
| .sub  => bvsubLift n
| .mul  => bvmulLift n
| .udiv => bvudivLift n
| .urem => bvuremLift n
| .sdiv => bvsdivLift n
| .srem => bvsremLift n
| .smod => bvsmodLift n

def BVCmp.interp (n : Nat) : (op : BVCmp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} Bool
| .ult => bvultLift n
| .ule => bvuleLift n
| .slt => bvsltLift n
| .sle => bvsleLift n

def BVCmp.propinterp (n : Nat) : (op : BVCmp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} Prop
| .ult => bvpropultLift n
| .ule => bvpropuleLift n
| .slt => bvpropsltLift n
| .sle => bvpropsleLift n

def BVShOp.interp (n : Nat) : (op : BVShOp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} Nat → GLift.{1, u} (BitVec n)
| .shl         => bvshlLift n
| .lshr        => bvlshrLift n
| .ashr        => bvashrLift n

def BVShOp.smtinterp (n : Nat) : (op : BVShOp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n)
| .shl         => bvsmtshlLift n
| .lshr        => bvsmtlshrLift n
| .ashr        => bvsmtashrLift n

def BitVecConst.interp (tyVal : Nat → Type u) : (b : BitVecConst) → b.lamCheck.interp tyVal
| .bvVal n i         => GLift.up (BitVec.ofNat n i)
| .bvofNat n         => bvofNatLift n
| .bvtoNat n         => bvtoNatLift n
| .bvofInt n         => bvofIntLift n
| .bvtoInt n         => bvtoIntLift n
| .bvmsb n           => bvmsbLift n
| .bvaOp n op        => op.interp n
| .bvneg n           => bvnegLift n
| .bvabs n           => bvabsLift n
| .bvcmp n false op  => op.interp n
| .bvcmp n true op   => op.propinterp n
| .bvand n           => bvandLift n
| .bvor n            => bvorLift n
| .bvxor n           => bvxorLift n
| .bvnot n           => bvnotLift n
| .bvshOp n false op => op.interp n
| .bvshOp n true op  => op.smtinterp n
| .bvappend n m      => bvappendLift n m
| .bvextract n h l   => bvextractLift n h l
| .bvrepeat w i      => bvrepeatLift w i
| .bvzeroExtend w v  => bvzeroExtendLift w v
| .bvsignExtend w v  => bvsignExtendLift w v

def BitVecConst.LamWF.interp (tyVal : Nat → Type u) : (lwf : LamWF b s) → s.interp tyVal
| .ofBvVal n i        => GLift.up (BitVec.ofNat n i)
| .ofBvofNat n        => bvofNatLift n
| .ofBvtoNat n        => bvtoNatLift n
| .ofBvofInt n        => bvofIntLift n
| .ofBvtoInt n        => bvtoIntLift n
| .ofBvmsb n          => bvmsbLift n
| .ofBvaOp n op       => op.interp n
| .ofBvneg n          => bvnegLift n
| .ofBvabs n          => bvabsLift n
| .ofBvcmp n op       => op.interp n
| .ofBvpropcmp n op   => op.propinterp n
| .ofBvand n          => bvandLift n
| .ofBvor n           => bvorLift n
| .ofBvxor n          => bvxorLift n
| .ofBvnot n          => bvnotLift n
| .ofBvshOp n op      => op.interp n
| .ofBvsmtshOp n op   => op.smtinterp n
| .ofBvappend n m     => bvappendLift n m
| .ofBvextract n h l  => bvextractLift n h l
| .ofBvrepeat w i     => bvrepeatLift w i
| .ofBvzeroExtend w v => bvzeroExtendLift w v
| .ofBvsignExtend w v => bvsignExtendLift w v

theorem BitVecConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : Nat → Type u) (bcwf₁ : LamWF b₁ s₁) (bcwf₂ : LamWF b₂ s₂)
  (HBeq : b₁ = b₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (bcwf₁.interp tyVal₁) (bcwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases BitVecConst.LamWF.unique bcwf₁ bcwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

def BitVecConst.interp_equiv (tyVal : Nat → Type u) (bcwf : LamWF b s) :
  HEq (LamWF.interp tyVal bcwf) (interp tyVal b) := by
  cases bcwf <;> rfl

noncomputable def LamBaseTerm.interp (lval : LamValuation.{u}) : (b : LamBaseTerm) → (b.lamCheck lval.toLamTyVal).interp lval.tyVal
| .pcst pc    => pc.interp lval.tyVal
| .bcst bc    => bc.interp lval.tyVal
| .ncst nc    => nc.interp lval.tyVal
| .icst ic    => ic.interp lval.tyVal
| .scst sc    => sc.interp lval.tyVal
| .bvcst bvc  => bvc.interp lval.tyVal
| .ocst oc    => oc.interp lval.tyVal
| .eqI n      => (lval.ilVal n).eqL.eqF
| .forallEI n => (lval.ilVal n).forallL.forallF
| .existEI n  => (lval.ilVal n).existL.existF
| .iteI n     => (lval.ilVal n).iteL.iteF
| .eq s       => eqLiftFn (s.interp lval.tyVal)
| .forallE s  => forallLiftFn (s.interp lval.tyVal)
| .existE s   => existLiftFn (s.interp lval.tyVal)
| .ite s      => iteLiftFn (s.interp lval.tyVal)

noncomputable def LamBaseTerm.LamWF.interp (lval : LamValuation.{u}) : (lwf : LamWF lval.toLamTyVal b s) → s.interp lval.tyVal
| .ofPcst wf    => wf.interp lval.tyVal
| .ofBcst wf    => wf.interp lval.tyVal
| .ofNcst wf    => wf.interp lval.tyVal
| .ofIcst wf    => wf.interp lval.tyVal
| .ofScst wf    => wf.interp lval.tyVal
| .ofBvcst wf   => wf.interp lval.tyVal
| .ofOcst wf    => wf.interp lval.tyVal
| .ofEqI n      => (lval.ilVal n).eqL.eqF
| .ofForallEI n => (lval.ilVal n).forallL.forallF
| .ofExistEI n  => (lval.ilVal n).existL.existF
| .ofIteI n     => (lval.ilVal n).iteL.iteF
| .ofEq s       => @eqLiftFn (s.interp lval.tyVal)
| .ofForallE s  => @forallLiftFn (s.interp lval.tyVal)
| .ofExistE s   => @existLiftFn (s.interp lval.tyVal)
| .ofIte s      => iteLiftFn (s.interp lval.tyVal)

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
          cases lwf₁ <;> cases lwf₂ <;> dsimp [interp] <;> try apply HEq.rfl
          case ofPcst => apply PropConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofBcst => apply BoolConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofNcst => apply NatConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofIcst => apply IntConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofScst => apply StringConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofBvcst => apply BitVecConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofOcst => apply OtherConst.LamWF.interp_lvalIrrelevance <;> rfl

def LamBaseTerm.interp_equiv (lval : LamValuation.{u})
  (lwf : LamWF lval.toLamTyVal b s) :
  HEq (LamWF.interp lval lwf) (interp lval b) := by
  cases lwf <;> try rfl
  case ofPcst => apply PropConst.interp_equiv
  case ofBcst => apply BoolConst.interp_equiv
  case ofNcst => apply NatConst.interp_equiv
  case ofIcst => apply IntConst.interp_equiv
  case ofScst => apply StringConst.interp_equiv
  case ofBvcst => apply BitVecConst.interp_equiv
  case ofOcst => apply OtherConst.interp_equiv

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
    apply IH.mpr; apply Nat.lt_pred_iff_succ_lt.mp; exact h
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

noncomputable def LamWF.interp.{u} (lval : LamValuation.{u}) :
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
      (pushLCtxsDep_substxs _ _ _ List.reverse_cons HList.reverse_cons)]
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
        apply HEq.trans (pushLCtxsDep_ge _ (Nat.le_of_eq List.length_reverse))
        rw [List.length_reverse, Nat.sub_self]; rfl

theorem LamWF.interp_eqForallEF
  {wf : LamWF lval.toLamTyVal ⟨pushLCtx s lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEF wf)) = (∀ x,
    GLift.down (LamWF.interp lval (pushLCtx s lctx) (pushLCtxDep x lctxTerm) wf)) := rfl

theorem LamWF.interp_eqForallEFN'
  {lval : LamValuation.{u}} {lctxTerm : ∀ n, (lctx n).interp lval.tyVal}
  {wf : LamWF lval.toLamTyVal ⟨pushLCtxs ls lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEFN' wf)) = (∀ xs,
    GLift.down (LamWF.interp lval (pushLCtxs ls lctx) (pushLCtxsDep xs lctxTerm) wf)) := by
  generalize LamWF.mkForallEFN' wf = wfMkF
  induction ls generalizing t
  case nil =>
    dsimp [mkForallEFN, interp]
    conv =>
      enter [2]; rw [IsomType.eqForall HList.nil_IsomType.{0, u + 1, u + 1}]
      rw [PUnit.eqForall]; unfold HList.nil_IsomType; dsimp
      dsimp [pushLCtxs, pushLCtxsDep, Nat.blt, Nat.ble]
    apply congrArg; apply interp_substWF
  case cons s ls IH =>
    revert wfMkF; rw [List.reverse_cons, LamTerm.mkForallEFN_append_singleton]; intro wfMkF
    apply Eq.trans (IH (wf:=LamWF.fromMkForallEFN' wfMkF) _)
    conv =>
      enter [2]; rw [IsomType.eqForall HList.cons_IsomType]; rw [Prod.eqForall']
      unfold HList.cons_IsomType; dsimp; enter [xs, x]
    apply forall_congr; intro xs
    rw [interp_app, interp_base, interp_lam, eq_of_heq (LamBaseTerm.interp_equiv _ _)]
    apply forall_congr; intro x
    apply congrArg; apply eq_of_heq; apply interp_heq <;> try rfl
    case HLCtxTyEq => rw [pushLCtxs_cons]
    case HLCtxTermEq => apply HEq.symm; apply pushLCtxsDep_cons

theorem LamWF.interp_eqForallEFN
  {lval : LamValuation.{u}} {ls : List LamSort} {lctxTerm : ∀ n, (lctx n).interp lval.tyVal}
  {wf : LamWF lval.toLamTyVal ⟨pushLCtxs ls.reverse lctx, t, .base .prop⟩} :
  GLift.down (LamWF.interp lval lctx lctxTerm (.mkForallEFN wf)) = (∀ xs,
    GLift.down (LamWF.interp lval (pushLCtxs ls.reverse lctx) (pushLCtxsDep xs lctxTerm) wf)) := by
  apply Eq.trans _ interp_eqForallEFN'; apply congrArg
  apply eq_of_heq; apply interp_heq <;> try rfl
  rw [List.reverse_reverse]

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
      apply congr_hd_heq (f₂:=fun lx =>valPre (HList.cons lx lctxTerm)) (x₂:=lx) <;> try rfl
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
          apply Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hlt
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

theorem LamTerm.forallEFBody_forallEFTys_eq (wft : LamWF ltv ⟨lctx, t, s⟩) :
  t = LamTerm.mkForallEFN t.getForallEFBody t.getForallEFTys := by
  generalize hsize' : t.size = n
  have hsize : t.size ≤ n := by cases hsize'; apply Nat.le_refl
  clear hsize'; induction n generalizing lctx t s
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
            dsimp [getForallEFTys, getForallEFBody, mkForallEFN]
            cases wft.getFn.getBase; cases wft.getArg
            case ofLam wfBody =>
              rw [← IH wfBody]; rfl
              have hsize' := Nat.le_trans size_app_gt_size_arg hsize
              apply Nat.le_of_succ_le_succ (Nat.le_of_succ_le hsize')

end Auto.Embedding.Lam
