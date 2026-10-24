module

public import Lean
public import Auto.Embedding.Lift
public import Auto.Embedding.LCtx
public import Auto.Lib.ExprExtra
public import Auto.Lib.NatExtra
public import Auto.Lib.IntExtra
public import Auto.Lib.HEqExtra
public import Auto.Lib.ListExtra

@[expose] public section

/-! Interpreted base sorts `LamBaseSort`, simple types `LamSort` and their valuation `TyVal` -/

namespace Auto.Embedding.Lam

open ToExprExtra

/--
  Types that are declared after `lean-auto` (e.g. Mathlib's `Real`), but
  which we want to treat as interpreted sorts. Their interpretations
  are supplied by the valuation (`TyVal.later`), together with the
  interpretations of their associated constants (see `LamBase/Later.lean`)
-/
inductive LaterType
  | real    : LaterType
  | complex : LaterType
deriving Hashable, Inhabited, Lean.ToExpr

def LaterType.reprPrec (t : LaterType) (n : Nat) :=
  let str :=
    match t with
    | .real => "real"
    | .complex => "complex"
  if n == 0 then
    f!"Auto.Embedding.Lam.LaterType." ++ str
  else
    f!"(.{str})"

instance : Repr LaterType where
  reprPrec t n := t.reprPrec n

def LaterType.toString : LaterType → String
| .real => "Real"
| .complex => "Complex"

instance : ToString LaterType where
  toString := LaterType.toString

def LaterType.beq : LaterType → LaterType → Bool
| .real,    .real    => true
| .complex, .complex => true
| _,        _        => false

instance : BEq LaterType where
  beq := LaterType.beq

theorem LaterType.beq_refl : {t : LaterType} → (t.beq t) = true
| .real    => rfl
| .complex => rfl

theorem LaterType.eq_of_beq_eq_true {t₁ t₂ : LaterType} (H : t₁.beq t₂) : t₁ = t₂ := by
  cases t₁ <;> cases t₂ <;> first | rfl | contradiction

instance : LawfulBEq LaterType where
  eq_of_beq := LaterType.eq_of_beq_eq_true
  rfl := LaterType.beq_refl

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
  | later  : LaterType → LamBaseSort -- Interpreted by `TyVal.later`
deriving Hashable, Inhabited, Lean.ToExpr

def LamBaseSort.string := LamBaseSort.isto0 .xH

def LamBaseSort.empty := LamBaseSort.isto0 (.xO .xH)

def LamBaseSort.real := LamBaseSort.later .real

def LamBaseSort.complex := LamBaseSort.later .complex

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
    | .later t => s!"later {LaterType.reprPrec t 1}"
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
| .later t => s!"{t}"

instance : ToString LamBaseSort where
  toString := LamBaseSort.toString

def LamBaseSort.beq : LamBaseSort → LamBaseSort → Bool
| .prop,     .prop     => true
| .bool,     .bool     => true
| .nat,      .nat      => true
| .int,      .int      => true
| .isto0 p₁, .isto0 p₂ => p₁.beq p₂
| .bv n,     .bv m     => n.beq m
| .later t₁, .later t₂ => t₁.beq t₂
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
| .later t => LaterType.beq_refl (t := t)

theorem LamBaseSort.eq_of_beq_eq_true {b₁ b₂ : LamBaseSort} : b₁.beq b₂ → b₁ = b₂ :=
  match b₁, b₂ with
  | .prop,    .prop    => fun _ => rfl
  | .bool,    .bool    => fun _ => rfl
  | .nat,     .nat     => fun _ => rfl
  | .int,     .int     => fun _ => rfl
  | .isto0 p, .isto0 q => fun H => Pos.eq_of_beq_eq_true H ▸ rfl
  | .bv n,    .bv m    => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .later s, .later t => fun H => LaterType.eq_of_beq_eq_true (t₁ := s) (t₂ := t) H ▸ rfl
  | .prop,    .bool    => fun H => by cases H
  | .prop,    .nat     => fun H => by cases H
  | .prop,    .int     => fun H => by cases H
  | .prop,    .isto0 p => fun H => by cases H
  | .prop,    .bv m    => fun H => by cases H
  | .prop,    .later t => fun H => by cases H
  | .bool,    .prop    => fun H => by cases H
  | .bool,    .nat     => fun H => by cases H
  | .bool,    .int     => fun H => by cases H
  | .bool,    .isto0 p => fun H => by cases H
  | .bool,    .bv m    => fun H => by cases H
  | .bool,    .later t => fun H => by cases H
  | .nat,     .prop    => fun H => by cases H
  | .nat,     .bool    => fun H => by cases H
  | .nat,     .int     => fun H => by cases H
  | .nat,     .isto0 p => fun H => by cases H
  | .nat,     .bv m    => fun H => by cases H
  | .nat,     .later t => fun H => by cases H
  | .int,     .prop    => fun H => by cases H
  | .int,     .bool    => fun H => by cases H
  | .int,     .nat     => fun H => by cases H
  | .int,     .isto0 p => fun H => by cases H
  | .int,     .bv m    => fun H => by cases H
  | .int,     .later t => fun H => by cases H
  | .isto0 p, .prop    => fun H => by cases H
  | .isto0 p, .bool    => fun H => by cases H
  | .isto0 p, .nat     => fun H => by cases H
  | .isto0 p, .int     => fun H => by cases H
  | .isto0 p, .bv m    => fun H => by cases H
  | .isto0 p, .later t => fun H => by cases H
  | .bv n,    .prop    => fun H => by cases H
  | .bv n,    .bool    => fun H => by cases H
  | .bv n,    .nat     => fun H => by cases H
  | .bv n,    .int     => fun H => by cases H
  | .bv n,    .isto0 p => fun H => by cases H
  | .bv n,    .later t => fun H => by cases H
  | .later s, .prop    => fun H => by cases H
  | .later s, .bool    => fun H => by cases H
  | .later s, .nat     => fun H => by cases H
  | .later s, .int     => fun H => by cases H
  | .later s, .isto0 p => fun H => by cases H
  | .later s, .bv m    => fun H => by cases H

instance : LawfulBEq LamBaseSort where
  eq_of_beq := LamBaseSort.eq_of_beq_eq_true
  rfl := LamBaseSort.beq_refl

@[reducible] def LamBaseSort.isto0_interp.{u} : Pos → Type u
| .xH     => GLift String
| .xO .xH => GLift Empty
| _       => GLift Empty

@[reducible] def LamBaseSort.interp.{u} (later : LaterType → Type u) : LamBaseSort → Type u
| .prop    => GLift Prop
| .bool    => GLift Bool
| .nat     => GLift Nat
| .int     => GLift Int
| .isto0 p => isto0_interp p
| .bv n    => GLift (BitVec n)
| .later t => later t

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

/-- Valuation of sorts -/
structure TyVal where
  /-- Interpretation of `.atom n` -/
  atom  : Nat → Type u
  /-- Interpretation of `.base (.later t)` -/
  later : LaterType → Type u

@[reducible] def LamSort.interp.{u} (val : TyVal.{u}) : LamSort → Type u
| .atom n => val.atom n
| .base b => b.interp val.later
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

end Auto.Embedding.Lam
