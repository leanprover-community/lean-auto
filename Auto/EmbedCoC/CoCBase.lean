module

public import Lean
public import Auto.EmbedLam.LCtx
public import Auto.EmbedCoC.CoCSort

@[expose] public section

namespace Auto.Embedding.CoC

/--
  The generators of the universe levels of the sorts of the embedded system, where
  `u` and `v` are level parameters. They are the single source of truth for the
  sorts, see `CoCLevel`
-/
meta def CoCLevelGen : List Lean.Level :=
  [0, 1, 2, .param `u, .succ (.param `u), .param `v, .succ (.param `v)]

/--
  The universe levels of the sorts of the embedded system: the 18 simplest levels of
  the closure of `CoCLevelGen` under `max` and `imax`. `CoCSort` has one constructor
  per level, named after it, and the functions on sorts are generated from it, see
  `Auto.EmbedCoC.CoCSort`
-/
meta def CoCLevel : List Lean.Level := simplestLevels (maxesClosure CoCLevelGen) 18

/--
  The sorts of the embedded system, one per level of `CoCLevel`, e.g. `CoCSort.prop`
  is `Prop` and `CoCSort.«u+1»` is `Type u`. A level parameter can be `0`, so e.g.
  `Sort u` is `Prop` when `u` is `0`: only the sorts whose levels are successors are
  known to be nonzero
-/
mkSortType CoCSort from CoCLevel deriving Inhabited, DecidableEq, Hashable, Lean.ToExpr

inductive PropConst
  | trueE    : PropConst -- Propositional `true`
  | falseE   : PropConst -- Propositional `false`
  | not      : PropConst -- Propositional `not`
  | and      : PropConst -- Propositional `and`
  | or       : PropConst -- Propositional `or`
  | imp      : PropConst -- Propositional `imp`
  | iff      : PropConst -- Propositional `iff`
deriving Inhabited, DecidableEq, Hashable, Lean.ToExpr

inductive BoolConst
  | ofProp
  | trueb  -- Boolean `true`
  | falseb -- Boolean `false`
  | notb   -- Boolean `not`
  | andb   -- Boolean `and`
  | orb    -- Boolean `or`
deriving Inhabited, DecidableEq, Hashable, Lean.ToExpr

inductive NatConst
  | natVal (n : Nat)
  | nadd | nsub | nmul | ndiv | nmod
  | nle | nlt | nmax | nmin
deriving Inhabited, DecidableEq, Hashable, Lean.ToExpr

inductive CoCBaseTerm
  /-- `Sort s` -/
  | sort : CoCSort → CoCBaseTerm
  | bool
  | nat
  | pcst : PropConst → CoCBaseTerm
  | bcst : BoolConst → CoCBaseTerm
  | ncst : NatConst → CoCBaseTerm
deriving Inhabited, DecidableEq, Hashable, Lean.ToExpr

/--
  Terms of the embedded system. Applications and binders carry annotations that
  a standard presentation leaves implicit, so that a term can be interpreted
  without first inferring its type (cf. Streicher, *Semantics of Type Theory*,
  1991). The model could not recover them:
  * Lean cannot prove `∀`-types injective, so the type of `fn` cannot be taken
    apart into `argTy` and `resTy` in the model. For the same reason `λ` carries the
    type of its body, so that a `β`-redex whose annotations agree is interpreted
    with the same type family on both sides
  * When the domain of a binder is empty, the sort of its body is never observed
-/
inductive CoCTerm
  /-- Bound variables represented using de bruijn index -/
  | b : Nat → CoCTerm
  /-- Base terms -/
  | t : CoCBaseTerm → CoCTerm
  /--
    Function application annotated with the type of the function:
    `CoCTerm.a <s'> <argTy> <resTy> <fn> <arg>` applies `fn : ∀ x : argTy, resTy`
    to `arg`. `resTy` is under the binder `x`, and `resTy : Sort s'`
  -/
  | a : CoCSort → CoCTerm → CoCTerm → CoCTerm → CoCTerm → CoCTerm
  /--
    `CoCTerm.λ <s'> <argTy> <resTy> <body>`, where `body : resTy` and `resTy : Sort s'`,
    both under the binder
  -/
  | «λ» : CoCSort → CoCTerm → CoCTerm → CoCTerm → CoCTerm
  /-- `CoCTerm.∀ <s'> <argTy> <bodyTy>`, where `bodyTy : Sort s'` -/
  | «∀» : CoCSort → CoCTerm → CoCTerm → CoCTerm
deriving Inhabited, DecidableEq, Hashable, Lean.ToExpr

@[reducible] def CoCSort.toCoCTerm (s : CoCSort) : CoCTerm := .t (.sort s)

/--
  The sort of `Sort s`, or `none` when `s + 1` is not a `CoCSort`. Closure under
  successor is exactly what would make the tower infinite, so it is truncated at
  the top sorts. Generated from `CoCLevel`, see `Auto.EmbedCoC.CoCSort`
-/
mkSortSucc CoCSort.succ for CoCSort from CoCLevel

/--
  The sort of `∀ x : A, B` where `A : Sort s` and `B : Sort s'`, i.e.
  `Sort (Level.imax s s')`, or `none` when that level is not a `CoCSort`. Each `none`
  is a ∀-formation that the embedding cannot express. `imax s s'` is `0` when `s'`
  is `0`, which is the impredicativity of `Prop`, and `max s s'` otherwise. A level
  parameter can be `0`, so e.g. `max 1 u` is not `u`, and `imax (u+1) u` is not
  `u+1`. Generated from `CoCLevel`, see `Auto.EmbedCoC.CoCSort`
-/
mkSortJoin CoCSort.join for CoCSort from CoCLevel

/--
  Map the free bound variables of `t` with `f`, where `idx` is the number of
  binders already entered. Mirrors `Auto.Embedding.Lam.LamTerm.mapBVarAt`
-/
def CoCTerm.mapBVarAt (idx : Nat) (f : Nat → Nat) (t : CoCTerm) : CoCTerm :=
  match t with
  | .b n                     => .b (mapAt idx f n)
  | .t bt                    => .t bt
  | .a s' argTy resTy fn arg =>
    .a s' (argTy.mapBVarAt idx f) (resTy.mapBVarAt (.succ idx) f)
      (fn.mapBVarAt idx f) (arg.mapBVarAt idx f)
  | .«λ» s' argTy resTy body =>
    .«λ» s' (argTy.mapBVarAt idx f) (resTy.mapBVarAt (.succ idx) f) (body.mapBVarAt (.succ idx) f)
  | .«∀» s' argTy bodyTy     => .«∀» s' (argTy.mapBVarAt idx f) (bodyTy.mapBVarAt (.succ idx) f)

/-- Lift the bound variables of `t` that are `≥ idx` by `lvl` -/
def CoCTerm.bvarLiftsIdx (idx lvl : Nat) := CoCTerm.mapBVarAt idx (fun x => Nat.add x lvl)

/-- Lift all free bound variables of `t` by `lvl` -/
@[reducible] def CoCTerm.bvarLifts := CoCTerm.bvarLiftsIdx 0

/--
  Substitute `arg` for the bound variable at index `idx` in `body`, decrementing
  the free bound variables of `body` above `idx`. Mirrors
  `Auto.Embedding.Lam.LamTerm.instantiateAt`
-/
def CoCTerm.instantiateAt (idx : Nat) (arg : CoCTerm) : (body : CoCTerm) → CoCTerm
| .b n                      => pushLCtxAt (arg.bvarLifts idx) idx CoCTerm.b n
| .t bt                     => .t bt
| .a s' argTy resTy fn arg' =>
  .a s' (CoCTerm.instantiateAt idx arg argTy)
     (CoCTerm.instantiateAt (.succ idx) arg resTy)
     (CoCTerm.instantiateAt idx arg fn)
     (CoCTerm.instantiateAt idx arg arg')
| .«λ» s' argTy resTy body  =>
  .«λ» s' (CoCTerm.instantiateAt idx arg argTy) (CoCTerm.instantiateAt (.succ idx) arg resTy)
    (CoCTerm.instantiateAt (.succ idx) arg body)
| .«∀» s' argTy bodyTy      =>
  .«∀» s' (CoCTerm.instantiateAt idx arg argTy) (CoCTerm.instantiateAt (.succ idx) arg bodyTy)

/-- Substitute `arg` for the innermost bound variable -/
@[reducible] def CoCTerm.instantiate1 := CoCTerm.instantiateAt 0

/-- The non-dependent function type `argTy → resTy`, where `resTy : Sort s'` -/
@[reducible] def CoCTerm.mkFunc (s' : CoCSort) (argTy resTy : CoCTerm) : CoCTerm :=
  .«∀» s' argTy (resTy.bvarLifts 1)

/-- `Prop`, i.e. `Sort 0` -/
@[reducible] def sort0 : CoCTerm := .t (.sort .prop)
/-- `Type 0`, i.e. `Sort 1` -/
@[reducible] def sort1 : CoCTerm := .t (.sort .«1»)
@[reducible] def tyBool : CoCTerm := .t .bool
@[reducible] def tyNat : CoCTerm := .t .nat

/--
  The types of the constants: simple types over `Prop`, `Bool` and `Nat`. They are
  all in `Sort 1`, so `ConstTy.toCoCTerm` annotates every arrow with `.«1»`.

  `ConstTy` is not part of the `CoCTerm` syntax. It is a utility
  that describes the types of the constants, so that `CoCBaseTerm.check`, the
  values of the constants in the model and their typing lemmas can be written
  once for all constants rather than case by case
-/
inductive ConstTy
  | prop | bool | nat
  | func : ConstTy → ConstTy → ConstTy
deriving Inhabited, Hashable, Lean.ToExpr

def ConstTy.toCoCTerm : ConstTy → CoCTerm
| .prop     => sort0
| .bool     => tyBool
| .nat      => tyNat
| .func σ τ => .mkFunc .«1» σ.toCoCTerm τ.toCoCTerm

def PropConst.constTy : PropConst → ConstTy
| .trueE | .falseE         => .prop
| .not                     => .func .prop .prop
| .and | .or | .imp | .iff => .func .prop (.func .prop .prop)

def BoolConst.constTy : BoolConst → ConstTy
| .ofProp          => .func .prop .bool
| .trueb | .falseb => .bool
| .notb            => .func .bool .bool
| .andb | .orb     => .func .bool (.func .bool .bool)

def NatConst.constTy : NatConst → ConstTy
| .natVal _ => .nat
| .nadd | .nsub | .nmul | .ndiv | .nmod | .nmax | .nmin => .func .nat (.func .nat .nat)
| .nle | .nlt => .func .nat (.func .nat .prop)

/--
  The type of a base term, or `none` when it is a sort whose successor is not a
  `CoCSort`. Base terms are closed, so this does not depend on a local context
-/
def CoCBaseTerm.check : CoCBaseTerm → Option CoCTerm
| .sort s  => s.succ.map CoCSort.toCoCTerm
| .bool    => some sort1
| .nat     => some sort1
| .pcst pc => some pc.constTy.toCoCTerm
| .bcst bc => some bc.constTy.toCoCTerm
| .ncst nc => some nc.constTy.toCoCTerm

end Auto.Embedding.CoC
