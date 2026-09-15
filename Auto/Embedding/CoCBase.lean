module

public import Lean
public import Auto.Lib.TreeList
public import Auto.Embedding.LCtx

@[expose] public section

namespace Auto.Embedding.CoC

inductive SortConst
  /-- `Sort 1` -/
  | «1»
  /-- `Sort 2` -/
  | «2»
  /-- `Sort u` -/
  | «u»
  /-- `Type u` -/
  | «u+1»
  /-- `Sort v` -/
  | «v»
  /-- `Type v` -/
  | «v+1»

inductive PropConst
  | trueE    : PropConst -- Propositional `true`
  | falseE   : PropConst -- Propositional `false`
  | not      : PropConst -- Propositional `not`
  | and      : PropConst -- Propositional `and`
  | or       : PropConst -- Propositional `or`
  | imp      : PropConst -- Propositional `imp`
  | iff      : PropConst -- Propositional `iff`
deriving Inhabited, Hashable, Lean.ToExpr

inductive BoolConst
  | ofProp
  | trueb  -- Boolean `true`
  | falseb -- Boolean `false`
  | notb   -- Boolean `not`
  | andb   -- Boolean `and`
  | orb    -- Boolean `or`
deriving Inhabited, Hashable, Lean.ToExpr

inductive NatConst
  | natVal (n : Nat)
  | nadd | nsub | nmul | ndiv | nmod
  | nle | nlt | nmax | nmin
deriving Inhabited, Hashable, Lean.ToExpr

inductive CoCBaseTerm
  /-- Lean `Prop`, i.e. `Sort 0` -/
  | prop
  /-- Lean Sorts, e.g. `Type 1`, `Sort u`, `Type v`. Excluding `Sort 0` since we already have `prop` -/
  | type : SortConst → CoCBaseTerm
  | bool
  | nat
  | pcst : PropConst → CoCBaseTerm
  | bcst : BoolConst → CoCBaseTerm
  | ncst : NatConst → CoCBaseTerm

inductive CoCTerm
  /-- Bound variables represented using de bruijn index -/
  | b : Nat → CoCTerm
  /-- Base terms -/
  | t : CoCBaseTerm → CoCTerm
  /--
    Function application with argument type annotated:
    `CoCTerm.a <argTy> <fn> <arg>`
  -/
  | a : CoCTerm → CoCTerm → CoCTerm → CoCTerm
  | «λ» : CoCTerm → CoCTerm → CoCTerm
  | «∀» : CoCTerm → CoCTerm → CoCTerm

/--
  The sorts of the embedded system: `Prop`, i.e. `Sort 0`, together with the
  nonzero sorts `SortConst`
-/
inductive CoCSort
  | prop
  | type : SortConst → CoCSort

@[reducible] def CoCSort.toBaseTerm : CoCSort → CoCBaseTerm
| .prop   => .prop
| .type s => .type s

@[reducible] def CoCSort.toCoCTerm (s : CoCSort) : CoCTerm := .t s.toBaseTerm

/--
  `Sort s ⊔ Sort s'`, i.e. `Sort (Level.max s s')`, or `none` when that level is
  not in `SortConst`. Note that `u` and `v` are arbitrary levels, so e.g.
  `max 1 u` is not `u`
-/
def SortConst.max : SortConst → SortConst → Option SortConst
  -- Both levels concrete
  | .«1», .«1»     => some .«1»
  | .«1», .«2»     => some .«2»
  | .«2», .«1»     => some .«2»
  | .«2», .«2»     => some .«2»
  -- `max 1 (w + 1) = (max 0 w) + 1 = w + 1`, since `0 ≤ w`
  | .«1», .«u+1»   => some .«u+1»
  | .«u+1», .«1»   => some .«u+1»
  | .«1», .«v+1»   => some .«v+1»
  | .«v+1», .«1»   => some .«v+1»
  -- Same level parameter, so the larger offset wins
  | .«u», .«u»     => some .«u»
  | .«u», .«u+1»   => some .«u+1»
  | .«u+1», .«u»   => some .«u+1»
  | .«u+1», .«u+1» => some .«u+1»
  | .«v», .«v»     => some .«v»
  | .«v», .«v+1»   => some .«v+1»
  | .«v+1», .«v»   => some .«v+1»
  | .«v+1», .«v+1» => some .«v+1»
  -- `max 2 u`, `max 2 (u+1)`, `max u v`, `max (u+1) (v+1)`, ... are not in
  -- `SortConst`. Each `none` here is a ∀-formation the embedding cannot express
  | _, _           => none

/--
  The sort of `Sort s`, or `none` when `s + 1` is not in `SortConst`. Closure
  under successor is exactly what would make the tower infinite, so it is
  truncated at `Sort 2`, `Sort (u+1)` and `Sort (v+1)`
-/
def CoCSort.succ : CoCSort → Option CoCSort
| .prop        => some (.type .«1»)   -- `Sort 0 : Sort 1`
| .type .«1»   => some (.type .«2»)   -- `Sort 1 : Sort 2`
| .type .«u»   => some (.type .«u+1»)
| .type .«v»   => some (.type .«v+1»)
| .type .«2»   => none               -- `Sort 3` is not in `SortConst`
| .type .«u+1» => none               -- `Sort (u+2)` is not in `SortConst`
| .type .«v+1» => none               -- `Sort (v+2)` is not in `SortConst`

/--
  The sort of `∀ x : A, B` where `A : Sort s` and `B : Sort s'`, i.e.
  `Sort (Level.imax s s')`. Total in its second argument at `Prop`, which is
  the impredicativity of `Prop`; otherwise partial, see `SortConst.max`
-/
def CoCSort.join : CoCSort → CoCSort → Option CoCSort
| _,        .prop    => some .prop         -- `imax _ 0 = 0`
| .prop,    .type s  => some (.type s)     -- `max 0 s = s`
| .type s,  .type s' => (s.max s').map CoCSort.type

/--
  Map the free bound variables of `t` with `f`, where `idx` is the number of
  binders already entered. Mirrors `Auto.Embedding.Lam.LamTerm.mapBVarAt`
-/
def CoCTerm.mapBVarAt (idx : Nat) (f : Nat → Nat) (t : CoCTerm) : CoCTerm :=
  match t with
  | .b n              => .b (mapAt idx f n)
  | .t bt             => .t bt
  | .a argTy fn arg   => .a (argTy.mapBVarAt idx f) (fn.mapBVarAt idx f) (arg.mapBVarAt idx f)
  | .«λ» argTy body   => .«λ» (argTy.mapBVarAt idx f) (body.mapBVarAt (.succ idx) f)
  | .«∀» argTy bodyTy => .«∀» (argTy.mapBVarAt idx f) (bodyTy.mapBVarAt (.succ idx) f)

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
| .b n              => pushLCtxAt (arg.bvarLifts idx) idx CoCTerm.b n
| .t bt             => .t bt
| .a argTy fn arg'  =>
  .a (CoCTerm.instantiateAt idx arg argTy)
     (CoCTerm.instantiateAt idx arg fn)
     (CoCTerm.instantiateAt idx arg arg')
| .«λ» argTy body   =>
  .«λ» (CoCTerm.instantiateAt idx arg argTy) (CoCTerm.instantiateAt (.succ idx) arg body)
| .«∀» argTy bodyTy =>
  .«∀» (CoCTerm.instantiateAt idx arg argTy) (CoCTerm.instantiateAt (.succ idx) arg bodyTy)

/-- Substitute `arg` for the innermost bound variable -/
@[reducible] def CoCTerm.instantiate1 := CoCTerm.instantiateAt 0

/-- The non-dependent function type `argTy → resTy` -/
@[reducible] def CoCTerm.mkFunc (argTy resTy : CoCTerm) : CoCTerm :=
  .«∀» argTy (resTy.bvarLifts 1)

/-- `Prop`, i.e. `Sort 0` -/
@[reducible] def sort0 : CoCTerm := .t .prop
/-- `Type 0`, i.e. `Sort 1` -/
@[reducible] def sort1 : CoCTerm := .t (.type .«1»)
@[reducible] def tyBool : CoCTerm := .t .bool
@[reducible] def tyNat : CoCTerm := .t .nat

def PropConst.check : PropConst → CoCTerm
| .trueE  => sort0
| .falseE => sort0
| .not    => .mkFunc sort0 sort0
| .and    => .mkFunc sort0 (.mkFunc sort0 sort0)
| .or     => .mkFunc sort0 (.mkFunc sort0 sort0)
| .imp    => .mkFunc sort0 (.mkFunc sort0 sort0)
| .iff    => .mkFunc sort0 (.mkFunc sort0 sort0)

def BoolConst.check : BoolConst → CoCTerm
| .ofProp => .mkFunc sort0 tyBool
| .trueb  => tyBool
| .falseb => tyBool
| .notb   => .mkFunc tyBool tyBool
| .andb   => .mkFunc tyBool (.mkFunc tyBool tyBool)
| .orb    => .mkFunc tyBool (.mkFunc tyBool tyBool)

def NatConst.check : NatConst → CoCTerm
| .natVal _ => tyNat
| .nadd | .nsub | .nmul | .ndiv | .nmod | .nmax | .nmin =>
  .mkFunc tyNat (.mkFunc tyNat tyNat)
| .nle | .nlt => .mkFunc tyNat (.mkFunc tyNat sort0)

/--
  The type of a base term, or `none` when it is a sort whose successor is not in
  `SortConst`. Base terms are closed, so this does not depend on a local context
-/
def CoCBaseTerm.check : CoCBaseTerm → Option CoCTerm
| .prop    => (CoCSort.prop.succ).map CoCSort.toCoCTerm
| .type s  => ((CoCSort.type s).succ).map CoCSort.toCoCTerm
| .bool    => some sort1
| .nat     => some sort1
| .pcst pc => some pc.check
| .bcst bc => some bc.check
| .ncst nc => some nc.check

/--
  Look up de Bruijn index `n` in local context `lctx`. `TreeList.push` appends at
  the end, so the innermost binder is the last entry and index `n` is entry
  `lctx.length - 1 - n`
-/
def lctxGet (lctx : TreeList CoCTerm) (n : Nat) (h : n < lctx.length) : CoCTerm :=
  lctx[lctx.length - 1 - n]'(by omega)

-- CoC Judgements, `Γ ⊢ term : type`
-- **TODO**: conversion (`β` and the `Bool`/`Nat` δ-rules) is still missing, so
-- `ofApp` currently demands that the argument's type match `argTy` syntactically
inductive CoCJ : TreeList CoCTerm → CoCTerm → CoCTerm → Type
  /--
    -------------
      Γ ⊢ c : T

    where `T` is the type of the base term `c`. Base terms are closed, so this
    holds in every `Γ`, which is why no weakening rule is needed. Sort formation
    (`Sort s : Sort (s+1)`) is the `.prop` / `.type` case of `CoCBaseTerm.check`
  -/
  | ofBase
      {lctx : TreeList CoCTerm} (b : CoCBaseTerm) {ty : CoCTerm}
      (H : b.check = some ty) :
    CoCJ lctx (.t b) ty
  /--
    `Γ = Γ', x : A, Δ`, where `Δ` has length `n`

    ----------------------------------
      Γ', x : A, Δ ⊢ (.b n) : ↑ⁿ⁺¹ A

    `A` is stored relative to `Γ'`, so it is lifted by `n + 1` to be read in `Γ`
  -/
  | ofBVar
      {lctx : TreeList CoCTerm} (n : Nat) (h : n < lctx.length) :
    CoCJ lctx (.b n) ((lctxGet lctx n h).bvarLifts (n + 1))
  /--
      Γ ⊢ (∀ x : A, B) : Sort s    Γ, x : A ⊢ b : B
    ---------------------------------------------------
                Γ ⊢ (λ x : A, b) : (∀ x : A, B)

    `resSort` is explicit because it cannot be recovered by unification: it
    occurs only under `CoCSort.toCoCTerm`, which Lean will not invert.

    The first premise is the whole ∀-type rather than just `Γ ⊢ A : Sort s`.
    Because `CoCSort.join` is partial, the two are not interchangeable here: the
    weaker premise would admit a λ whose type has no sort at all
  -/
  | ofLam
      {lctx : TreeList CoCTerm} {argTy : CoCTerm}
      (bodyTy : CoCTerm) (body : CoCTerm) (resSort : CoCSort)
      (HForall : CoCJ lctx (.«∀» argTy bodyTy) resSort.toCoCTerm)
      (H : CoCJ (lctx.push argTy) body bodyTy) :
    CoCJ lctx (.«λ» argTy body) (.«∀» argTy bodyTy)
  /--
      Γ ⊢ A : Sort s    Γ, x : A ⊢ B : Sort s'    join s s' = some s''
    -----------------------------------------------------------------------
                      Γ ⊢ (∀ x : A, B) : Sort s''
  -/
  | ofForall
      {lctx : TreeList CoCTerm} {argTy bodyTy : CoCTerm}
      (argSort bodySort resSort : CoCSort)
      (HArgTy : CoCJ lctx argTy argSort.toCoCTerm)
      (HBodyTy : CoCJ (lctx.push argTy) bodyTy bodySort.toCoCTerm)
      (HJoin : argSort.join bodySort = some resSort) :
    CoCJ lctx (.«∀» argTy bodyTy) resSort.toCoCTerm
  /--
      Γ ⊢ f : (∀ x : A, B)    Γ ⊢ a : A
    ---------------------------------------
            Γ ⊢ f a : B[a / x]
  -/
  | ofApp
      {lctx : TreeList CoCTerm}
      (argTy : CoCTerm) {resTy : CoCTerm} {fn : CoCTerm} {arg : CoCTerm}
      (HFn : CoCJ lctx fn (.«∀» argTy resTy))
      (HArg : CoCJ lctx arg argTy) :
    CoCJ lctx (.a argTy fn arg) (CoCTerm.instantiate1 arg resTy)

end Auto.Embedding.CoC
