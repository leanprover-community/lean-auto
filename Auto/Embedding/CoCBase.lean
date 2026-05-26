import Lean
import Auto.Lib.TreeList

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

-- CoC Judgements, `Γ ⊢ term : type`
-- **TODO**
inductive CoCJ : TreeList CoCTerm → CoCTerm → CoCTerm → Type
  -- **TODO**
  -- | ofWeak
  --     {Γ : TreeList CoCTerm} {Δ : TreeList CoCTerm} {t : CoCTerm} {s : CoCTerm}
  --     (hΓΔ : Γ ≼ Δ) (hΓ : CoCJ Γ t s) : CoCJ Δ t x
  /--
          Γ ⊢ A : K
    --------------------
    Γ, x : A, Γ' ⊢ x : A
  -/
  -- **TODO**
  | ofBVar
      {lctx : TreeList CoCTerm} (n : Nat) (h : n < lctx.length) :
    CoCJ lctx (.b n) lctx[n]
  | ofLam
      {lctx : TreeList CoCTerm} {argTy : CoCTerm} (bodyTy : CoCTerm) (body : CoCTerm)
      (H : CoCJ (lctx.push argTy) (.«λ» argTy body) bodyTy) :
    CoCJ lctx (.«λ» argTy body) (.«∀» argTy bodyTy)
  | ofApp
      {lctx : TreeList CoCTerm}
      (argTy : CoCTerm) {resTy : CoCTerm} {fn : CoCTerm} {arg : CoCTerm}
      (HFn : CoCJ lctx fn (.«∀» argTy resTy))
      (HArg : CoCJ lctx arg argTy) :
    CoCJ lctx (.a argTy fn arg) resTy
  -- TODO

end Auto.Embedding.CoC
