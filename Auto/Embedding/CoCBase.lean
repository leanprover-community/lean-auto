import Lean
import Auto.Lib.TreeList

namespace Auto.Embedding.CoC

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
  | prop
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
inductive CoCJ : TreeList CoCTerm → CoCTerm → CoCTerm → Type
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
