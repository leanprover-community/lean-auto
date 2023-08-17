import Lean
import Auto.Util.ExprExtra
import Auto.Embedding.LamBase
import Auto.Translation.LamReif
open Lean

-- Lam2DTT : Simply-typed lambda calculus to Lean
-- The reason we need this file is that, sometimes we want external
--   provers (e.g. duper) to help us complete proofs. Note that
--   external provers does not work with things like `GLift.up Prop`.
--   Therefore, we must have a function to translate expressions
--   into `un-lifted` (original) `Lean expressions`.
-- Also, an important part of translating to un-lifted Lean
--   expressions is to deal with `=, ∀` and `∃`, namely assigning
--   the appropriate valuation so that the type matches.

namespace Auto

open LamReif
open Embedding.Lam

-- All the type atoms and term atoms are actually let-declarations
--   in the local context. We don't want the external prover to
--   unfold these let-declarations, so we add these atoms as non-let
--   free variables into the local context, run the external prover,
--   abstract these free variables after the external prover has
--   finished, and apply the abstracted expression to the value of
--   these atoms to restore the requires expression.
structure State where
  -- Type atoms that are used in the expressions sent to external prover
  typeAtoms       : Array Nat
  typeAtomFVars   : HashMap Nat FVarId
  -- Term atoms that are used in the expressions sent to external prover
  termAtoms       : Array Nat
  termAtomFVars   : HashMap Nat FVarId

-- Takes a `s : LamSort` and produces the
--   `un-lifted` version of `s.interp` (note that `s.interp`
--   is lifted)
def interpLamSortAsUnlifted (s : LamSort) : ReifM Expr :=
  match s with
  | .atom n => do
    let .some (_, orig, _) := (← getTyVal).get? n
      | throwError "interpLamSortAsUnlifted :: Unexpected sort atom {n}"
    return orig
  | .base b =>
    match b with
    | .prop => return .sort .zero
    | .int  => return .const ``Int []
    | .real => return .const ``Real []
    | .bv n => return .app (.const ``Bitvec []) (.lit (.natVal n))
  | .func s₁ s₂ => do
    return .forallE `_ (← interpLamSortAsUnlifted s₁) (← interpLamSortAsUnlifted s₂) .default

def interpCstrRealAsUnlifted (c : CstrReal) : Expr :=
  let lvl₁ := Level.succ .zero
  let real := Expr.const ``Real []
  match c with
  | .zero => .app (.app (.const ``Zero.zero [lvl₁]) real) real
  | .one => .app (.app (.const ``One.one [lvl₁]) real) real

open Embedding in
def interpLamBaseTermAsUnlifted : LamBaseTerm → ReifM Expr
| .trueE     => return .const ``True []
| .falseE    => return .const ``False []
| .not       => return .const ``Not []
| .and       => return .const ``And []
| .or        => return .const ``Or []
| .imp       => return .const ``ImpF [.zero, .zero]
| .iff       => return .const ``Iff []
| .intVal _  => throwError "Not implemented"
| .realVal c => return interpCstrRealAsUnlifted c
| .bvVal _   => throwError "Not implemented"
| .eq n      => do
  let eqLamTy ← getEqLamTy
  let .some s := eqLamTy[n]?
    | throwError "interpLamBaseTermAsUnlifted :: Unknown eq {n}"
  return ← Meta.mkAppOptM ``Eq #[← interpLamSortAsUnlifted s]
| .forallE n => do
  let forallLamTy ← getForallLamTy
  let .some s := forallLamTy[n]?
    | throwError "interpLamBaseTermAsUnlifted :: Unknown forall {n}"
  let ty ← interpLamSortAsUnlifted s
  let sort ← Util.normalizeType (← Meta.inferType ty)
  let Expr.sort lvl := sort
    | throwError "interpLamBaseTermAsUnlifted :: Unexpected sort {sort}"
  return mkAppN (.const ``forallF [lvl, .zero]) #[← interpLamSortAsUnlifted s]
| .existE n => do
  let existLamTy ← getExistLamTy
  let .some s := existLamTy[n]?
    | throwError "interpLamBaseTermAsUnlifted :: Unknown exist {n}"
  return ← Meta.mkAppOptM ``Exists #[← interpLamSortAsUnlifted s]

def interpLamTermAsUnlifted : LamTerm → ReifM Expr := sorry  

end Auto