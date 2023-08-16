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