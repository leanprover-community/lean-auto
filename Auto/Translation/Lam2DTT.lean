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

-- All the type atoms and term atoms are interpreted as fvars, which
--   are let-declarations in the local context. We don't want the external
--   prover to unfold these let-declarations, so we add these atoms as
--   non-let free variables into the local context, run the external prover,
--   abstract these free variables after the external prover has
--   finished, and apply the abstracted expression to the value of
--   these atoms to restore the requires expression.
structure Context where
  -- Type atoms that are used in the expressions sent to external prover
  typeAtomFVars   : HashMap Nat FVarId := HashMap.empty
  -- Term atoms that are used in the expressions sent to external prover
  termAtomFVars   : HashMap Nat FVarId := HashMap.empty

abbrev ExternM := ReaderT Context ReifM

#genMonadContext ExternM

def withTypeAtomAsFVar (atom : Nat) (cont : ExternM Expr) : ExternM Expr := do
  if (← getTypeAtomFVars).contains atom then
    return ← cont
  let freshId := (← mkFreshId).toString
  let (_, orig, lvl) ← lookupTyVal! atom
  Meta.withLocalDeclD ("_exTypeAtom_" ++ freshId) (.sort lvl) (fun newFVar =>
    withReader (fun s => {s with typeAtomFVars := s.typeAtomFVars.insert atom newFVar.fvarId!}) (do
      let abst ← Meta.mkLambdaFVars #[newFVar] (← cont)
      return mkApp abst orig)
    )

def withTypeAtomsAsFVar (atoms : Array Nat) (cont : ExternM Expr) : ExternM Expr :=
  atoms.foldl (fun cont atom => withTypeAtomAsFVar atom cont) cont

-- Takes a `s : LamSort` and produces the `un-lifted` version of `s.interp`
--   (note that `s.interp` is lifted)
-- This function should be called after we've called
--   `withTypeAtomAsFVar` on all the type atoms occurring in `s`
def interpLamSortAsUnlifted : LamSort → ExternM Expr
| .atom n => do
  let .some fid := (← getTypeAtomFVars).find? n
    | throwError "interpLamSortAsUnlifted :: Cannot find fvarId assigned to type atom {n}"
  return .fvar fid
| .base b =>
  match b with
  | .prop => return .sort .zero
  | .int  => return .const ``Int []
  | .real => return .const ``Real []
  | .bv n => return .app (.const ``Bitvec []) (.lit (.natVal n))
| .func s₁ s₂ => do
  return .forallE `_ (← interpLamSortAsUnlifted s₁) (← interpLamSortAsUnlifted s₂) .default

def withTermAtomAsFVar (atom : Nat) (cont : ExternM Expr) : ExternM Expr := do
  if (← getTermAtomFVars).contains atom then
    return ← cont
  let freshId := (← mkFreshId).toString
  let (_, e, s) ← lookupVarVal! atom
  let sinterp ← interpLamSortAsUnlifted s
  Meta.withLocalDeclD ("_exTermAtom_" ++ freshId) sinterp (fun newFVar =>
    withReader (fun s => {s with termAtomFVars := s.termAtomFVars.insert atom newFVar.fvarId!}) (do
      let abst ← Meta.mkLambdaFVars #[newFVar] (← cont)
      return mkApp abst e)
    )

def withTermAtomsAsFVar (atoms : Array Nat) (cont : ExternM Expr) : ExternM Expr :=
  atoms.foldl (fun cont atom => withTermAtomAsFVar atom cont) cont

def interpCstrRealAsUnlifted (c : CstrReal) : Expr :=
  let lvl₁ := Level.succ .zero
  let real := Expr.const ``Real []
  match c with
  | .zero => .app (.app (.const ``Zero.zero [lvl₁]) real) real
  | .one => .app (.app (.const ``One.one [lvl₁]) real) real

open Embedding in
def interpLamBaseTermAsUnlifted : LamBaseTerm → ExternM Expr
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

-- Takes a `t : LamTerm` and produces the `un-lifted` version of `t.interp`.
-- This function should be called after we've called
--   `withTermAtomAsFVar` on all the term atoms occurring in `t`
def interpLamTermAsUnlifted : LamTerm → ExternM Expr
| .atom n => do
  let .some fid := (← getTermAtomFVars).find? n
    | throwError "interpLamTermAsUnlifted :: Cannot find fvarId assigned to term atom {n}"
  return .fvar fid
| .base b => interpLamBaseTermAsUnlifted b
| .bvar n => return .bvar n
| .lam s t => do
  let sinterp ← interpLamSortAsUnlifted s
  let tinterp ← interpLamTermAsUnlifted t
  return .lam `_ sinterp tinterp .default
| .app _ fn arg => do
  return .app (← interpLamTermAsUnlifted fn) (← interpLamTermAsUnlifted arg)

-- The external prover should only see the local context
--   and an array of Lean expressions, and should not see
--   anything within `ExternM, LamReif.ReifM, ULiftM` or `Reif.ReifM`
def withTranslatedLamTerms (ts : Array LamTerm) (externCont : Array Expr → MetaM Expr) : ReifM Expr :=
  let extern : ExternM Expr := do
    let hss ← ts.mapM (fun t => liftM (collectAtoms t))
    let (typeHs, termHs) := hss.foldl
      (fun (typeHs, termHs) (typeHs', termHs') =>
        (mergeHashSet typeHs typeHs', mergeHashSet termHs termHs')) (HashSet.empty, HashSet.empty)
    withTypeAtomsAsFVar typeHs.toArray (
      withTermAtomsAsFVar termHs.toArray (do
        externCont (← ts.mapM interpLamTermAsUnlifted)
      )
    )
  extern.run {}

end Auto