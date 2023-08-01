import Lean
import Auto.Util.MonadUtils
import Auto.Util.ExprExtra
import Auto.Translation.LamULift
import Auto.Embedding.LamBase
open Lean

namespace Auto.LamReif
open LamULift Embedding.Lam

inductive FVarType where
  | var       -- Ordinary variable
  | eqVar     -- Lifted `=`
  | forallVar -- Lifted `∀`
  | existVar  -- Lifted `∃`
deriving Inhabited, Hashable, BEq

structure State where
  -- Maps fvars representing (lifted) type to their index
  tyVarMap    : HashMap FVarId Nat := HashMap.empty
  -- Maps fvars representing free variables to their index
  varMap      : HashMap FVarId (FVarType × Nat) := HashMap.empty
  -- Corresponding fields of `LamValuation`
  lamVarTy    : Array (FVarId × LamSort) := #[]
  eqLamTy     : Array (FVarId × LamSort) := #[]
  forallLamTy : Array (FVarId × LamSort) := #[]
  existLamTy  : Array (FVarId × LamSort) := #[]
  tyVal       : Array FVarId             := #[]
deriving Inhabited

abbrev ReifM := StateRefT State ULiftM
#genMonadState ReifM

-- Accept a new free variable representing atom or lifted logical constant
-- Returns the index of it in the corresponding Array after we've inserted it into
--   its Array and HashMap
def newTermFVar (fvty : FVarType) (id : FVarId) (sort : LamSort) : ReifM LamTerm := do
  let varMap ← getVarMap
  match fvty with
  | .var   =>
    let lamVarTy ← getLamVarTy
    let idx := lamVarTy.size
    setLamVarTy (lamVarTy.push (id, sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .atom idx
  | .eqVar =>
    let eqLamTy ← getEqLamTy
    let idx := eqLamTy.size
    setEqLamTy (eqLamTy.push (id, sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.eq idx)
  | .forallVar =>
    let forallLamTy ← getForallLamTy
    let idx := forallLamTy.size
    setForallLamTy (forallLamTy.push (id, sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.forallE idx)
  | .existVar =>
    let existLamTy ← getExistLamTy
    let idx := existLamTy.size
    setExistLamTy (existLamTy.push (id, sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.existE idx)

def newTypeFVar (id : FVarId) : ReifM LamSort := do
  let tyVarMap ← getTyVarMap
  let tyVal ← getTyVal
  let idx := tyVal.size
  setTyVal (tyVal.push id)
  setTyVarMap (tyVarMap.insert id idx)
  return .atom idx

def processTypeFVar (fid : FVarId) : ReifM LamSort := do
  let tyVarMap ← getTyVarMap
  match tyVarMap.find? fid with
  | .some idx => return .atom idx
  | .none     => newTypeFVar fid

mutual

  partial def processTermFVar (fid : FVarId) : ReifM LamTerm := do
    let boundFVars ← getBoundFVars
    if let .some idx := boundFVars.find? fid then
      return .bvar (boundFVars.size - 1 - idx)
    let varMap ← getVarMap
    -- If the free variable has already been processed
    if let .some (fvarType, id) := varMap.find? fid then
      match fvarType with
      | .var => return .atom id
      | .eqVar => return .base (.eq id)
      | .forallVar => return .base (.forallE id)
      | .existVar => return .base (.existE id)
    -- If the free variable has not been processed
    let liftedILogical ← getLiftedILogical
    match liftedILogical.find? fid with
    -- A lifted logical constant, lifted from `origFid`
    | .some origFid => do
      let .some val := (← Reif.getILogical).find? origFid
        | throwError "reifTerm :: Cannot find let declaration of interpreted logical constant"
      match val with
      | .app (.const ``Eq [u]) α => sorry
      | _ => sorry
    -- A normal free variable, treated as atom
    | .none =>
      let ty ← fid.getType
      let lamTy ← reifType ty
      newTermFVar .var fid lamTy

  partial def reifTerm : Expr → ReifM LamTerm
  | .bvar _ => throwError "reifTerm :: Loose bound variable"
  | .fvar fid => processTermFVar fid
  | .app fn arg => do
    let lamFn ← reifTerm fn
    let lamArg ← reifTerm arg
    return .app lamFn lamArg
  | .lam name ty body binfo => do
    let lamTy ← reifType ty
    let body ← withLocalDeclAsBoundFVar name binfo ty fun fvar => do
      let body' := body.instantiate1 fvar
      reifTerm body'
    return .lam lamTy body
  | e => throwError "reifTerm :: {e} should have been lifted into fvar"

  -- At this point, there should only be non-dependent `∀`s in the type.
  --   Nothing else!
  partial def reifType : Expr → ReifM LamSort
  | .fvar fid => processTypeFVar fid
  | .forallE _ ty body _ => do
    if body.hasLooseBVar 0 then
      throwError "reifType :: Dependently typed functions are not supported"
    else
      return .func (← reifType ty) (← reifType body)
  | e => throwError "reifType :: {e} should have been lifted into fvar"

end

end Auto.LamReif