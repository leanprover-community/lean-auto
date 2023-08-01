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
  -- Corresponds to fields of `LamValuation`
  lamVarTy    : Array (FVarId × LamSort) := #[]
  eqLamTy     : Array (FVarId × LamSort) := #[]
  forallLamTy : Array (FVarId × LamSort) := #[]
  existLamTy  : Array (FVarId × LamSort) := #[]
  tyVal       : Array FVarId             := #[]
  eqVal       : Array Expr               := #[]
  forallVal   : Array Expr               := #[]
  existVal    : Array Expr               := #[]
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
        | throwError "processTermFVar :: Cannot find let declaration of interpreted logical constant"
      let u ← getU
      -- `α` is the original (un-lifted) type
      let (fvTy, uOrig, α) ← (do
        match val with
        | .app (.const ``Eq [uOrig]) α =>
          return (FVarType.eqVar, uOrig, α)
        | .app (.const ``Embedding.forallF [uOrig, _]) α =>
          return (FVarType.forallVar, uOrig, α)
        | .app (.const ``Exists [uOrig]) α =>
          return (FVarType.existVar, uOrig, α)
        | _ => throwError "processTermFVar :: Unexpected logical construct {val}")
      -- Make `IsomType`. We choose not to call `termULift` and `typeULift` at this stage
      let (upFunc, upTy) ← Meta.withLocalDeclD `_ α fun down => do
        let (up, upTy) ← cstULiftPos u down (← instantiateMVars α)
        let upFunc ← Meta.mkLambdaFVars #[down] up
        return (upFunc, upTy)
      let downFunc ← Meta.withLocalDeclD `_ upTy fun up => do
        let (down, _) ← cstULiftNeg u up (← instantiateMVars α)
        Meta.mkLambdaFVars #[up] down
      let eq₁ : Expr := mkLambda `_ .default α (mkAppN (.const ``Eq.refl [uOrig]) #[α, .bvar 0])
      let eq₂ : Expr := mkLambda `_ .default upTy (mkAppN (.const ``Eq.refl [u]) #[upTy, .bvar 0])
      let isomTy : Expr := mkAppN (.const ``Embedding.IsomType.mk [uOrig, u]) #[α, upTy, upFunc, downFunc, eq₁, eq₂]
      let fidTy ← fid.getType
      match fvTy with
      | .var => throwError "processTermFVar :: Unexpected error"
      | .eqVar =>
        let .forallE _ upTy' _ _ := fidTy
          | throwError "processTermFVar :: Unexpected `=` type {fidTy}"
        let s ← reifType upTy'
        let eqLift := mkAppN (.const ``Embedding.EqLift.ofEqLift [uOrig, u])
          #[α, upTy, isomTy]
        setEqVal ((← getEqVal).push eqLift)
        newTermFVar .eqVar fid s
      | .forallVar =>
        let .forallE _ (.forallE _ upTy' _ _) _ _ := fidTy
          | throwError "processTermFVar :: Unexpected `∀` type {fidTy}"
        let s ← reifType upTy'
        let forallLift := mkAppN (.const ``Embedding.ForallLift.ofForallLift [uOrig, u, .zero])
          #[α, upTy, isomTy]
        setForallVal ((← getForallVal).push forallLift)
        newTermFVar .forallVar fid s
      | .existVar =>
        let .forallE _ (.forallE _ upTy' _ _) _ _ := fidTy
          | throwError "processTermFVar :: Unexpected `∃` type {fidTy}"
        let s ← reifType upTy'
        let existLift := mkAppN (.const ``Embedding.ExistLift.ofExistLift [uOrig, u])
          #[α, upTy, isomTy]
        setExistVal ((← getExistVal).push existLift)
        newTermFVar .existVar fid s
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