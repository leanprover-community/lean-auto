import Lean
import Auto.Util.MonadUtils
import Auto.Util.ExprExtra
import Auto.Translation.LamULift
import Auto.Embedding.LamBase
open Lean

initialize
  registerTraceClass `auto.reifLam

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
  tyVarMap    : HashMap FVarId Nat              := HashMap.empty
  -- Maps fvars representing free variables to their index
  varMap      : HashMap FVarId (FVarType × Nat) := HashMap.empty
  -- Corresponds to fields of `LamValuation`
  lamVarTy    : Array (FVarId × LamSort)        := #[]
  eqLamTy     : Array (FVarId × LamSort)        := #[]
  forallLamTy : Array (FVarId × LamSort)        := #[]
  existLamTy  : Array (FVarId × LamSort)        := #[]
  tyVal       : Array FVarId                    := #[]
  eqVal       : Array Expr                      := #[]
  forallVal   : Array Expr                      := #[]
  existVal    : Array Expr                      := #[]
  assertions  : Array (Expr × LamTerm)          := #[]
deriving Inhabited

abbrev ReifM := StateRefT State ULiftM

@[inline] def ReifM.run' (x : ReifM α) (s : State) := Prod.fst <$> x.run s

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
  if let .some idx := tyVarMap.find? fid then
    return .atom idx
  match (← getLiftedInterped).find? fid with
  | .some val =>
    match val with
    | .sort lvl => do
      if !(← Meta.isLevelDefEq lvl .zero) then
        throwError "processTypeFVar :: Unexpected sort {val}"
      else
        return .base .prop
    | .const ``Nat [] => return .base .nat
    | .const ``Real [] => return .base .real
    | .app (.const ``Bitvec []) (.lit (.natVal n)) => return .base (.bv n)
    | _ => throwError "processTypeFVar :: Unexpected interpreted constant {val}"
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
    match (← getLiftedInterped).find? fid with
    | .some val => do
      -- An interpreted constant, lifted from `val`
      let mut info : FVarType × Level × Expr := Inhabited.default
      match val with
      | .const ``True [] => return .base .trueE
      | .const ``False [] => return .base .falseE
      | .const ``Not [] => return .base .not
      | .const ``And [] => return .base .and
      | .const ``Or []  => return .base .or
      | .const ``Embedding.impF [] => return .base .imp
      | .const ``Iff [] => return .base .iff
      | .lit (.natVal n) => return .base (.natVal n)
      -- **TODO: Real number, Bit vector**
      -- `α` is the original (un-lifted) type
      | .app (.const ``Eq [uOrig]) α =>
        info := (FVarType.eqVar, uOrig, α)
      | .app (.const ``Embedding.forallF [uOrig, _]) α =>
        info := (FVarType.forallVar, uOrig, α)
      | .app (.const ``Exists [uOrig]) α =>
        info := (FVarType.existVar, uOrig, α)
      | _ => throwError "processTermFVar :: Unexpected interpreted constant {val}"
      let (fvTy, uOrig, α) := info
      -- Process `=, ∀, ∃`
      -- Make `IsomType`. We choose not to call `termULift` and `typeULift` at this stage
      let u ← getU
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
    -- A normal free variable, treated as an atom
    | .none =>
      let tyLift ← fid.getType
      let lamTy ← reifType tyLift
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
  partial def reifType : Expr → ReifM LamSort
  | .app (.const ``Embedding.liftTyConv _) (.fvar fid) =>
    processTypeFVar fid
  | .forallE _ ty body _ => do
    if body.hasLooseBVar 0 then
      throwError "reifType :: Dependently typed functions are not supported"
    else
      return .func (← reifType ty) (← reifType body)
  | e => throwError "reifType :: {e} should have been lifted into fvar"

end

def reifFacts (facts : Array ULiftedFact) : ReifM Unit := do
  let _ ← facts.mapM (fun (proof, tyLift) => do
    trace[auto.reifLam] s!"Reifying {proof} : {tyLift}"
    let lamty ← reifTerm tyLift
    setAssertions ((← getAssertions).push (proof, lamty)))

-- `cont` is what we need to do after we ulift and reify the facts
def uLiftAndReify (cont : State → MetaM α) : ReifM α :=
  withULiftedFacts (fun pfacts => do
    reifFacts pfacts
    cont (← get))

end Auto.LamReif