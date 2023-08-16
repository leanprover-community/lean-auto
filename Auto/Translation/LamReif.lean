import Lean
import Auto.Util.MonadUtils
import Auto.Util.ExprExtra
import Auto.Translation.LamPULift
import Auto.Embedding.LamBase
open Lean

initialize
  registerTraceClass `auto.lamReif

namespace Auto.LamReif
open LamPULift Embedding.Lam

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
  -- For `eqLamTy`, `forallLamTy` and `existLamTy`,
  --   the `LamSort` is the corresponding sort where
  --   we'll use in `<eq/forall/exist>LamVal`, and
  --   the `FVarId` is the expression we'll use in
  --   `<eq/forall/exist>Val`
  eqLamTy     : Array (FVarId × LamSort)        := #[]
  forallLamTy : Array (FVarId × LamSort)        := #[]
  existLamTy  : Array (FVarId × LamSort)        := #[]
  -- `tyVal` is the inverse of `tyVarMap`
  -- The first `FVarId` is the interpretation of the sort atom
  -- The second `level` is the level of the un-lifted counterpart of `FVarId`
  tyVal       : Array (FVarId × Level)          := #[]
  eqVal       : Array Expr                      := #[]
  forallVal   : Array Expr                      := #[]
  existVal    : Array Expr                      := #[]
  -- This array contains assertions that have external (lean) proof
  --   The first `Expr` is the proof of the assertion
  assertions  : Array (Expr × LamTerm)          := #[]
deriving Inhabited

abbrev ReifM := StateRefT State ULiftM

@[inline] def ReifM.run' (x : ReifM α) (s : State) := Prod.fst <$> x.run s

#genMonadState ReifM

-- Takes a `s : LamSort` and produces the
--   `un-lifted` version of `s.interp` (note that `s.interp`
--   is lifted)
def interpLamSortAsUnlifted (s : LamSort) : ReifM Expr :=
  match s with
  | .atom n => do
    let .some (id, _) := (← getTyVal).get? n
      | throwError "interpLamSortAsUnlifted :: Unexpected sort atom {n}"
    let .some orig := (← getUnliftMap).find? id
      | throwError "interpLamSortAsUnlifted :: Unable to find un-lifted counterpart of {Expr.fvar id}"
    return orig
  | .base b =>
    match b with
    | .prop => return .sort .zero
    | .int  => return .const ``Int []
    | .real => return .const ``Real []
    | .bv n => return .app (.const ``Bitvec []) (.lit (.natVal n))
  | .func s₁ s₂ => do
    return .forallE `_ (← interpLamSortAsUnlifted s₁) (← interpLamSortAsUnlifted s₂) .default

-- Takes a `s : LamSort` and produces the expression definitionally
--   equal to `s.interp`
open Embedding in
def interpLamSortAsLifted (s : LamSort) : ReifM Expr :=
  match s with
  | .atom n => do
    let .some (id, lvl) := (← getTyVal).get? n
      | throwError "interpLamSortAsLifted :: Unexpected sort atom {n}"
    let .some orig := (← getUnliftMap).find? id
      | throwError "interpLamSortAslifted :: Unable to find un-lifted counterpart of {Expr.fvar id}"
    return Expr.app (.const ``GLift [lvl, ← getU]) orig
  | .base b => do
    let u ← getU
    let lvl₁ := Level.succ .zero
    let lift₁ := Expr.app (.const ``GLift [lvl₁, u])
    match b with
    | .prop => return lift₁ (.sort .zero)
    | .int => return lift₁ (.const ``Int [])
    | .real => return lift₁ (.const ``Real [])
    | .bv n => return lift₁ (.app (.const ``Bitvec []) (.lit (.natVal n)))
  | .func s₁ s₂ => do
    return .forallE `_ (← interpLamSortAsLifted s₁) (← interpLamSortAsLifted s₂) .default

-- Computes `upFunc` and `downFunc` between `s.interpAsUnlifted` and `s.interpAsLifted`
--   The first `Expr` is `upFunc`
--   The second `Expr` is `downFunc`
--   The third `Expr` is `s.interpAsUnlifted`
--   The fourth `Expr` is `s.interpAsLifted`
open Embedding in
partial def updownFunc (s : LamSort) : ReifM (Expr × Expr × Expr × Expr) :=
  match s with
  | .atom n => do
    let .some (id, lvl) := (← getTyVal).get? n
      | throwError "upFunc :: Unexpected sort atom {n}"
    let .some orig := (← getUnliftMap).find? id
      | throwError "upFunc :: Unable to find un-lifted counterpart of {Expr.fvar id}"
    let up := Expr.app (.const ``GLift.up [lvl, (← getU)]) orig
    let down := Expr.app (.const ``GLift.down [lvl, (← getU)]) orig
    return (up, down, orig, Expr.app (.const ``GLift [lvl, ← getU]) orig)
  | .base b => do
    let u ← getU
    let lvl₁ := Level.succ .zero
    let lift₁ := Expr.app (.const ``GLift [lvl₁, u])
    let liftup₁ := Expr.app (.const ``GLift.up [lvl₁, u])
    let liftdown₁ := Expr.app (.const ``GLift.down [lvl₁, u])
    match b with
    | .prop =>
      let ty := Expr.sort .zero
      return (liftup₁ ty, liftdown₁ ty, ty, lift₁ ty)
    | .int =>
      let ty := Expr.const ``Int []
      return (liftup₁ ty, liftdown₁ ty, ty, lift₁ ty)
    | .real =>
      let ty := Expr.const ``Real []
      return (liftup₁ ty, liftdown₁ ty, ty, lift₁ ty)
    | .bv n =>
      let ty := Expr.app (.const ``Bitvec []) (.lit (.natVal n))
      return (liftup₁ ty, liftdown₁ ty, ty, lift₁ ty)
  | .func s₁ s₂ => do
    let (uf₁, df₁, ty₁, tyUp₁) ← updownFunc s₁
    let (uf₂, df₂, ty₂, tyUp₂) ← updownFunc s₂
    let fty := Expr.forallE `_ ty₁ ty₂ .default
    let ftyUp := Expr.forallE `_ tyUp₁ tyUp₂ .default
    let up := Expr.lam `_ fty (Expr.lam `_ tyUp₁ (.app uf₂ (.app (.bvar 1) (.app df₁ (.bvar 0)))) .default) .default
    let down := Expr.lam `_ ftyUp (Expr.lam `_ ty₁ (.app df₂ (.app (.bvar 1) (.app uf₁ (.bvar 0)))) .default) .default
    return (up, down, fty, ftyUp)

section

  open Embedding

  private def mkImportAux (s : LamSort) : ReifM (Expr × Expr × Expr × Expr × Level) := do
    let (upFunc, downFunc, ty, upTy) ← updownFunc s
    let sortOrig ← instantiateMVars (← Meta.inferType ty)
    let sortOrig ← Meta.withTransparency .all <| Meta.whnf sortOrig
    let .sort uOrig := sortOrig
      | throwError "mkIsomType :: Unexpected sort {sortOrig} when processing sort {repr s}"
    return (upFunc, downFunc, ty, upTy, uOrig)

  def mkIsomType (upFunc downFunc ty upTy : Expr) (uOrig : Level) : ReifM Expr := do
    let u ← getU
    let eq₁ : Expr := mkLambda `_ .default ty (mkAppN (.const ``Eq.refl [uOrig]) #[ty, .bvar 0])
    let eq₂ : Expr := mkLambda `_ .default upTy (mkAppN (.const ``Eq.refl [.succ u]) #[upTy, .bvar 0])
    let isomTy : Expr := mkAppN (.const ``Embedding.IsomType.mk [uOrig, .succ u]) #[ty, upTy, upFunc, downFunc, eq₁, eq₂]
    return isomTy
  
  def mkImportingEqLift (s : LamSort) := do
    let (upFunc, downFunc, ty, upTy, uOrig) ← mkImportAux s
    let isomTy ← mkIsomType upFunc downFunc ty upTy uOrig
    return mkAppN (.const ``EqLift.ofEqLift [uOrig, .succ (← getU)]) #[ty, upTy, isomTy]

  def mkImportingForallLift (s : LamSort) := do
    let (upFunc, downFunc, ty, upTy, uOrig) ← mkImportAux s
    let isomTy ← mkIsomType upFunc downFunc ty upTy uOrig
    return mkAppN (.const ``Embedding.ForallLift.ofForallLift [uOrig, .succ (← getU), .zero]) #[ty, upTy, isomTy]

  def mkImportingExistLift (s : LamSort) := do
    let (upFunc, downFunc, ty, upTy, uOrig) ← mkImportAux s
    let isomTy ← mkIsomType upFunc downFunc ty upTy uOrig
    return  mkAppN (.const ``Embedding.ExistLift.ofExistLift [uOrig, .succ (← getU)]) #[ty, upTy, isomTy]

end

-- Accept a new free variable representing term atom or lifted logical constant
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
  -- The universe level of the un-lifted counterpart of `id`
  let origSort ← Meta.inferType ((← getUnliftMap).find! id)
  let origSort := (← instantiateMVars origSort).headBeta
  let .sort lvl := origSort
    | throwError "newTypeFVar :: Unexpected sort {origSort}"
  setTyVal (tyVal.push (id, lvl))
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
    | .const ``Int [] => return .base .int
    | .const ``Real [] => return .base .real
    | .app (.const ``Bitvec []) (.lit (.natVal n)) => return .base (.bv n)
    | _ => throwError "processTypeFVar :: Unexpected interpreted constant {val}"
  | .none     => newTypeFVar fid

-- This is an auxiliary function for `reifTerm`. Please refer to `reifTerm`
--   `fid` is an interpreted constant, lifted from `val`.
def processLiftedInterped (val : Expr) (fid : FVarId) (reifType : Expr → ReifM LamSort) : ReifM LamTerm := do
  let fidTy ← fid.getType
  let mut fvTy : FVarType := Inhabited.default
  match val with
  | .const ``True [] => return .base .trueE
  | .const ``False [] => return .base .falseE
  | .const ``Not [] => return .base .not
  | .const ``And [] => return .base .and
  | .const ``Or []  => return .base .or
  | .const ``Embedding.ImpF [u, v] =>
    if (← Meta.isLevelDefEq u .zero) ∧ (← Meta.isLevelDefEq v .zero) then
      return .base .imp
    else
      throwError "processTermFVar :: Unexpected ImpF levels"
  | .const ``Iff [] => return .base .iff
  -- **TODO: Integer, Real number, Bit vector**
  -- `α` is the original (un-lifted) type
  | .app (.const ``Eq _) _ =>
    fvTy := FVarType.eqVar
  | .app (.const ``Embedding.forallF _) _ =>
    fvTy := FVarType.forallVar
  | .app (.const ``Exists _) _ =>
    fvTy := FVarType.existVar
  | _ => throwError "processTermFVar :: Unexpected interpreted constant {val}"
  match fvTy with
  | .var => throwError "processTermFVar :: Unexpected error"
  | .eqVar =>
    let .forallE _ upTy' _ _ := fidTy
      | throwError "processTermFVar :: Unexpected `=` type {fidTy}"
    let s ← reifType upTy'
    let eqLift := ← mkImportingEqLift s
    if !(← Meta.isTypeCorrect eqLift) then
      throwError "processTermFVar :: Malformed eqLift {eqLift}"
    setEqVal ((← getEqVal).push eqLift)
    newTermFVar .eqVar fid s
  | .forallVar =>
    let .forallE _ (.forallE _ upTy' _ _) _ _ := fidTy
      | throwError "processTermFVar :: Unexpected `∀` type {fidTy}"
    let s ← reifType upTy'
    let forallLift ← mkImportingForallLift s
    if !(← Meta.isTypeCorrect forallLift) then
      throwError "processTermFVar :: Malformed forallLift {forallLift}"
    setForallVal ((← getForallVal).push forallLift)
    newTermFVar .forallVar fid s
  | .existVar =>
    let .forallE _ (.forallE _ upTy' _ _) _ _ := fidTy
      | throwError "processTermFVar :: Unexpected `∃` type {fidTy}"
    let s ← reifType upTy'
    let existLift ← mkImportingExistLift s
    if !(← Meta.isTypeCorrect existLift) then
      throwError "processTermFVar :: Malformed existLift {existLift}"
    setExistVal ((← getExistVal).push existLift)
    newTermFVar .existVar fid s

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
    | .some val => processLiftedInterped val fid reifType      
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
    let argTy ← Meta.inferType arg
    let lamTy ← reifType argTy
    return .app lamTy lamFn lamArg
  | .lam name ty body binfo => do
    let lamTy ← reifType ty
    let body ← withLocalDeclAsBoundFVar name binfo ty fun fvar => do
      let body' := body.instantiate1 fvar
      reifTerm body'
    return .lam lamTy body
  | e => throwError "reifTerm :: {e} should have been lifted into fvar"

  -- At this point, there should only be non-dependent `∀`s in the type.
  partial def reifType : Expr → ReifM LamSort
  | .app (.const ``Embedding.LiftTyConv _) (.fvar fid) =>
    processTypeFVar fid
  | .mdata _ e => reifType e
  | .forallE _ ty body _ => do
    if body.hasLooseBVar 0 then
      throwError "reifType :: Dependently typed functions are not supported"
    else
      return .func (← reifType ty) (← reifType body)
  | e => throwError "reifType :: {e} should have been lifted into fvar"

end

def reifFacts (facts : Array ULiftedFact) : ReifM Unit := do
  let _ ← facts.mapM (fun (proof, tyLift) => do
    trace[auto.lamReif] m!"Reifying {proof} : {tyLift}"
    let lamty ← reifTerm tyLift
    setAssertions ((← getAssertions).push (proof, lamty)))

-- **TODO:** Real and bitvec
open Embedding in
def checkInterpretedConst : Expr → MetaM Bool
| .const ``Int []      => return true
| .const ``Real []     => return true
| .const ``True []     => return true
| .const ``False []    => return true
| .const ``Not []      => return true
| .const ``And []      => return true
| .const ``Or []       => return true
-- Although `ImpF` should have been turned into free
--   variable, we write code for it here anyway because
--   this does not hurt.
| .const ``ImpF [u, v] =>
  return (← Meta.isLevelDefEq u .zero) ∧ (← Meta.isLevelDefEq v .zero)
| .const ``Iff []      => return true
| _                    => return false

-- `cont` is what we need to do after we ulift and reify the facts
def uLiftAndReify (facts : Array Reif.UMonoFact) (cont : ReifM α) : ReifM α :=
  withULiftedFacts checkInterpretedConst facts (fun pfacts => do reifFacts pfacts; cont)

end Auto.LamReif