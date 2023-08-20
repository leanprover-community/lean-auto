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
  -- Maps reified free variables to their index
  -- Whenever we encounter a free variable, we look up
  --   `varMap`. If it's already reified, then `varMap`
  --   tells us about its index. If it's not reified, insert
  --   it to `varMap`.
  varMap      : HashMap FVarId (FVarType × Nat) := HashMap.empty
  -- `tyVal` is the inverse of `tyVarMap`
  -- The first `FVarId` is the interpretation of the type atom
  -- The second `Expr` is the un-lifted counterpart of the first `FVarId`
  -- The `level` is the sort level of the second `Expr`
  tyVal       : Array (FVarId × Expr × Level)   := #[]
  -- The `FVarId` is the valuation of the atom
  -- The `Expr` is the un-lifted counterpart of `FVarId`
  -- The `LamSort` is the λ sort of the atom
  varVal      : Array (FVarId × Expr × LamSort) := #[]
  isomTys   : Array LamSort                   := #[]
  -- Inverse of ``isomTys
  isomTyMap : HashMap LamSort Nat             := HashMap.empty
  -- If `eqLamTy[n] = s`, then `s` is the corresponding
  --   sort where we'll use in `<eq/forall/exist>LamVal n`
  -- The same holds for `forallLamTy` and `existLamTy`
  eqLamTy     : Array Nat                       := #[]
  forallLamTy : Array Nat                       := #[]
  existLamTy  : Array Nat                       := #[]
  -- This array contains assertions that have external (lean) proof
  --   The first `e : Expr` is the proof of the assertion
  --   The second `t : LamTerm` is the corresponding λ term,
  --     where all `eq, ∀, ∃` are import version
  -- To be precise, we require that `e : GLift.down t.interp`
  assertions  : Array (Expr × LamTerm)          := #[]
deriving Inhabited

abbrev ReifM := StateRefT State ULiftM

@[inline] def ReifM.run' (x : ReifM α) (s : State) := Prod.fst <$> x.run s

#genMonadState ReifM

def sort2IsomTysIdx (s : LamSort) : ReifM Nat := do
  let isomTyMap ← getIsomTyMap
  match isomTyMap.find? s with
  | .some n => return n
  | .none =>
    let isomTys ← getIsomTys
    let idx := isomTys.size
    setIsomTys (isomTys.push s)
    setIsomTyMap (isomTyMap.insert s idx)
    return idx

def lookupTyVal! (n : Nat) : ReifM (FVarId × Expr × Level) := do
  if let .some r := (← getTyVal)[n]? then
    return r
  else
    throwError "lookupTyVal! :: Unknown type atom {n}"

-- Lookup valuation of term atom
def lookupVarVal! (n : Nat) : ReifM (FVarId × Expr × LamSort) := do
  if let .some r := (← getVarVal)[n]? then
    return r
  else
    throwError "lookupVarVal! :: Unknown term atom {n}"

def lookupIsomTy! (idx : Nat) : ReifM LamSort := do
  if let .some s := (← getIsomTys)[idx]? then
    return s
  else
    throwError "lookupIsomTy! :: Unknown index {idx}"

def lookupEqLamTy! (n : Nat) : ReifM LamSort := do
  if let .some idx := (← getEqLamTy)[n]? then
    lookupIsomTy! idx
  else
    throwError "lookupEqLamTy! :: Unknown eq {n}"

def lookupForallLamTy! (n : Nat) : ReifM LamSort := do
  if let .some idx := (← getForallLamTy)[n]? then
    lookupIsomTy! idx
  else
    throwError "lookupForallLamTy! :: Unknown forall {n}"

def lookupExistLamTy! (n : Nat) : ReifM LamSort := do
  if let .some idx := (← getExistLamTy)[n]? then
    lookupIsomTy! idx
  else
    throwError "lookupExistLamTy! :: Unknown exist {n}"

-- Computes `upFunc` and `downFunc` between `s.interpAsUnlifted` and `s.interpAsLifted`
--   The first `Expr` is `upFunc`
--   The second `Expr` is `downFunc`
--   The third `Expr` is `s.interpAsUnlifted`
--   The fourth `Expr` is `s.interpAsLifted`
open Embedding in
partial def updownFunc (s : LamSort) : ReifM (Expr × Expr × Expr × Expr) :=
  match s with
  | .atom n => do
    let (_, orig, lvl) ← lookupTyVal! n
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

section ILLifting

  open Embedding

  private def mkImportAux (s : LamSort) : ReifM (Expr × Expr × Expr × Expr × Level) := do
    let (upFunc, downFunc, ty, upTy) ← updownFunc s
    let sortOrig ← Util.normalizeType (← Meta.inferType ty)
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
    let eqLift := mkAppN (.const ``EqLift.ofEqLift [uOrig, .succ (← getU)]) #[ty, upTy, isomTy]
    if !(← Meta.isTypeCorrect eqLift) then
      throwError "mkImportingEqLift :: Malformed eqLift {eqLift}"
    return eqLift

  def mkImportingForallLift (s : LamSort) := do
    let (upFunc, downFunc, ty, upTy, uOrig) ← mkImportAux s
    let isomTy ← mkIsomType upFunc downFunc ty upTy uOrig
    let forallLift := mkAppN (.const ``Embedding.ForallLift.ofForallLift [uOrig, .succ (← getU), .zero]) #[ty, upTy, isomTy]
    if !(← Meta.isTypeCorrect forallLift) then
      throwError "mkImportingForallLift :: Malformed forallLift {forallLift}"
    return forallLift

  def mkImportingExistLift (s : LamSort) := do
    let (upFunc, downFunc, ty, upTy, uOrig) ← mkImportAux s
    let isomTy ← mkIsomType upFunc downFunc ty upTy uOrig
    let existLift := mkAppN (.const ``Embedding.ExistLift.ofExistLift [uOrig, .succ (← getU)]) #[ty, upTy, isomTy]
    if !(← Meta.isTypeCorrect existLift) then
      throwError "mkImportingExistLift :: Malformed existLift {existLift}"
    return existLift

end ILLifting

-- Accept a new free variable representing term atom or lifted logical constant
-- Returns the index of it in the corresponding Array after we've inserted it into
--   its Array and HashMap
def newTermFVar (fvty : FVarType) (id : FVarId) (sort : LamSort) : ReifM LamTerm := do
  let varMap ← getVarMap
  match fvty with
  | .var   =>
    let varVal ← getVarVal
    let idx := varVal.size
    let .some orig := (← getUnliftMap).find? id
      | throwError "newTermFVar :: Unable to find un-lifted counterpart of {Expr.fvar id}"
    setVarVal (varVal.push (id, orig, sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .atom idx
  | .eqVar =>
    let eqLamTy ← getEqLamTy
    let idx := eqLamTy.size
    setEqLamTy (eqLamTy.push (← sort2IsomTysIdx sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.eqI idx)
  | .forallVar =>
    let forallLamTy ← getForallLamTy
    let idx := forallLamTy.size
    setForallLamTy (forallLamTy.push (← sort2IsomTysIdx sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.forallEI idx)
  | .existVar =>
    let existLamTy ← getExistLamTy
    let idx := existLamTy.size
    setExistLamTy (existLamTy.push (← sort2IsomTysIdx sort))
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.existEI idx)

def newTypeFVar (id : FVarId) : ReifM LamSort := do
  let tyVarMap ← getTyVarMap
  let tyVal ← getTyVal
  let idx := tyVal.size
  -- The universe level of the un-lifted counterpart of `id`
  let origSort ← Meta.inferType ((← getUnliftMap).find! id)
  let origSort := (← instantiateMVars origSort).headBeta
  let .sort lvl := origSort
    | throwError "newTypeFVar :: Unexpected sort {origSort}"
  let .some orig := (← getUnliftMap).find? id
    | throwError "newTypeFVar :: Unable to find un-lifted counterpart of {Expr.fvar id}"
  setTyVal (tyVal.push (id, orig, lvl))
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

-- This is an auxiliary function for `processTermFVar`. Please refer to `processTermFVar`
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
    newTermFVar .eqVar fid s
  | .forallVar =>
    let .forallE _ (.forallE _ upTy' _ _) _ _ := fidTy
      | throwError "processTermFVar :: Unexpected `∀` type {fidTy}"
    let s ← reifType upTy'
    newTermFVar .forallVar fid s
  | .existVar =>
    let .forallE _ (.forallE _ upTy' _ _) _ _ := fidTy
      | throwError "processTermFVar :: Unexpected `∃` type {fidTy}"
    let s ← reifType upTy'
    newTermFVar .existVar fid s

mutual

  partial def processTermFVar (fid : FVarId) : ReifM LamTerm := do
    if let .some n ← deBruijn? fid then
      return .bvar n
    let varMap ← getVarMap
    -- If the free variable has already been processed
    if let .some (fvarType, id) := varMap.find? fid then
      match fvarType with
      | .var => return .atom id
      | .eqVar => return .base (.eqI id)
      | .forallVar => return .base (.forallEI id)
      | .existVar => return .base (.existEI id)
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

-- Functions which models checker steps on the `meta` level
-- Steps that only requires looking at the `LamTerm`s and does not
--   require looking up the valuation should be put in the files
--   in the `Embedding` folder. There is no need to model them
--   on the `meta` level
section Checker

  def resolveLamBaseTermImport : LamBaseTerm → ReifM LamBaseTerm
  | .eqI n      => do return .eq (← lookupEqLamTy! n)
  | .forallEI n => do return .forallE (← lookupForallLamTy! n)
  | .existEI n  => do return .existE (← lookupExistLamTy! n)
  | t           => pure t

  def resolveImport : LamTerm → ReifM LamTerm
  | .atom n       => return .atom n
  | .base b       => return .base (← resolveLamBaseTermImport b)
  | .bvar n       => return .bvar n
  | .lam s t      => return .lam s (← resolveImport t)
  | .app s fn arg => return .app s (← resolveImport fn) (← resolveImport arg)

end Checker

-- This section should only be used when exporting terms to external provers
section ExportUtils

  def exportError.ImpPolyLog :=
    "Import versions of polymorphic logical " ++
    "constants should have been eliminated"

  def collectLamSortAtoms : LamSort → HashSet Nat
  | .atom n => HashSet.empty.insert n
  | .base _ => HashSet.empty
  | .func a b => (collectLamSortAtoms a).insertMany (collectLamSortAtoms b)

  -- Collect type atoms in a LamBaseTerm
  def collectLamBaseTermAtoms (b : LamBaseTerm) : ReifM (HashSet Nat) := do
    let s? : Option LamSort ← (do
      match b with
      | .eqI _ => throwError ("collectAtoms :: " ++ exportError.ImpPolyLog)
      | .forallEI _ => throwError ("collectAtoms :: " ++ exportError.ImpPolyLog)
      | .existEI _ => throwError ("collectAtoms :: " ++ exportError.ImpPolyLog)
      | .eq s => return .some s
      | .forallE s => return .some s
      | .existE s => return .some s
      | _ => return none)
    if let .some s := s? then
      return collectLamSortAtoms s
    else
      return HashSet.empty    

  -- The first hashset is the type atoms
  -- The second hashset is the term atoms
  -- This function is called when we're trying to export terms
  --   from `λ` to external provers, e.g. Lean/Duper
  -- Therefore, we expect that `eqI, forallEI` and `existEI`
  --   does not occur in the `LamTerm`
  def collectAtoms : LamTerm → ReifM (HashSet Nat × HashSet Nat)
  | .atom n => do
    let (_, _, s) ← lookupVarVal! n
    return (collectLamSortAtoms s, HashSet.empty.insert n)
  | .base b => do
    return (← collectLamBaseTermAtoms b, HashSet.empty)
  | .bvar _ => pure (HashSet.empty, HashSet.empty)
  | .lam s t => do
    let (typeHs, termHs) ← collectAtoms t
    let sHs := collectLamSortAtoms s
    return (mergeHashSet typeHs sHs, termHs)
  | .app _ t₁ t₂ => do
    let (typeHs₁, termHs₁) ← collectAtoms t₁
    let (typeHs₂, termHs₂) ← collectAtoms t₂
    return (mergeHashSet typeHs₁ typeHs₂, mergeHashSet termHs₁ termHs₂)

end ExportUtils

end Auto.LamReif