import Lean
import Auto.Lib.MonadUtils
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
import Auto.MathlibEmulator
import Auto.Translation.LamPULift
import Auto.Embedding.LamChecker
open Lean

initialize
  registerTraceClass `auto.lamReif
  registerTraceClass `auto.buildChecker

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
  -- The first `id : FVarId` is the free variable associated with the sort atom
  -- The second `e : Expr` is the un-lifted counterpart of the first `FVarId`
  --   (!) Note that `id ≝ GLift.up.{lvl, u} e`, where `u ← getU`
  -- The thrid `lvl : level` is the sort level of the second `Expr`
  -- Let `u ← getU`. The following two expressions are the interpretation of
  --   the sort atom:
  --   (1) `LiftTyConv.{lvl, u} (Expr.fvar id)`
  --   (2) `GLift.{lvl, u} e`
  tyVal       : Array (FVarId × Expr × Level)   := #[]
  -- The `FVarId` is the valuation of the atom
  -- The `Expr` is the un-lifted counterpart of `FVarId`
  -- The `LamSort` is the λ sort of the atom
  varVal      : Array (FVarId × Expr × LamSort) := #[]
  -- lamILTy
  lamILTy     : Array LamSort                   := #[]
  -- Inverse of `lamILTy`
  isomTyMap   : HashMap LamSort Nat             := HashMap.empty
  -- This array contains assertions that have external (lean) proof
  --   The first `e : Expr` is the proof of the assertion
  --   The second `t : LamTerm` is the corresponding λ term,
  --     where all `eq, ∀, ∃` are of import version
  --   The third `Nat` is the position of this assertion within
  --     the ImportTable
  -- To be precise, we require that `e : GLift.down t.interp`
  assertions  : Array (Expr × LamTerm × Nat)    := #[]
  -- The `n`-th element of the ImportTable would be `assertions[importMap.get! n]!`
  importMap   : HashMap Nat Nat                 := HashMap.empty
  -- `Embedding/LamChecker/ChkSteps`
  chkSteps    : Array (ChkStep × Nat)           := #[]
  -- We insert entries into `wfTable` and `validTable` through two different ways
  -- 1. Calling `newChkStepValid`
  -- 2. Validness facts from the ImportTable are treated in `newAssertions`
  -- `Embedding/LamChecker/RTable.wf`
  wfTable     : Array (List LamSort × LamSort × LamTerm) := #[]
  -- `Embedding/LamChecker/RTable.valid`
  validTable  : Array (List LamSort × LamTerm)           := #[]
  -- Something about the universes level `u`
  -- Suppose `u ← getU`
  -- 1. `tyVal : Nat → Type u`
  -- 2. `LamValuation.{u}`
  -- 3. All the `GLift/GLift.up/GLift.down` has level parameter list `[?, u]`
deriving Inhabited

abbrev ReifM := StateRefT State ULiftM

@[inline] def ReifM.run' (x : ReifM α) (s : State) := Prod.fst <$> x.run s

#genMonadState ReifM

def sort2LamILTyIdx (s : LamSort) : ReifM Nat := do
  let isomTyMap ← getIsomTyMap
  match isomTyMap.find? s with
  | .some n => return n
  | .none =>
    let lamILTy ← getLamILTy
    let idx := lamILTy.size
    setLamILTy (lamILTy.push s)
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

def lookupLamILTy! (idx : Nat) : ReifM LamSort := do
  if let .some s := (← getLamILTy)[idx]? then
    return s
  else
    throwError "lookupIsomTy! :: Unknown index {idx}"

def lookupImportMap! (wPos : Nat) : ReifM Nat := do
  if let .some idx := (← getImportMap).find? wPos then
    return idx
  else
    throwError "lookupImportMap! :: Unknown import table entry {wPos}"

def lookupImportTableEntry! (wPos : Nat) : ReifM (Expr × LamTerm × Nat) := do
  if let .some r := (← getAssertions).get? (← lookupImportMap! wPos) then
    return r
  else
    throwError "lookupImportTableEntry! :: Unknown import table entry {wPos}"

def lookupWfTable! (wPos : Nat) : ReifM (List LamSort × LamSort × LamTerm) := do
  if let .some r := (← getWfTable).get? wPos then
    return r
  else
    throwError "lookupWfTable :: Unknown wfTable entry {wPos}"

def lookupValidTable! (vPos : Nat) : ReifM (List LamSort × LamTerm) := do
  if let .some r := (← getValidTable).get? vPos then
    return r
  else
    throwError "lookupValidTable! :: Unknown validTable entry {vPos}"

def resolveLamBaseTermImport : LamBaseTerm → ReifM LamBaseTerm
| .eqI n      => do return .eq (← lookupLamILTy! n)
| .forallEI n => do return .forallE (← lookupLamILTy! n)
| .existEI n  => do return .existE (← lookupLamILTy! n)
| t           => pure t

-- Models `resolveImport` on the `meta` level
def resolveImport : LamTerm → ReifM LamTerm
| .atom n       => return .atom n
| .base b       => return .base (← resolveLamBaseTermImport b)
| .bvar n       => return .bvar n
| .lam s t      => return .lam s (← resolveImport t)
| .app s fn arg => return .app s (← resolveImport fn) (← resolveImport arg)

-- This is the inverse of `resolveImport`
-- After exporting `LamTerm`s to external prover and running
--   the external prover, we would like to accept the proof
--   returned by the prover. If we already know that the proof
--   returned by the prover corresponds to `t : LamTerm`, then
--   we don't need to `uLiftAndReify` the proof again.
-- However, since `t` is exported from `ReifM`, all import
--   versions of `eq, ∀, ∃` are already resolved and `t.interp`
--   may not be defeq to the type of the proof returned by
--   the prover. So, we have to build the import version `tI`
--   of `t` so that `tI.interp ≝ proof`
def mkImportVersion : LamTerm → ReifM LamTerm
| .atom n => return (.atom n)
| .base b =>
  match b with
  | .eq s      => return .base (.eqI (← sort2LamILTyIdx s))
  | .forallE s => return .base (.forallEI (← sort2LamILTyIdx s))
  | .existE s  => return .base (.existEI (← sort2LamILTyIdx s))
  | b => return .base b
| .bvar n => return (.bvar n)
| .lam s t => do
  return .lam s (← mkImportVersion t)
| .app s t₁ t₂ => do
  return .app s (← mkImportVersion t₁) (← mkImportVersion t₂)

-- A new `ChkStep` that produces `LamThmWF` certificate
-- `res` is the result of the `ChkStep`
-- Returns the position of the result of this `ChkStep` in the `wfTable`
def newWfChkStep (c : ChkStep) (res : List LamSort × LamSort × LamTerm) : ReifM Nat := do
  setChkSteps ((← getChkSteps).push (c, (← getWfTable).size))
  let wfsize := (← getWfTable).size
  setWfTable ((← getWfTable).push res)
  return wfsize

-- A new `ChkStep` that produces `LamThmValid` certificate
-- `res` is the result of the `ChkStep`
-- Returns the position of the result of this `ChkStep` in the `validTable`
def newValidChkStep (c : ChkStep) (res : List LamSort × LamTerm) : ReifM Nat := do
  setChkSteps ((← getChkSteps).push (c, (← getValidTable).size))
  let vsize := (← getValidTable).size
  setValidTable ((← getValidTable).push res)
  return vsize

-- A new assertion `proof : ty`
-- Returns the position of the `resolveImport`-ed LamTerm inside the `validTable`
def newAssertion (proof : Expr) (ty : LamTerm) : ReifM Nat := do
  let validTable ← getValidTable
  -- Position of external proof within the ImportTable
  let wPos := validTable.size
  setValidTable (validTable.push ([], ty))
  -- First push the term into `validTable` so that `validTable[wPos] = ty`,
  --   then call `newChkStepValid` so that the `(← getValidTable).size` within
  --   it gives the desired result
  let ret ← newValidChkStep (.validOfResolveImport wPos) ([], ← resolveImport ty)
  let assertions ← getAssertions
  -- `assertionIdx` is the index of the new (Expr × LamTerm) within `assertions`
  let assertionIdx := assertions.size
  setAssertions (assertions.push (proof, ty, wPos))
  setImportMap ((← getImportMap).insert wPos assertionIdx)
  return ret

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
    let sortOrig ← normalizeType (← Meta.inferType ty)
    let .sort uOrig := sortOrig
      | throwError "mkIsomType :: Unexpected sort {sortOrig} when processing sort {repr s}"
    return (upFunc, downFunc, ty, upTy, uOrig)

  set_option pp.universes true
  def mkIsomType (upFunc downFunc ty upTy : Expr) (uOrig : Level) : ReifM Expr := do
    let u ← getU
    let eq₁ : Expr := mkLambda `_ .default ty (mkAppN (.const ``Eq.refl [uOrig]) #[ty, .bvar 0])
    let eq₂ : Expr := mkLambda `_ .default upTy (mkAppN (.const ``Eq.refl [.succ u]) #[upTy, .bvar 0])
    let isomTy : Expr := mkAppN (.const ``Embedding.IsomType.mk [uOrig, .succ u]) #[ty, upTy, upFunc, downFunc, eq₁, eq₂]
    return isomTy

  -- Suppose `u ← getU`, this function returns a term of type `ILLift.{u} s.interpAsLifted`
  def mkImportingILLift (s : LamSort) := do
    let (upFunc, downFunc, ty, upTy, uOrig) ← mkImportAux s
    let isomTy ← mkIsomType upFunc downFunc ty upTy uOrig
    let ilLift := mkAppN (.const ``ILLift.ofIsomTy [uOrig, (← getU)]) #[ty, upTy, isomTy]
    -- if !(← Meta.isTypeCorrectCore ilLift) then
    --   throwError "mkImportingEqLift :: Malformed eqLift {ilLift}"
    return ilLift

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
    let idx ← sort2LamILTyIdx sort
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.eqI idx)
  | .forallVar =>
    let idx ← sort2LamILTyIdx sort
    setVarMap (varMap.insert id (fvty, idx))
    return .base (.forallEI idx)
  | .existVar =>
    let idx ← sort2LamILTyIdx sort
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

-- Returns the positions of the reified and `resolveImport`-ed facts
--   within the `validTable`
def reifFacts (facts : Array ULiftedFact) : ReifM (Array Nat) :=
  facts.mapM (fun (proof, tyLift) => do
    trace[auto.lamReif] "Reifying {proof} : {tyLift}"
    let lamty ← reifTerm tyLift
    trace[auto.lamReif] "Successfully reified proof to λterm `{repr lamty}`"
    newAssertion proof lamty)

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

-- `cont` is what we need to do after we ulift and reify the facts. Its
--    argument is the position of the reified and `resolveImport`-ed
--    facts within the `validTable`
def uLiftAndReify (facts : Array Reif.UMonoFact) (cont : Array Nat → ReifM α) : ReifM α :=
  withULiftedFacts checkInterpretedConst facts (fun pfacts => do
    let arr ← reifFacts pfacts;
    cont arr)

section Checker

  /-- `Unit test`
  unsafe def act (e : Expr) : Lean.Elab.TermElabM Unit := do
    let e' ← exprFromExpr e
    IO.println e'
    Meta.coreCheck e'
  
  #getExprAndApply[BinTree.toLCtx (α:=LamSort) (BinTree.ofListFoldl [LamSort.base .prop]) (.base .prop)|act]
  -/

  -- Functions that operates on the checker table

  -- `t₁ → t₂ → ⋯ → tₙ → t` , `t₁`, `t₂`, ⋯, `tₙ` implies `t`
  -- `imp` is the position of `t₁ → t₂ → ⋯ → tₙ → t` in the `wfTable`
  -- `hyps` are the positions of `t₁`, `t₂`, ⋯, `tₙ` in the `validTable`
  -- Returns the position of the new `t` in the valid table
  def impApps (imp : Nat) (hyps : Array Nat) : ReifM Nat := do
    let mut imp := imp
    let mut impV ← lookupValidTable! imp
    for hyp in hyps do
      let (lctx, t) := impV
      let (lctx', t') ← lookupValidTable! hyp
      if !(lctx'.beq lctx) then
        throwError "impApps : LCtx mismatch, `{repr lctx'}` ≠ `{repr lctx}`"
      let .app (.base .prop) (.app (.base .prop) (.base .imp) hypT) conclT := t
        | throwError "imApps : Error, `{repr t}` is not an implication"
      if !(hypT.beq t') then
        throwError "impApps : Term mismatch, `{repr hypT}` ≠ `{repr t'}`"
      impV := (lctx, conclT)
      imp ← newValidChkStep (.validOfImp imp hyp) impV
    return imp

  -- Functions that turns data structure in `ReifM.State` into `Expr`

  def checkerStats : ReifM (Array (String × Nat)) := do
    let ret : Array (String × Nat) := #[]
    let ret := ret.push ("tyVal", (← getTyVal).size)
    let ret := ret.push ("varVal", (← getVarVal).size)
    let ret := ret.push ("ilLamTy", (← getLamILTy).size)
    let ret := ret.push ("importTable", (← getImportMap).size)
    let ret := ret.push ("chkSteps", (← getChkSteps).size)
    let ret := ret.push ("wfTable", (← getWfTable).size)
    let ret := ret.push ("validTable", (← getValidTable).size)
    return ret

  def printCheckerStats : ReifM Unit := do
    let stats := (← checkerStats).map (fun (s, n) => "  " ++ s ++ s!": {n}")
    let ss := #["Checker Statics :"] ++ stats
    trace[auto.buildChecker] (String.intercalate "\n" ss.data)

  def buildChkStepsExpr : ReifM Expr := do
    let chkSteps ← getChkSteps
    -- `ChkSteps` are run using `foldl`, so we use `BinTree.ofListFoldl`
    let e := Lean.toExpr (BinTree.ofListFoldl chkSteps.data)
    -- if !(← Meta.isTypeCorrectCore e) then
    --   throwError "buildChkSteps :: Malformed expression"
    return e

    -- Given a list of expression of type `ty`, construct the corresponding `lctx`
  private def exprListToLCtx (l : List Expr) (lvl : Level) (ty : Expr) :=
    @BinTree.toLCtx Expr ⟨lvl, Prop⟩ (instExprToExprId ty) (BinTree.ofListGet l)

  def buildTyVal : ReifM Expr := do
    let u ← getU
    -- `tyVal : List (Type u)`
    let tyVal : List Expr := (← getTyVal).data.map (fun (id, _, lvl) =>
      Expr.app (.const ``Embedding.LiftTyConv [lvl, u]) (.fvar id))
    -- `tyValExpr : Nat → Type u`
    let tyValExpr := exprListToLCtx tyVal (.succ u) (.sort (.succ u)) (.sort u)
    -- if !(← Meta.isTypeCorrectCore tyValExpr) then
    --   throwError "buildLamValuation :: Malformed tyVal"
    return tyValExpr

  -- **Build `LamVarTy` and `varVal`**
  def buildVarValExpr (tyValExpr : Expr) : ReifM (Expr × Expr) := do
    let u ← getU
    let lamSortExpr := Expr.const ``LamSort []
    let varValPair := (← getVarVal).data
    let vars := varValPair.map (fun (id, _, s) =>
      let sExpr := toExpr s
      Lean.mkApp3 (.const ``varValSigmaMk [u]) tyValExpr sExpr (Expr.fvar id))
    let varBundleExpr := exprListToLCtx vars u (Lean.mkApp2
      (.const ``Sigma [.zero, u]) lamSortExpr
      (.app (.const ``LamSort.interp [u]) tyValExpr))
      (.app (.const ``varValSigmaDefault [u]) tyValExpr)
    let lamVarTyExpr := Expr.lam `n (.const ``Nat []) (
        Lean.mkApp2 (.const ``varValSigmaFst [u]) tyValExpr (.app varBundleExpr (.bvar 0))
      ) .default
    let varValExpr := Expr.lam `n (.const ``Nat []) (
        Lean.mkApp2 (.const ``varValSigmaSnd [u]) tyValExpr (.app varBundleExpr (.bvar 0))
      ) .default
    return (lamVarTyExpr, varValExpr)

  -- **Build `lamILTy` and `ilVal`**
  def buildILValExpr (tyValExpr : Expr) : ReifM (Expr × Expr) := do
    let u ← getU
    let lamSortExpr := Expr.const ``LamSort []
    let lamILTy := (← getLamILTy).data
    -- `ils : List ((s : LamSort) × ILLift.{u} (s.interp tyVal))`
    let ils ← lamILTy.mapM (fun s => do
      let sExpr := toExpr s
      let ilVal ← mkImportingILLift s
      return Lean.mkApp3 (.const ``ilValSigmaMk [u]) tyValExpr sExpr ilVal)
    let ilBundleExpr := exprListToLCtx ils u (Lean.mkApp2
      (.const ``Sigma [.zero, u]) lamSortExpr
      (.app (.const ``ilValSigmaβ [u]) tyValExpr))
      (.app (.const ``ilValSigmaDefault [u]) tyValExpr)
    let lamILTyExpr := Expr.lam `n (.const ``Nat []) (
        Lean.mkApp2 (.const ``ilValSigmaFst [u]) tyValExpr (.app ilBundleExpr (.bvar 0))
      ) .default
    let ilValExpr := Expr.lam `n (.const ``Nat []) (
        Lean.mkApp2 (.const ``ilValSigmaSnd [u]) tyValExpr (.app ilBundleExpr (.bvar 0))
      ) .default
    return (lamILTyExpr, ilValExpr)

  def buildLamValuationExpr : ReifM Expr := do
    -- let startTime ← IO.monoMsNow
    let u ← getU
    let tyValExpr ← buildTyVal
    let tyValTy := Expr.forallE `_ (.const ``Nat []) (.sort (.succ u)) .default
    let lamValuationExpr ← Meta.withLetDecl `tyVal tyValTy tyValExpr fun tyValFVarExpr => do
      let (lamVarTyExpr, varValExpr) ← buildVarValExpr tyValFVarExpr
      let (lamILTyExpr, ilValExpr) ← buildILValExpr tyValFVarExpr
      let lamTyValExpr := Lean.mkApp2 (.const ``LamTyVal.mk []) lamVarTyExpr lamILTyExpr
      let lamValuationExpr := Lean.mkApp4 (.const ``LamValuation.mk [u]) lamTyValExpr tyValExpr ilValExpr varValExpr
      Meta.mkLetFVars #[tyValFVarExpr] lamValuationExpr
    -- if !(← Meta.isTypeCorrectCore lamValuationExpr) then
    --   throwError "buildLamValuation :: Malformed LamValuation"
    -- trace[auto.buildChecker] "LamValuation typechecked in time {(← IO.monoMsNow) - startTime}"
    return lamValuationExpr

  -- debug
  -- def ofType (α : Sort u) (x : α) := x

  -- `lvalExpr` is the `LamValuation`
  def buildImportTableExpr (lvalExpr : Expr) : ReifM Expr := do
    -- let startTime ← IO.monoMsNow
    let u ← getU
    let lamTermExpr := Expr.const ``LamTerm []
    -- Record the entries in the importTable for debug purpose
    let mut entries : Array (Expr × Expr) := #[]
    let mut importTable : BinTree Expr := BinTree.leaf
    for (step, _) in (← getChkSteps) do
      if let .validOfResolveImport vPos := step then
        let (e, t, _) ← lookupImportTableEntry! vPos
        let tExpr := Lean.toExpr t
        let itEntry := Lean.mkApp3 (.const ``importTablePSigmaMk [u]) lvalExpr tExpr e
        importTable := importTable.insert vPos itEntry
        entries := entries.push (e, tExpr)
    let type := Lean.mkApp2 (.const ``PSigma [.succ .zero, .zero])
      lamTermExpr (.app (.const ``importTablePSigmaβ [u]) lvalExpr)
    let importTableExpr := (@instToExprBinTree Expr
      (instExprToExprId type) ⟨.zero, Prop⟩).toExpr importTable
    -- if !(← Meta.isTypeCorrectCore importTableExpr) then
    --   let tyValExpr ← buildTyVal
    --   for (e, tExpr) in entries do
    --     let tInterp := Lean.mkApp4 (.const ``LamTerm.interpAsProp [u])
    --       lvalExpr (.const ``dfLCtxTy []) (.app (.const ``dfLCtxTerm [u]) tyValExpr) tExpr
    --     let tInterp ← Meta.zetaReduce tInterp
    --     let ofTypeExpr := Lean.mkApp2 (.const ``ofType [.succ u])
    --       (.app (.const ``Embedding.LiftTyConv [.zero, u]) tInterp)
    --       (Lean.mkApp2 (.const ``Embedding.GLift.up [.zero, u]) (← Meta.inferType e) e)
    --     if !(← Meta.isTypeCorrect e) then
    --       trace[auto.buildChecker] "buildImportTable :: Proof {e} is not type correct"
    --       Meta.check e
    --     if !(← Meta.isTypeCorrect ofTypeExpr) then
    --       throwError "buildImportTable :: Malformed ImportTable Entry, proof : {e}, interp : {tInterp}"
    --     else
    --       trace[auto.buildChecker] "Well-formed ImportTable Entry"
    --   throwError "buildImportTable :: Malformed ImportTable, but all entries are well-formed"
    -- trace[auto.buildChecker] "ImportTable typechecked in time {(← IO.monoMsNow) - startTime}"
    return importTableExpr

  -- `entryIdx` is the entry we want to retrieve from the `validTable`
  -- The `expr` returned is a proof of the `LamThmValid`-ness of the entry
  def buildCheckerExpr (entryIdx : Nat) : ReifM Expr := do
    printCheckerStats
    let startTime ← IO.monoMsNow
    let u ← getU
    let lvalExpr ← buildLamValuationExpr
    let lvalTy := Expr.const ``LamValuation [u]
    let checker ← Meta.withLetDecl `lval lvalTy lvalExpr fun lvalFVarExpr => do
      let itExpr ← buildImportTableExpr lvalFVarExpr
      let csExpr ← buildChkStepsExpr
      let wholeChecker := Lean.mkApp3 (.const ``Checker [u]) lvalFVarExpr itExpr csExpr
      let validInv ← Meta.mkAppM ``And.right #[wholeChecker]
      let validExpr := Lean.toExpr (BinTree.ofListGet (← getValidTable).data)
      let valExpr := Lean.toExpr (← lookupValidTable! entryIdx)
      let nExpr := Lean.toExpr entryIdx
      let eqExpr ← Meta.mkAppM ``Eq.refl #[← Meta.mkAppM ``Option.some #[valExpr]]
      let getEntry := Lean.mkApp6 (.const ``RTable.validInv_get [u])
        lvalExpr nExpr valExpr validExpr validInv eqExpr
      let getEntry ← Meta.mkLetFVars #[lvalFVarExpr] getEntry
      -- debug
      -- let rt := Lean.mkApp3 (.const ``ChkSteps.runFromBeginning [u]) lvalExpr itExpr csExpr
      -- let rt ← Meta.withTransparency .all <| Meta.reduceAll rt
      -- trace[auto.buildChecker] "Final RTable : {rt}, Expected valid : {validExpr}"
      trace[auto.buildChecker] "Checker expression built in time {(← IO.monoMsNow) - startTime}ms"
      return getEntry
    -- debug
    -- let startTime ← IO.monoMsNow
    -- if !(← Meta.isTypeCorrectCore checker) then
    --   trace[auto.buildChecker] "buildCheckerExpr :: Malformed checker {checker}"
    --   Meta.check checker
    -- trace[auto.buildChecker] "Checker typechecked in time {(← IO.monoMsNow) - startTime}"
    return checker

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