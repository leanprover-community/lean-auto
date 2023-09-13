import Lean
import Auto.Lib.MonadUtils
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
import Auto.Translation.ReifM
import Auto.MathlibEmulator
import Auto.Embedding.LamChecker
open Lean

initialize
  registerTraceClass `auto.lamReif
  registerTraceClass `auto.buildChecker
  registerTraceClass `auto.lamReif.printValuation
  registerTraceClass `auto.lamReif.printResult

namespace Auto.LamReif
open Embedding.Lam

-- We require that all instances of polymorphic constants,
--   including `∀`, `∃`, `BitVec`, are turned into free variables
--   before being sent to `LamReif.` Since propositional
--   implication `→` has the same representation as `∀` in Lean `Expr`,
--   we also require that they are turned into free variables.
-- In this way, the expression that `LamReif` receives is an
--   essentially higher-order term that can be reified directly.
structure State where
  -- Maps previously reified type to their type atom index
  tyVarMap    : HashMap Expr Nat                := {}
  -- Maps previously reified expressions to their term atom index
  -- Whenever we encounter an atomic expression, we look up
  --   `varMap`. If it's already reified, then `varMap`
  --   tells us about its index. If it's not reified, insert
  --   it to `varMap`.
  varMap      : HashMap Expr Nat                := {}
  -- `tyVal` is the inverse of `tyVarMap`
  -- The `e : Expr` is the un-lifted valuation of the type atom
  -- The `lvl : level` is the sort level of `e`
  -- Let `u ← getU`. The interpretation of the sort atom would be
  --   `GLift.{lvl, u} e`
  tyVal       : Array (Expr × Level)            := #[]
  -- The `e : Expr` is the un-lifted counterpart of the interpretation of
  --   the term atom
  -- The `s : LamSort` is the λ sort of the atom
  -- The interpretation of the sort atom would be `s.upfunc e`
  varVal      : Array (Expr × LamSort)          := #[]
  -- lamILTy
  lamILTy     : Array LamSort                   := #[]
  -- Inverse of `lamILTy`
  isomTyMap   : HashMap LamSort Nat             := {}
  /-
    This hashmap contains assertions that have external (lean) proof
    · The key `t : LamTerm` is the corresponding λ term,
      where all `eq, ∀, ∃` are not of import version
    · The first `e : Expr` is the proof of the assertion
    · The second `t' : LamTerm` is `← mkImportVersion t`
    · The thrid `n : Nat` is the position of the assertion in the `ImportTable`
    · To be precise, we require that `e : GLift.down t.interp`

    This field also corresponds to the `ImportTable` in `LamChecker.lean`
  -/
  assertions  : HashMap LamTerm (Expr × LamTerm × Nat) := {}
  -- `Embedding/LamChecker/ChkMap`
  -- `chkMap.find?[re]` returns the checkstep which proves `re`
  chkMap      : HashMap REntry (ChkStep × Nat)  := {}
  -- We insert entries into `rTable` through two different ways
  -- 1. Calling `newChkStep`
  -- 2. Validness facts from the ImportTable are treated in `newAssertions`
  rTable      : Array REntry                    := #[]
  -- This works as a cache for `BinTree.ofListGet rTable.data`
  rTableTree  : BinTree REntry                  := BinTree.leaf
  -- maxEVarSucc
  maxEVarSucc : Nat                             := 0
  -- lamEVarTy
  lamEVarTy   : BinTree LamSort                 := .leaf
  -- `u` is the universe level that all constants will lift to
  -- Something about the universes level `u`
  -- Suppose `u ← getU`
  -- · `tyVal : Nat → Type u`
  -- · `LamValuation.{u}`
  -- · All the `GLift/GLift.up/GLift.down` has level parameter list `[?, u]`
  u           : Level
deriving Inhabited

abbrev ReifM := StateRefT State Reif.ReifM

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

def lookupTyVal! (n : Nat) : ReifM (Expr × Level) := do
  if let .some r := (← getTyVal)[n]? then
    return r
  else
    throwError "lookupTyVal! :: Unknown type atom {n}"

-- Lookup valuation of term atom
def lookupVarVal! (n : Nat) : ReifM (Expr × LamSort) := do
  if let .some r := (← getVarVal)[n]? then
    return r
  else
    throwError "lookupVarVal! :: Unknown term atom {n}"

def lookupLamILTy! (idx : Nat) : ReifM LamSort := do
  if let .some s := (← getLamILTy)[idx]? then
    return s
  else
    throwError "lookupLamILTy! :: Unknown index {idx}"

def lookupAssertion! (t : LamTerm) : ReifM (Expr × LamTerm × Nat) := do
  if let .some r := (← getAssertions).find? t then
    return r
  else
    throwError "lookupAssertion! :: Unknown assertion {t}"

def lookupRTable! (pos : Nat) : ReifM REntry := do
  if let .some r := (← getRTable).get? pos then
    return r
  else
    throwError "lookupRTable! :: Unknown RTable entry {pos}"

def lookupREntryPos! (re : REntry) : ReifM Nat := do
  match (← getChkMap).find? re with
  | .some (_, n) => return n
  | .none =>
    match re with
    | .valid [] t =>
      match (← getAssertions).find? t with
      | .some (_, _, n) => return n
      | .none => throwError "lookupREntryPos! :: Unknown REntry {re}"
    | _ => throwError "lookupREntryPos! :: Unknown REntry {re}"

def lookupREntryProof? (re : REntry) : ReifM (Option (ChkStep ⊕ (Expr × LamTerm))) := do
  match (← getChkMap).find? re with
  | .some (cs, _) => return .some (.inl cs)
  | .none =>
    match re with
    | .valid [] t =>
      match (← getAssertions).find? t with
      | .some (e, t, _) => return .some (.inr (e, t))
      | .none => return .none
    | _ => return .none

def lookupREntryProof! (re : REntry) : ReifM (ChkStep ⊕ (Expr × LamTerm)) := do
  match ← lookupREntryProof? re with
  | .some proof => return proof
  | .none => throwError "lookupREntryProof! :: Unknown REntry {re}"

-- This should only be used at the meta level, i.e. in code that will
--   be evaluated during the execution of `auto`
private def getLamTyValAtMeta : ReifM LamTyVal := do
  let varVal ← getVarVal
  let varTy := varVal.map Prod.snd
  let lamILTy ← getLamILTy
  let lamEVarTy ← getLamEVarTy
  return ⟨fun n => varTy[n]?.getD (.base .prop),
          fun n => lamILTy[n]?.getD (.base .prop),
          fun n => (lamEVarTy.get? n).getD (.base .prop)⟩

def resolveLamBaseTermImport : LamBaseTerm → ReifM LamBaseTerm
| .eqI n      => do return .eq (← lookupLamILTy! n)
| .forallEI n => do return .forallE (← lookupLamILTy! n)
| .existEI n  => do return .existE (← lookupLamILTy! n)
| t           => pure t

-- Models `resolveImport` on the `meta` level
def resolveImport : LamTerm → ReifM LamTerm
| .atom n       => return .atom n
| .etom _       => throwError "resolveImport :: etom should not occur here"
| .base b       => return .base (← resolveLamBaseTermImport b)
| .bvar n       => return .bvar n
| .lam s t      => return .lam s (← resolveImport t)
| .app s fn arg => return .app s (← resolveImport fn) (← resolveImport arg)

-- This is the inverse of `resolveImport`
-- · When importing external proof `H : α`, we will reify `α`
--   into `t : LamTerm` using `reifTerm`. The `t` returned
--   by `reifTerm` has `eq` for `Eq`, `forallE` for `∀` and
--   `existE` for `∃`.
-- · It's easy to see that `t.interp` will not be definitionally
--   equal to `α` because `=, ∀, ∃` within `α` operates on the
--   original domain, while `=, ∀, ∃` in `t.interp` operates on
--   the lifted domain
-- · Therefore, we need to turn `=, ∀, ∃` in `t` into import
--   version to get `t'`, and design an appropriate `ilVal`,
--   such that `GLift.down t'.interp` is definitionally equal to `α`   
def mkImportVersion : LamTerm → ReifM LamTerm
| .atom n => return (.atom n)
| .etom _ => throwError "mkImportVersion :: etom should not occur here"
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

-- A new `ChkStep`. `res` is the result of the `ChkStep`
-- Returns the position of the result of this `ChkStep` in the `RTable`
def newChkStep (c : ChkStep) (res? : Option EvalResult) : ReifM EvalResult := do
  let ltv ← getLamTyValAtMeta
  let res := c.eval ltv.lamVarTy ltv.lamILTy ⟨← getRTableTree, ← getMaxEVarSucc, ← getLamEVarTy⟩
  if let .some res' := res? then
    if res' != res then
      throwError "newChkStep :: Result {res} of ChkStep {c} does not match with expected {res'}"
  match res with
  | .fail => throwError "newChkStep :: Evaluation of ChkStep {c} produces `fail`"
  | .addEntry re =>
    -- If `re` is already provable, do nothing
    if let .some _ ← lookupREntryProof? re then
      return res
    let rsize := (← getRTable).size
    setChkMap ((← getChkMap).insert re (c, rsize))
    setRTableTree ((← getRTableTree).insert rsize re)
    setRTable ((← getRTable).push re)
  return res

-- Returns the position of the entry inside the `RTable`
def addREntryToRTable (re : REntry) : ReifM Nat := do
  let rTable ← getRTable
  let pos := rTable.size
  setRTableTree ((← getRTableTree).insert pos re)
  setRTable (rTable.push re)
  return pos

-- **TODO**
-- `ty` is a reified assumption. `∀, ∃` and `=` in `ty` are supposed to
--   not be of the import version
-- The type of `proof` is definitionally equal to `GLift.down (← mkImportVersion ty).interp`
-- Returns the position of `ty` inside the `validTable` after inserting it
def newAssertion (proof : Expr) (ty : LamTerm) : ReifM Unit := do
  -- Because of the way we `buildImportTableExpr`, we need to deduplicate facts
  if (← getAssertions).contains ty then
    return
  let pos ← addREntryToRTable (.validEVar0 [] ty)
  -- This `mkImportVersion` must be called before we build the lval expression
  -- So it cannot be called on-the-fly in `buildImportTableExpr`
  let tyi ← mkImportVersion ty
  setAssertions ((← getAssertions).insert ty (proof, tyi, pos))
/-
  Computes `upFunc` and `downFunc` between `s.interpAsUnlifted` and `s.interpAsLifted`
  · `upFunc` is such that `upFunc binder` is equivalent to `binder↑`
  · `downFunc` is such that `downFunc binder↑` is equivalent to `binder`
  Return type:
  · The first `Expr` is `upFunc`
  · The second `Expr` is `downFunc`
  · The third `Expr` is `s.interpAsUnlifted`
  · The fourth `Expr` is `s.interpAsLifted`
-/
open Embedding in
partial def updownFunc (s : LamSort) : ReifM (Expr × Expr × Expr × Expr) :=
  match s with
  | .atom n => do
    let (orig, lvl) ← lookupTyVal! n
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

-- `(e, s)` is a pair from the `varVal` field of `LamReif.ReifM.State`
-- Returns the lifted counterpart of `e`
def varValInterp (e : Expr) (s : LamSort) : ReifM Expr := do
  let (up, _, _, _) ← updownFunc s
  return .app up e

section ILLifting

  open Embedding

  private def mkImportAux (s : LamSort) : ReifM (Expr × Expr × Expr × Expr × Level) := do
    let (upFunc, downFunc, ty, upTy) ← updownFunc s
    let sortOrig ← Expr.normalizeType (← Meta.inferType ty)
    let .sort uOrig := sortOrig
      | throwError "mkImportAux :: Unexpected sort {sortOrig} when processing sort {s}"
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
    -- debug
    -- if !(← Meta.isTypeCorrectCore ilLift) then
    --   throwError "mkImportingEqLift :: Malformed eqLift {ilLift}"
    return ilLift

end ILLifting

-- Accept a new expression representing λterm atom
-- Returns the index of it in the `varVal` array
def newTermExpr (e : Expr) (sort : LamSort) : ReifM LamTerm := do
  let varMap ← getVarMap
  let varVal ← getVarVal
  let idx := varVal.size
  setVarVal (varVal.push (e, sort))
  setVarMap (varMap.insert e idx)
  return .atom idx

def newTypeExpr (e : Expr) : ReifM LamSort := do
  let tyVarMap ← getTyVarMap
  let tyVal ← getTyVal
  let idx := tyVal.size
  -- The universe level of `e`
  let origSort ← Meta.inferType e
  let origSort := (← instantiateMVars origSort).headBeta
  let .sort lvl := origSort
    | throwError "newTypeExpr :: Unexpected sort {origSort}"
  setTyVal (tyVal.push (e, lvl))
  setTyVarMap (tyVarMap.insert e idx)
  return .atom idx

def processTypeExpr (e : Expr) : ReifM LamSort := do
  let tyVarMap ← getTyVarMap
  let e ← Reif.resolveTy e
  if let .some idx := tyVarMap.find? e then
    return .atom idx
  match e with
  | .sort lvl =>
    if ← Meta.isLevelDefEq lvl .zero then
      return .base .prop
    else
      newTypeExpr e
  | .const ``Int [] => return .base .int
  | .const ``Real [] => return .base .real
  | .app (.const ``Bitvec []) (.lit (.natVal n)) => return .base (.bv n)
  | _ => newTypeExpr e

-- At this point, there should only be non-dependent `∀`s in the type.
def reifType : Expr → ReifM LamSort
| .mdata _ e => reifType e
| e@(.forallE _ ty body _) => do
  if body.hasLooseBVar 0 then
    throwError "reifType :: Type {e} has dependent ∀"
  else
    return .func (← reifType ty) (← reifType body)
| e => processTypeExpr e

def processTermExprAux (e : Expr) : ReifM LamTerm :=
  match e with
  | .const ``True [] => return .base .trueE
  | .const ``False [] => return .base .falseE
  | .const ``Not [] => return .base .not
  | .const ``And [] => return .base .and
  | .const ``Or []  => return .base .or
  | .const ``Embedding.ImpF [u, v] => do
    if (← Meta.isLevelDefEq u .zero) ∧ (← Meta.isLevelDefEq v .zero) then
      return .base .imp
    else
      throwError "processTermExpr :: Non-propositional implication is not supported"
  | .const ``Iff [] => return .base .iff
  -- **TODO: Integer, Real number, Bit vector**
  -- `α` is the original (un-lifted) type
  | .app (.const ``Eq _) α =>
    return .base (.eq (← reifType α))
  | .app (.const ``Embedding.forallF _) α =>
    return .base (.forallE (← reifType α))
  | .app (.const ``Exists _) α =>
    return .base (.existE (← reifType α))
  | e => do
    let eTy ← instantiateMVars (← Meta.inferType e)
    let lamTy ← reifType eTy
    newTermExpr e lamTy

private def deBruijn? (lctx : HashMap FVarId Nat) (id : FVarId) : Option Nat :=
  match lctx.find? id with
  | .some n => lctx.size - 1 - n
  | .none   => none

def processTermExpr (lctx : HashMap FVarId Nat) (e : Expr) : ReifM LamTerm := do
  if let .fvar fid := e then
    if let .some n := deBruijn? lctx fid then
      return .bvar n
  let e ← Reif.resolveVal e
  let varMap ← getVarMap
  -- If the expression has already been processed
  if let .some id := varMap.find? e then
    return .atom id
  -- If the expression has not been processed
  processTermExprAux e

partial def reifTerm (lctx : HashMap FVarId Nat) : Expr → ReifM LamTerm
| .app fn arg => do
  let lamFn ← reifTerm lctx fn
  let lamArg ← reifTerm lctx arg
  let argTy ← Meta.inferType arg
  let lamTy ← reifType argTy
  return .app lamTy lamFn lamArg
| .lam name ty body binfo => do
  let lamTy ← reifType ty
  let body ← Meta.withLocalDecl name binfo ty fun fvar => do
    let body' := body.instantiate1 fvar
    reifTerm (lctx.insert fvar.fvarId! lctx.size) body'
  return .lam lamTy body
| e => processTermExpr lctx e

-- Return the positions of the reified and `resolveImport`-ed facts
--   within the `validTable`
def reifFacts (facts : Array UMonoFact) : ReifM (Array LamTerm) :=
  facts.mapM (fun (proof, ty) => do
    trace[auto.lamReif] "Reifying {proof} : {ty}"
    let lamty ← reifTerm .empty ty
    trace[auto.lamReif.printResult] "Successfully reified proof of {← Meta.zetaReduce ty} to λterm `{lamty}`"
    newAssertion proof lamty
    return lamty)

section Checker

  /-- `Unit test`
  unsafe def act (e : Expr) : Lean.Elab.TermElabM Unit := do
    let e' ← exprFromExpr e
    IO.println e'
    Meta.coreCheck e'
  
  #getExprAndApply[BinTree.toLCtx (α:=LamSort) (BinTree.ofListFoldl [LamSort.base .prop]) (.base .prop)|act]
  -/

  -- Functions that operates on the checker table

  def validOfImp (v₁₂ : REntry) (v₁ : REntry) : ReifM REntry := do
    let p₁₂ ← lookupREntryPos! v₁₂
    let p₁ ← lookupREntryPos! v₁
    let .addEntry re ← newChkStep (.validOfImp p₁₂ p₁) .none
      | throwError "validOfImp :: Unexpected evaluation result"
    return re

  def validOfImps (impV : REntry) (hypVs : Array REntry) : ReifM REntry := do
    let imp ← lookupREntryPos! impV
    let ps ← hypVs.mapM lookupREntryPos!
    let .addEntry re ← newChkStep (.validOfImps imp ps.data) .none
      | throwError "validOfImps :: Unexpected evaluation result"
    return re

  -- Functions that turns data structure in `ReifM.State` into `Expr`

  def checkerStats : ReifM (Array (String × Nat)) := do
    let ret : Array (String × Nat) := #[]
    let ret := ret.push ("tyVal", (← getTyVal).size)
    let ret := ret.push ("varVal", (← getVarVal).size)
    let ret := ret.push ("ilLamTy", (← getLamILTy).size)
    let ret := ret.push ("assertions", (← getAssertions).size)
    let ret := ret.push ("chkMap", (← getChkMap).size)
    let ret := ret.push ("RTable", (← getRTable).size)
    return ret

  def printCheckerStats : ReifM Unit := do
    let stats := (← checkerStats).map (fun (s, n) => "  " ++ s ++ s!": {n}")
    let ss := #["Checker Statistics:"] ++ stats
    trace[auto.buildChecker] (String.intercalate "\n" ss.data)

  def printValuation : ReifM Unit := do
    let varVal ← getVarVal
    for ((e, s), idx) in varVal.zip ⟨List.range varVal.size⟩ do
      trace[auto.lamReif.printValuation] "Term Atom {idx} : {toString s} := {e}"
    let tyVal ← getTyVal
    for ((e, lvl), idx) in tyVal.zip ⟨List.range tyVal.size⟩ do
      trace[auto.lamReif.printValuation] "Type Atom {idx} := {e} : {Expr.sort lvl}"
    let lamIl ← getLamILTy
    for (s, idx) in lamIl.zip ⟨List.range lamIl.size⟩ do
      trace[auto.lamReif.printValuation] "LamILTy {idx} := {s}"

  def buildChkStepsExpr : ReifM Expr := do
    let chkMap ← getChkMap
    let mut chkSteps := #[]
    for re in (← getRTable) do
      if let .some (cs, n) := chkMap.find? re then
        chkSteps := chkSteps.push (cs, n)
    -- `ChkMap` are run using `foldl`, so we use `BinTree.ofListFoldl`
    let e := Lean.toExpr (BinTree.ofListFoldl chkSteps.data)
    -- if !(← Meta.isTypeCorrectCore e) then
    --   throwError "buildChkMap :: Malformed expression"
    return e

    -- Given a list of expression of type `ty`, construct the corresponding `BinTree`
  private def exprListToBinTree (l : List Expr) (lvl : Level) (ty : Expr) :=
    (@instToExprBinTree Expr (instExprToExprId ty) ⟨lvl, Prop⟩).toExpr (BinTree.ofListGet l)

    -- Given a list of expression of type `ty`, construct the corresponding `lctx`
  private def exprListToLCtx (l : List Expr) (lvl : Level) (ty : Expr) :=
    @BinTree.toLCtx Expr ⟨lvl, Prop⟩ (instExprToExprId ty) (BinTree.ofListGet l)

  def buildTyVal : ReifM Expr := do
    let u ← getU
    -- `tyVal : List (Type u)`
    let tyVal : List Expr := (← getTyVal).data.map (fun (e, lvl) =>
      Expr.app (.const ``Embedding.GLift [lvl, u]) e)
    -- `tyValExpr : Nat → Type u`
    let tyValExpr := exprListToLCtx tyVal (.succ u) (.sort (.succ u)) (.sort u)
    -- if !(← Meta.isTypeCorrectCore tyValExpr) then
    --   throwError "buildLamValuation :: Malformed tyVal"
    return tyValExpr

  -- **Build `LamVarTy` and `varVal`**
  def buildVarExpr (tyValExpr : Expr) : ReifM Expr := do
    let u ← getU
    let lamSortExpr := Expr.const ``LamSort []
    let varValPair := (← getVarVal).data
    let vars ← varValPair.mapM (fun (e, s) => do
      let sExpr := toExpr s
      return Lean.mkApp3 (.const ``varSigmaMk [u]) tyValExpr sExpr (← varValInterp e s))
    return exprListToBinTree vars u (Lean.mkApp2
      (.const ``Sigma [.zero, u]) lamSortExpr
      (.app (.const ``LamSort.interp [u]) tyValExpr))

  -- **Build `lamILTy` and `ilVal`**
  def buildILExpr (tyValExpr : Expr) : ReifM Expr := do
    let u ← getU
    let lamSortExpr := Expr.const ``LamSort []
    let lamILTy := (← getLamILTy).data
    -- `ils : List ((s : LamSort) × ILLift.{u} (s.interp tyVal))`
    let ils ← lamILTy.mapM (fun s => do
      let sExpr := toExpr s
      let ilVal ← mkImportingILLift s
      return Lean.mkApp3 (.const ``ilSigmaMk [u]) tyValExpr sExpr ilVal)
    return exprListToBinTree ils u (Lean.mkApp2
      (.const ``Sigma [.zero, u]) lamSortExpr
      (.app (.const ``ilβ [u]) tyValExpr))

  def buildCPValExpr : ReifM Expr := do
    -- let startTime ← IO.monoMsNow
    let u ← getU
    let tyValExpr ← buildTyVal
    let tyValTy := Expr.forallE `_ (.const ``Nat []) (.sort (.succ u)) .default
    let lamValuationExpr ← Meta.withLetDecl `tyVal tyValTy tyValExpr fun tyValFVarExpr => do
      let varExpr ← buildVarExpr tyValFVarExpr
      let ilExpr ← buildILExpr tyValFVarExpr
      let checkerValuationExpr := Lean.mkApp3 (.const ``CPVal.mk [u]) tyValExpr varExpr ilExpr
      Meta.mkLetFVars #[tyValFVarExpr] checkerValuationExpr
    -- if !(← Meta.isTypeCorrectCore lamValuationExpr) then
    --   throwError "buildLamValuation :: Malformed LamValuation"
    -- trace[auto.buildChecker] "LamValuation typechecked in time {(← IO.monoMsNow) - startTime}"
    return lamValuationExpr

  -- `lvalExpr` is the `LamValuation`
  def buildImportTableExpr (chkValExpr : Expr) : ReifM Expr := do
    -- let startTime ← IO.monoMsNow
    let u ← getU
    let lamTermExpr := Expr.const ``LamTerm []
    -- Record the entries in the importTable for debug purpose
    let mut entries : Array (Expr × Expr) := #[]
    let mut importTable : BinTree Expr := BinTree.leaf
    for (_, (e, ti, n)) in (← getAssertions).toList do
      let tExpr := Lean.toExpr ti
      let itEntry := Lean.mkApp3 (.const ``importTablePSigmaMk [u]) chkValExpr tExpr e
      importTable := importTable.insert n itEntry
      entries := entries.push (e, tExpr)
    let type := Lean.mkApp2 (.const ``PSigma [.succ .zero, .zero])
      lamTermExpr (.app (.const ``importTablePSigmaβ [u]) chkValExpr)
    let importTableExpr := (@instToExprBinTree Expr
      (instExprToExprId type) ⟨.zero, Prop⟩).toExpr importTable
    -- if !(← Meta.isTypeCorrectCore importTableExpr) then
    --   let tyValExpr ← buildTyVal
    --   for (e, tExpr) in entries do
    --     let tInterp := Lean.mkApp4 (.const ``LamTerm.interpAsProp [u])
    --       lvalExpr (.const ``dfLCtxTy []) (.app (.const ``dfLCtxTerm [u]) tyValExpr) tExpr
    --     let tInterp ← Meta.zetaReduce tInterp
    --     let ofTypeExpr := Lean.mkApp2 (.const ``id [.succ u])
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

  -- `re` is the entry we want to retrieve from the `validTable`
  -- The `expr` returned is a proof of the `LamThmValid`-ness of the entry
  def buildFullCheckerExprFor (re : REntry) : ReifM Expr := do
    printCheckerStats
    let startTime ← IO.monoMsNow
    let u ← getU
    let cpvExpr ← buildCPValExpr
    let cpvTy := Expr.const ``CPVal [u]
    let checker ← Meta.withLetDecl `cpval cpvTy cpvExpr fun cpvFVarExpr => do
      let itExpr ← buildImportTableExpr cpvFVarExpr
      let csExpr ← buildChkStepsExpr
      let rInv := Lean.mkApp3 (.const ``Checker [u]) cpvFVarExpr itExpr csExpr
      let rExpr := Lean.mkApp3 (.const ``RTable.mk [])
        (Lean.toExpr (← getRTableTree)) (Lean.toExpr (← getMaxEVarSucc))
        (Lean.toExpr (← getLamEVarTy))
      let .valid lctx t := re
        | throwError "buildFullCheckerExprFor :: {re} is not a `valid` entry"
      let vExpr := Lean.toExpr (← lookupREntryPos! re)
      let eqExpr ← Meta.mkAppM ``Eq.refl #[← Meta.mkAppM ``Option.some #[Lean.toExpr (lctx, t)]]
      let getEntry := Lean.mkApp7 (.const ``RTable.getValidExport_correct [u])
        rExpr cpvExpr vExpr (Lean.toExpr lctx) (Lean.toExpr t) rInv eqExpr
      let getEntry ← Meta.mkLetFVars #[cpvFVarExpr] getEntry
      -- debug
      -- let rt := Lean.mkApp3 (.const ``ChkMap.runFromBeginning [u]) lvalExpr itExpr csExpr
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
  def collectLamBaseTermAtoms (b : LamBaseTerm) : MetaM (HashSet Nat) := do
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
  def collectAtoms (varVal : Array (Expr × LamSort)) :
    LamTerm → MetaM (HashSet Nat × HashSet Nat)
  | .atom n => do
    let .some (_, s) := varVal[n]?
      | throwError "collectAtoms :: Unknown term atom {n}"
    return (collectLamSortAtoms s, HashSet.empty.insert n)
  | .etom _ => throwError "collectAtoms :: Exporting etom is not supported"
  | .base b => do
    return (← collectLamBaseTermAtoms b, HashSet.empty)
  | .bvar _ => pure (HashSet.empty, HashSet.empty)
  | .lam s t => do
    let (typeHs, termHs) ← collectAtoms varVal t
    let sHs := collectLamSortAtoms s
    return (mergeHashSet typeHs sHs, termHs)
  | .app _ t₁ t₂ => do
    let (typeHs₁, termHs₁) ← collectAtoms varVal t₁
    let (typeHs₂, termHs₂) ← collectAtoms varVal t₂
    return (mergeHashSet typeHs₁ typeHs₂, mergeHashSet termHs₁ termHs₂)

end ExportUtils

section

  -- Type of `type atoms` in the language that translates to `LamReif`
  variable (ω : Type) [BEq ω] [Hashable ω]

  -- Type of `term atoms` in the language that translates to `LamReif`
  variable (μ : Type) [BEq μ] [Hashable μ]

  structure TransState where
    typeH2lMap : HashMap ω Nat := {}
    -- This field should be in sync with `LamReif.State.tyVal`
    typeL2hMap : Array ω       := #[]
    termH2lMap : HashMap μ Nat := {}
    -- This field should be in sync with `LamReif.State.varVal`
    termL2hMap : Array μ       := #[]

  abbrev TransM := StateRefT (TransState ω μ) ReifM

  variable {ω : Type} [BEq ω] [Hashable ω]

  variable {μ : Type} [BEq μ] [Hashable μ]

  @[always_inline]
  instance : Monad (TransM ω μ) :=
    let i := inferInstanceAs (Monad (TransM ω μ));
    { pure := i.pure, bind := i.bind }

  instance : Inhabited (TransM ω μ α) where
    default := fun _ => throw default

  #genMonadState (TransM ω μ)

  def transTypeAtom (a : ω) (val : Expr × Level) : TransM ω μ Nat := do
    let typeH2lMap ← getTypeH2lMap
    match typeH2lMap.find? a with
    | .some n => return n
    | .none =>
      let idx := typeH2lMap.size
      setTypeH2lMap (typeH2lMap.insert a idx)
      setTypeL2hMap ((← getTypeL2hMap).push a)
      setTyVal ((← getTyVal).push val)
      setTyVarMap ((← getTyVarMap).insert val.fst idx)
      return idx
  
  -- When translating `Lam` to `Lam` in `Lam2Lam`, make sure that
  --   the `LamSort` in this `val` is already translated.
  def transTermAtom (a : μ) (val : Expr × LamSort) : TransM ω μ Nat := do
    let termH2lMap ← getTermH2lMap
    match termH2lMap.find? a with
    | .some n => return n
    | .none =>
      let idx := termH2lMap.size
      setTermH2lMap (termH2lMap.insert a idx)
      setTermL2hMap ((← getTermL2hMap).push a)
      setVarVal ((← getVarVal).push val)
      setVarMap ((← getVarMap).insert val.fst idx)
      return idx

end

end LamReif

/-
namespace Lam2Lam
open Embedding.Lam LamReif

  -- We're translating `Lam` to `Lam`. We call the first `Lam`
  --   the `high-level` one, and the second `Lam` the `low-level` one.
  
  def transLamSort (ref : State) : LamSort → TransM Nat Nat LamSort
  | .atom n => do
    let (val, _) ← (lookupTyVal! n).run ref
    return .atom (← transTypeAtom n val)
  | .base b => return .base b
  | .func arg res => .func <$> transLamSort ref arg <*> transLamSort ref res
  
  private def transLamBaseTermILErr := "transLamBaseTerm :: Import versions of logical constants should not occur here"

  def transLamBaseTerm (ref : State) : LamBaseTerm → TransM Nat Nat LamBaseTerm
  | .eqI _ => throwError transLamBaseTermILErr
  | .forallEI _ => throwError transLamBaseTermILErr
  | .existEI _ => throwError transLamBaseTermILErr
  | .eq s => .eq <$> transLamSort ref s
  | .forallE s => .forallE <$> transLamSort ref s
  | .existE s => .existE <$> transLamSort ref s
  | b => return b
  
  def transLamTerm (ref : State) : LamTerm → TransM Nat Nat LamTerm
  | .atom n => do
    let ((e, s), _) ← (lookupVarVal! n).run ref
    let s' ← transLamSort ref s
    return .atom (← transTermAtom n (e, s'))
  | .base b => .base <$> transLamBaseTerm ref b
  | .bvar n => return .bvar n
  | .lam s t => .lam <$> transLamSort ref s <*> transLamTerm ref t
  | .app s fn arg => .app <$> transLamSort ref s <*> transLamTerm ref fn <*> transLamTerm ref arg
  
  def transREntry (ref : State) : REntry → TransM Nat Nat REntry
  | .wf lctx s t => do
    return .wf (← lctx.mapM (transLamSort ref)) (← transLamSort ref s) (← transLamTerm ref t)
  | .valid lctx t => do
    return .valid (← lctx.mapM (transLamSort ref)) (← transLamTerm ref t)
  | .nonempty s => .nonempty <$> transLamSort ref s

  -- Collect essential chksteps and assertions from the high-level `lam`
  --   into the low-level `lam` such that the low-level `lam` proves `re`
  partial def collectProofFor (ref : State) (hre : REntry) : TransM Nat Nat Unit := do
    if let .some _ := (← getChkMap).find? hre then
      return
    let (highLvlProof, _) ← (lookupREntryProof! hre).run ref
    match highLvlProof with
    | .inl cs =>
      trace[auto.buildChecker] "Collecting for {hre} by ChkStep {cs}"
      let posCont (n : Nat) : TransM Nat Nat Nat := (do
        let (hre, _) ← (lookupRTable! n).run ref
        collectProofFor ref hre
        lookupREntryPos! (← transREntry ref hre))
      let cs' : ChkStep ← (do
        match cs with
        | .wfOfCheck lctx t => return .wfOfCheck (← lctx.mapM (transLamSort ref)) (← transLamTerm ref t)
        | .wfOfAppend ex pos => return .wfOfAppend (← ex.mapM (transLamSort ref)) (← posCont pos)
        | .wfOfPrepend ex pos => return .wfOfPrepend (← ex.mapM (transLamSort ref)) (← posCont pos)
        | .wfOfHeadBeta pos => return .wfOfHeadBeta (← posCont pos)
        | .wfOfBetaBounded pos bound => return .wfOfBetaBounded (← posCont pos) bound
        | .validOfIntro1F pos => return .validOfIntro1F (← posCont pos)
        | .validOfIntro1H pos => return .validOfIntro1H (← posCont pos)
        | .validOfIntros pos idx => return .validOfIntros (← posCont pos) idx
        | .validOfHeadBeta pos => return .validOfHeadBeta (← posCont pos)
        | .validOfBetaBounded pos bound => return .validOfBetaBounded (← posCont pos) bound
        | .validOfImp p₁₂ p₁ => return .validOfImp (← posCont p₁₂) (← posCont p₁)
        | .validOfImps imp ps => return .validOfImps (← posCont imp) (← ps.mapM posCont)
        | .validOfInstantiate1 pos arg => return .validOfInstantiate1 (← posCont pos) (← transLamTerm ref arg)
        | .validOfInstantiate pos args => return .validOfInstantiate (← posCont pos) (← args.mapM (transLamTerm ref))
        | .validOfInstantiateRev pos args => return .validOfInstantiateRev (← posCont pos) (← args.mapM (transLamTerm ref))
        | .validOfCongrArg pos rw => return .validOfCongrArg (← posCont pos) (← posCont rw)
        | .validOfCongrFun pos rw => return .validOfCongrFun (← posCont pos) (← posCont rw)
        | .validOfCongr pos rwFn rwArg => return .validOfCongr (← posCont pos) (← posCont rwFn) (← posCont rwArg)
        | .validOfCongrArgs pos rws => return .validOfCongrArgs (← posCont pos) (← rws.mapM posCont)
        | .validOfCongrFunN pos rwFn n => return .validOfCongrFunN (← posCont pos) (← posCont rwFn) n
        | .validOfCongrs pos rwFn rwArgs => return .validOfCongrs (← posCont pos) (← posCont rwFn) (← rwArgs.mapM posCont)
        )
      let _ ← newChkStep cs' (← transREntry ref hre)
    | .inr (e, _) =>
      let .valid [] t := hre
        | throwError "collectProofFor :: Unexpected error"
      newAssertion e (← transLamTerm ref t)
  
  -- Delete irrelevant Valuations and ChkSteps, but make sure that
  --   entries in `res` are still provable
  def optimizedStateFor (res : Array REntry) : LamReif.ReifM State := do
    let ref ← get
    let (_, s') ← ((res.foldlM (fun _ re => collectProofFor ref re) ()).run {}).run { u := ref.u }
    return s'

end Lam2Lam
-/
namespace LamReif
open Embedding.Lam

-- Build optimized checker = Optimize state + Build full checker
def buildOptimizedCheckerExprFor (re : REntry) : ReifM Expr := do
  -- let s' ← Lam2Lam.optimizedStateFor #[re]
  -- let (e, _) ← (buildFullCheckerExprFor re).run s'
  -- return e
  buildFullCheckerExprFor re

register_option auto.optimizeCheckerProof : Bool := {
  defValue := true
  descr := "Whether to optimize checker proof"
}

-- Decide whether to optimize based on option
def buildCheckerExprFor (re : REntry) : ReifM Expr := do
  match auto.optimizeCheckerProof.get (← getOptions) with
  | true => buildOptimizedCheckerExprFor re
  | false => buildFullCheckerExprFor re

end Auto.LamReif