import Lean
import Duper.Tactic
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
import Auto.Lib.MetaState
import Auto.Embedding.LamBase
import Auto.Translation.LamReif
open Lean

initialize
  registerTraceClass `auto.lam2D

/-
  Lam2D : Simply-typed lambda calculus to Lean
  The reason we need this is that, sometimes we need external
    provers (e.g. duper) to help us construct proofs.
  Note that external provers does not work with things like
    `GLift.up Prop`. Therefore, we must write functions to interpret
    `λ` terms into `un-lifted` (original) `Lean` expressions.
  Also, an important part of translating to un-lifted Lean
    expressions is to deal with `=, ∀` and `∃`, namely assigning
    the appropriate valuation so that `GLift.down t.interp` matches
    with the type of the un-lifted expression. This is mostly done
    in `LamReif.lean`.
-/

namespace Auto.Lam2D

open LamReif
open Embedding.Lam MetaState

-- All the type atoms and term atoms are interpreted as fvars, which
--   are let-declarations in the local context. We don't want the external
--   prover to unfold these let-declarations, so we add these atoms as
--   non-let free variables into the local context, run the external prover,
--   abstract these free variables after the external prover has
--   finished, and apply the abstracted expression to the value of
--   these atoms to restore the requires expression.
structure State where
  tyVal           : Array (Expr × Level)  
  varVal          : Array (Expr × LamSort)
  fvarsToAbstract : Array (FVarId × Expr)  := #[]
  -- Type atoms that are used in the expressions sent to external prover
  typeAtomFVars   : HashMap Nat FVarId     := {}
  -- Term atoms that are used in the expressions sent to external prover
  termAtomFVars   : HashMap Nat FVarId     := {}

abbrev ExternM := StateRefT State MetaStateM

def ExternM.run (m : ExternM α) (s : State) : MetaStateM (α × State) :=
  StateRefT'.run m s

def ExternM.run' (m : ExternM α) (s : State) : MetaStateM α :=
  StateRefT'.run' m s

#genMonadState ExternM

def withTypeAtomsAsFVar (atoms : Array Nat) : ExternM Unit :=
  for atom in atoms do
    if (← getTypeAtomFVars).contains atom then
      return
    let .some (e, lvl) := (← getTyVal)[atom]?
      | throwError "withTypeAtomAsFVar :: Unknown type atom {atom}"
    let name := "_exTypeAtom" ++ (← mkFreshId).toString
    let newFVarId ← withLocalDecl name .default (.sort lvl) .default
    setFvarsToAbstract ((← getFvarsToAbstract).push (newFVarId, e))
    setTypeAtomFVars ((← getTypeAtomFVars).insert atom newFVarId)

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

def withTermAtomsAsFVar (atoms : Array Nat) : ExternM Unit :=
  for atom in atoms do
    if (← getTermAtomFVars).contains atom then
      return
    let .some (e, s) := (← getVarVal)[atom]?
      | throwError "withTermAtomAsFVar :: Unknown term atom {atom}"
    let sinterp ← interpLamSortAsUnlifted s
    let name := "_exTermAtom" ++ (← mkFreshId).toString
    let newFVarId ← withLocalDecl name .default sinterp .default
    setFvarsToAbstract ((← getFvarsToAbstract).push (newFVarId, e))
    setTermAtomFVars ((← getTermAtomFVars).insert atom newFVarId)

def interpCstrRealAsUnlifted (c : CstrReal) : Expr :=
  let lvl₁ := Level.succ .zero
  let real := Expr.const ``Real []
  match c with
  | .zero => .app (.app (.const ``Zero.zero [lvl₁]) real) real
  | .one => .app (.app (.const ``One.one [lvl₁]) real) real

open Embedding in
def interpLamBaseTermAsUnlifted : LamBaseTerm → ExternM Expr
| .trueE      => return .const ``True []
| .falseE     => return .const ``False []
| .not        => return .const ``Not []
| .and        => return .const ``And []
| .or         => return .const ``Or []
| .imp        => return .const ``ImpF [.zero, .zero]
| .iff        => return .const ``Iff []
| .intVal _   => throwError "Not implemented"
| .realVal c  => return interpCstrRealAsUnlifted c
| .bvVal _    => throwError "Not implemented"
| .eqI _      => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .forallEI _ => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .existEI _  => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .eq s       => do
  return ← runMetaM <| Meta.mkAppOptM ``Eq #[← interpLamSortAsUnlifted s]
| .forallE s  => do
  let ty ← interpLamSortAsUnlifted s
  let sort ← runMetaM <| Expr.normalizeType (← MetaState.inferType ty)
  let Expr.sort lvl := sort
    | throwError "interpLamBaseTermAsUnlifted :: Unexpected sort {sort}"
  return mkAppN (.const ``forallF [lvl, .zero]) #[← interpLamSortAsUnlifted s]
| .existE s  => do
  return ← runMetaM <| Meta.mkAppOptM ``Exists #[← interpLamSortAsUnlifted s]

-- Takes a `t : LamTerm` and produces the `un-lifted` version of `t.interp`.
-- This function should be called after we've called
--   `withTermAtomAsFVar` on all the term atoms occurring in `t`
def interpLamTermAsUnlifted : LamTerm → ExternM Expr
| .atom n => do
  let .some fid := (← getTermAtomFVars).find? n
    | throwError "interpLamTermAsUnlifted :: Cannot find fvarId assigned to term atom {n}"
  return .fvar fid
| .etom _ => throwError "interpLamTermAsUnlifted :: etom is not supported"
| .base b => interpLamBaseTermAsUnlifted b
| .bvar n => return .bvar n
| .lam s t => do
  let sinterp ← interpLamSortAsUnlifted s
  let tinterp ← interpLamTermAsUnlifted t
  return .lam (← mkFreshId) sinterp tinterp .default
| .app _ fn arg => do
  return .app (← interpLamTermAsUnlifted fn) (← interpLamTermAsUnlifted arg)

-- The external prover should only see the local context
--   and an array of Lean expressions, and should not see
--   anything within `ExternM, LamReif.ReifM, ULiftM` or `Reif.ReifM`
def withTranslatedLamTerms (ts : Array LamTerm) : ExternM (Array Expr) := do
  let varVal ← getVarVal
  let hss ← runMetaM <| ts.mapM (fun t => do collectAtoms varVal t)
  let (typeHs, termHs) := hss.foldl
    (fun (typeHs, termHs) (typeHs', termHs') =>
        (mergeHashSet typeHs typeHs', mergeHashSet termHs termHs')) (HashSet.empty, HashSet.empty)
  withTypeAtomsAsFVar typeHs.toArray
  withTermAtomsAsFVar termHs.toArray
  ts.mapM interpLamTermAsUnlifted

-- Given a list of non-dependent types `ty₁, ty₂, ⋯, tyₙ`, add
--   free variables `x₁ : ty₁, x₂ : ty₂, ⋯, xₙ : tyₙ` into local context,
--   and return `#[x₁, x₂, ⋯, xₙ]`
def withHyps (hyps : Array Expr) : ExternM (Array FVarId) := do
  let mut ret := #[]
  for hyp in hyps do
    let name := "_exHyp" ++ (← mkFreshId).toString
    let newFVarId ← withLocalDecl name .default hyp .default
    ret := ret.push newFVarId
  return ret

-- Override the one in duper so that it works for `MetaM`
def Duper.withoutModifyingCoreEnv (m : MetaM α) : MetaM α :=
  try
    let env := (← liftM (get : CoreM Core.State)).env
    let ret ← m
    liftM (modify fun s => {s with env := env} : CoreM Unit)
    return ret
  catch e =>
    throwError e.toMessageData

-- Override the one in duper so that it works for `MetaM`
def Duper.rconsProof (state : Duper.ProverM.State) : MetaM Expr := do
  let some emptyClause := state.emptyClause
    | throwError "rconsProof :: Can't find empty clause in ProverM's state"
  let l := (← Elab.Tactic.collectClauses state emptyClause (#[], Std.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[ProofReconstruction] "Collected clauses: {l}"
  -- First make proof for skolems, then make proof for clauses
  let proof ← Elab.Tactic.mkAllProof state l
  trace[ProofReconstruction] "rconsProof :: Reconstructed proof {proof}"
  return proof

private def callDuperMetaMAction (lemmas : Array (Expr × Expr × Array Name)) : MetaM Expr := do
  let startTime ← IO.monoMsNow
  let state ← Duper.withoutModifyingCoreEnv <| do
    let skSorryName ← Elab.Tactic.addSkolemSorry
    let (_, state) ←
      Duper.ProverM.ProverM.runWithExprs (ctx := {}) (s := {skolemSorryName := skSorryName})
        Duper.ProverM.saturateNoPreprocessingClausification
        lemmas.toList
    return state
  match state.result with
  | .contradiction =>
    IO.println s!"callDuper :: Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
    Duper.rconsProof state
  | .saturated =>
    throwError "callDuper :: Duper saturated"
  | .unknown => throwError "callDuper :: Duper was terminated"

--Meta.mkLambdaFVars (fvars.map (.fvar ·)) expr
private def callDuperExternMAction (ts : Array LamTerm) : ExternM (Array LamTerm × Expr × LamTerm) := do
  let hyps ← withTranslatedLamTerms ts
  for hyp in hyps do
    if !(← runMetaM <| Meta.isTypeCorrect hyp) then
      throwError "callDuper :: Malformed hypothesis {hyp}"
    if !(← runMetaM <| Meta.isProp hyp) then
      throwError "callDuper :: Hypothesis {hyp} is not a proposition"
  let hyps ← runMetaM <| Meta.withTransparency .reducible <| hyps.mapM (fun e => Meta.reduceAll e)
  let hypFvars ← withHyps hyps
  if hyps.size != hypFvars.size then
    throwError "callDuper :: Unexpected error"
  let lemmas : Array (Expr × Expr × Array Name) ← (hyps.zip hypFvars).mapM
    (fun (ty, proof) => do return (ty, ← runMetaM <| Meta.mkAppM ``eq_true #[.fvar proof], #[]))
  -- Note that we're not introducing bound variables into local context
  --   in the above action, so it's reasonable to use `runMetaM`
  let fvarsToAbstract ← getFvarsToAbstract
  runMetaM (do
    let mut expr ← callDuperMetaMAction lemmas
    let mut usedHyps := []
    for (fvar, t) in (hypFvars.zip ts).reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedHyps := t :: usedHyps
    let mut usedVals := []
    for (fvar, val) in fvarsToAbstract.reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedVals := val :: usedVals
    return (⟨usedHyps⟩, mkAppN expr ⟨usedVals⟩, (Array.mk usedHyps).foldr (fun t' t => t'.mkImp t) (.base .falseE)))

-- Given `ts = #[t₀, t₁, ⋯, kₖ₋₁]`, invoke Duper to get a proof 
--   `proof : (s₀ → s₁ → ⋯ → sₗ₋₁ → ⊥).interp`, and returns
--       `([s₀, s₁, ⋯, sₗ₋₁], proof, s₀ → s₁ → ⋯ → sₗ₋₁ → ⊥)`
--   Here `[s₀, s₁, ⋯, sₗ₋₁]` is a subsequence of `[t₀, t₁, ⋯, kₖ₋₁]`
-- It is important to add `Meta.withNewMCtxDepth`, otherwise exprmvars
--   or levelmvars of the current level will be assigned, and we'll
--   get weird proof reconstruction error
def callDuper (ts : Array LamTerm) : ReifM (Array LamTerm × Expr × LamTerm) := Meta.withNewMCtxDepth <| do
  let tyVal ← LamReif.getTyVal
  let varVal ← LamReif.getVarVal
  runAtMetaM' <| (callDuperExternMAction ts).run' { tyVal := tyVal, varVal := varVal }

end Auto.Lam2D