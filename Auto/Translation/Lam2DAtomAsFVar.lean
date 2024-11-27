import Lean
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
import Auto.Lib.MetaState
import Auto.Lib.ToExprExtra
import Auto.Embedding.LamChecker
import Auto.Translation.Assumptions
import Auto.Translation.LamUtils
open Lean

initialize
  registerTraceClass `auto.lam2D
  registerTraceClass `auto.lam2D.printInhs
  registerTraceClass `auto.lam2D.printHyps
  registerTraceClass `auto.lam2D.printProof

/-
  Lam2D : Simply-typed lambda calculus to Lean expression
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

namespace Auto.Lam2DAAF

open Embedding.Lam LamExportUtils MetaState

/--
  All the type atoms and term atoms are interpreted as fvars, which
    are let-declarations in the local context. We don't want the external
    prover to unfold these let-declarations, so we add these atoms as
    non-let free variables into the local context, run the external prover,
    abstract these free variables after the external prover has
    finished, and apply the abstracted expression to the value of
    these atoms to restore the requires expression.
-/
structure State where
  tyVal           : Array (Expr × Level)
  varVal          : Array (Expr × LamSort)
  lamEVarTy       : Array LamSort
  -- Type atoms and term atoms to be abstracted
  atomsToAbstract : Array (FVarId × Expr) := #[]
  -- Etoms to be abstracted
  etomsToAbstract : Array (FVarId × Nat)  := #[]
  -- Type atoms that are used in the expressions sent to external prover
  typeAtomFVars   : Std.HashMap Nat Expr      := {}
  -- Term atoms that are used in the expressions sent to external prover
  termAtomFVars   : Std.HashMap Nat Expr      := {}
  -- Etoms that are used in the expression sent to external prover
  etomFVars       : Std.HashMap Nat Expr      := {}

abbrev ExternM := StateRefT State MetaStateM

def ExternM.run (m : ExternM α) (s : State) : MetaStateM (α × State) :=
  StateRefT'.run m s

def ExternM.run' (m : ExternM α) (s : State) : MetaStateM α :=
  StateRefT'.run' m s

#genMonadState ExternM

def withTypeAtomsAsFVar (atoms : Array Nat) : ExternM Unit :=
  for atom in atoms do
    if (← getTypeAtomFVars).contains atom then
      continue
    let .some (e, lvl) := (← getTyVal)[atom]?
      | throwError "{decl_name%} :: Unknown type atom {atom}"
    let name := (`_exTy).appendIndexAfter (← getTypeAtomFVars).size
    let newFVarId ← withLocalDecl name .default (.sort lvl) .default
    setAtomsToAbstract ((← getAtomsToAbstract).push (newFVarId, e))
    setTypeAtomFVars ((← getTypeAtomFVars).insert atom (.fvar newFVarId))

def withTermAtomsAsFVar (atoms : Array Nat) : ExternM Unit :=
  for atom in atoms do
    if (← getTermAtomFVars).contains atom then
      continue
    let .some (e, s) := (← getVarVal)[atom]?
      | throwError "{decl_name%} :: Unknown term atom {atom}"
    let sinterp ← Lam2D.interpLamSortAsUnlifted (← getTypeAtomFVars) s
    let name := (`e!).appendIndexAfter (← getTermAtomFVars).size
    let newFVarId ← withLocalDecl name .default sinterp .default
    setAtomsToAbstract ((← getAtomsToAbstract).push (newFVarId, e))
    setTermAtomFVars ((← getTermAtomFVars).insert atom (.fvar newFVarId))

def withEtomsAsFVar (etoms : Array Nat) : ExternM Unit :=
  for etom in etoms do
    if (← getEtomFVars).contains etom then
      return
    let .some s := (← getLamEVarTy)[etom]?
      | throwError "{decl_name%} :: Unknown etom {etom}"
    let sinterp ← Lam2D.interpLamSortAsUnlifted (← getTypeAtomFVars) s
    let name := (`e?).appendIndexAfter (← getEtomFVars).size
    let newFVarId ← withLocalDecl name .default sinterp .default
    setEtomsToAbstract ((← getEtomsToAbstract).push (newFVarId, etom))
    setEtomFVars ((← getEtomFVars).insert etom (.fvar newFVarId))

def withTranslatedLamSorts (ss : Array LamSort) : ExternM (Array Expr) := do
  let typeHs := collectLamSortsAtoms ss
  withTypeAtomsAsFVar typeHs.toArray
  ss.mapM (m:=CoreM) (Lam2D.interpLamSortAsUnlifted (← getTypeAtomFVars))

/--
  The external prover should only see the local context
    and an array of Lean expressions, and should not see
    anything within `ExternM, LamReif.ReifM, ULiftM` or `Reif.ReifM`
-/
def withTranslatedLamTerms (ts : Array LamTerm) : ExternM (Array Expr) := do
  let varVal ← getVarVal
  let lamEVarTy ← getLamEVarTy
  let (typeHs, termHs, etomHs) ← runMetaM <| collectLamTermsAtoms (varVal.map Prod.snd) lamEVarTy ts
  withTypeAtomsAsFVar typeHs.toArray
  withTermAtomsAsFVar termHs.toArray
  withEtomsAsFVar etomHs.toArray
  MetaState.runMetaM <| ts.mapM (Lam2D.interpLamTermAsUnlifted (← getTypeAtomFVars) (← getTermAtomFVars) (← getEtomFVars) 0)

/--
  Given a list of non-dependent types `ty₁, ty₂, ⋯, tyₙ`, add
    free variables `x₁ : ty₁, x₂ : ty₂, ⋯, xₙ : tyₙ` into local context,
    and return `#[x₁, x₂, ⋯, xₙ]`
-/
def withHyps (hyps : Array Expr) : ExternM (Array FVarId) := do
  let mut ret := #[]
  for hyp in hyps do
    let name := Name.mkSimple ("_exHyp" ++ (← mkFreshId).toString)
    let newFVarId ← withLocalDecl name .default hyp .default
    ret := ret.push newFVarId
  return ret

/--
  Calling external provere with type atoms, atoms, etoms, inhabitation facts
  and lemmas as free variables

  Note that `MetaState.withTemporaryLCtx` is used to isolate the prover from the
  current local context. This is necessary because `lean-auto` assumes that the prover
  does not use free variables introduced during monomorphization
-/
def callNativeWithAtomAsFVar
  (nonemptiesWithDTr : Array (REntry × DTr)) (validsWithDTr : Array (REntry × DTr)) (prover : Array Lemma → Array Lemma → MetaM Expr) :
  ExternM (Expr × LamTerm × Array Nat × Array REntry × Array REntry) := MetaState.withTemporaryLCtx {} {} <| do
  let ss ← nonemptiesWithDTr.mapM (fun (re, _) => do
    match re with
    | .nonempty s => return s
    | _ => throwError "{decl_name%} :: {re} is not a `nonempty` entry")
  let inhs ← withTranslatedLamSorts ss
  for inh in inhs do
    trace[auto.lam2D.printInhs] "{inh}"
  let inhFVars ← withHyps inhs
  let inhDTrs := nonemptiesWithDTr.map Prod.snd
  let valids := validsWithDTr.map Prod.fst
  let hypDTrs := validsWithDTr.map Prod.snd
  let ts ← valids.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "{decl_name%} :: {re} is not a `valid` entry")
  let hyps ← withTranslatedLamTerms ts
  for hyp in hyps do
    if !(← runMetaM <| Meta.isTypeCorrect hyp) then
      throwError "{decl_name%} :: Malformed hypothesis {hyp}"
    if !(← runMetaM <| Meta.isProp hyp) then
      throwError "{decl_name%} :: Hypothesis {hyp} is not a proposition"
    trace[auto.lam2D.printHyps] "{hyp}"
  let hyps ← runMetaM <| hyps.mapM (fun e => Core.betaReduce e)
  let hypFvars ← withHyps hyps
  let lemmas : Array Lemma := ((hyps.zip hypFvars).zip hypDTrs).map
    (fun ((ty, proof), dtr) => ⟨⟨.fvar proof, ty, dtr⟩, #[]⟩)
  let hypLemmas : Array Lemma := ((inhs.zip inhFVars).zip inhDTrs).map
    (fun ((ty, proof), dtr) => ⟨⟨.fvar proof, ty, dtr⟩, #[]⟩)
  -- Note that we're not introducing bound variables into local context
  --   in the above action, so it's reasonable to use `runMetaM`
  let atomsToAbstract ← getAtomsToAbstract
  let etomsToAbstract ← getEtomsToAbstract
  let lamEVarTy ← getLamEVarTy
  runMetaM (do
    -- It is important to add `Meta.withNewMCtxDepth`, otherwise exprmvars
    --   or levelmvars of the current level will be assigned, and we'll
    --   get weird proof reconstruction error
    let mut expr ← Meta.withNewMCtxDepth <| prover lemmas hypLemmas
    let mut usedHyps := []
    for (fvar, re_t) in (hypFvars.zip (valids.zip ts)).reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedHyps := re_t :: usedHyps
    let mut usedInhs := []
    for (fvar, re_s) in (inhFVars.zip ((nonemptiesWithDTr.map Prod.fst).zip ss)).reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedInhs := re_s :: usedInhs
    let mut usedEtoms := []
    for (fvar, eidx) in etomsToAbstract do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedEtoms := eidx :: usedEtoms
    let mut usedVals := []
    for (fvar, val) in atomsToAbstract.reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedVals := val :: usedVals
    let proofLamTermPre := (Array.mk usedHyps).foldr (fun (_, t') t => t'.mkImp t) (.base .falseE)
    let proofLamTermPre := (Array.mk usedInhs).foldr (fun (_, s) t => t.mkForallEF s) proofLamTermPre
    let proofLamTermPre := proofLamTermPre.abstractsRevImp ((Array.mk usedEtoms).map LamTerm.etom)
    let usedEtomTys ← usedEtoms.mapM (fun etom => do
      let .some ty := lamEVarTy[etom]?
        | throwError "{decl_name%} :: Unexpected error"
      return ty)
    let proof := mkAppN expr ⟨usedVals⟩
    let proofLamTerm := usedEtomTys.foldr (fun s cur => LamTerm.mkForallEF s cur) proofLamTermPre
    trace[auto.lam2D.printProof] "Found proof of {proofLamTerm}\n\n{proof}"
    return (proof, proofLamTerm, ⟨usedEtoms⟩, ⟨usedInhs.map Prod.fst⟩, ⟨usedHyps.map Prod.fst⟩))

end Auto.Lam2DAAF
