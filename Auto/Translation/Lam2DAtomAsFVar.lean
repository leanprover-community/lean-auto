module

public import Lean
public import Auto.Lib.ExprExtra
public import Auto.Lib.MetaExtra
public import Auto.Lib.MetaState
public import Auto.Lib.ToExprExtra
public import Auto.EmbedLam.LamChecker
public import Auto.Translation.Assumptions
public import Auto.Translation.LamUtils
public import Auto.Translation.LamLater
public import Auto.Solver.Native

public section

open Lean

initialize
  registerTraceClass `auto.lam2D
  registerTraceClass `auto.lam2D.printInhs
  registerTraceClass `auto.lam2D.printHyps
  registerTraceClass `auto.lam2D.printLaterSpecs
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
  -- Recognized later-declared types, with the proofs of the characterizations of their constants
  laterInfo       : LamLater.LaterInfo        := {}

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

def withAll
  (nonemptiesWithDTr : Array (REntry × DTr))
  (validsWithDTr : Array (REntry × DTr)) :
  ExternM (Array LamSort × Array LamTerm × Array Lemma × Array Lemma) := do
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
  let inhLemmas : Array Lemma := ((inhs.zip inhFVars).zip inhDTrs).map
    (fun ((ty, proof), dtr) => ⟨⟨.fvar proof, ty, dtr⟩, #[]⟩)
  return (ss, ts, lemmas, inhLemmas)

/--
  Add the characterizations of later-declared types into the local context as free
    variables. The characterizations of the core constants are sent to the external
    prover as proofs of the structures they come from, e.g. `RealInterpUnlifted.CoreSpec`
    (see `LaterInfo.coreSpecOfConj`). Returns the `λ` terms of the characterizations
    and their free variables
-/
def withLaterSpecs (laterSpecsWithDTr : LaterSpecInterface (REntry × DTr)) :
  ExternM (Array LamTerm × Array FVarId × LaterSpecInterface Lemma) := do
  let laterInfo ← getLaterInfo
  let laterSpecs ← laterSpecsWithDTr.withSteps.mapM (fun (fs, re, dtr) => do
    let .valid [] t := re
      | throwError "{decl_name%} :: {re} is not a `valid` entry"
    let #[spec] ← withTranslatedLamTerms #[t]
      | throwError "{decl_name%} :: Unexpected error"
    if !(← runMetaM <| Meta.isTypeCorrect spec) then
      throwError "{decl_name%} :: Malformed characterization {spec}"
    let spec ← runMetaM <| Core.betaReduce spec
    trace[auto.lam2D.printLaterSpecs] "{spec}"
    let #[fvar] ← withHyps #[spec]
      | throwError "{decl_name%} :: Unexpected error"
    let proof ← match fs with
      | .realCoreSpec => runMetaM <| laterInfo.coreSpecOfConj .real (.fvar fvar)
      | .complexCoreSpec => runMetaM <| laterInfo.coreSpecOfConj .complex (.fvar fvar)
      | _ => pure (.fvar fvar)
    if !(← runMetaM <| Meta.isTypeCorrect proof) then
      throwError "{decl_name%} :: Malformed proof {proof} of characterization {spec}"
    let lem : Lemma := ⟨⟨proof, ← runMetaM <| Meta.inferType proof, dtr⟩, #[]⟩
    return (t, fvar, lem))
  let entries := laterSpecs.toArray
  return (entries.map (·.1), entries.map (·.2.1), laterSpecs.map (·.2.2))

/--
  Calling external prover with type atoms, atoms, etoms, inhabitation facts
  and lemmas as free variables. Each characterization of later-declared types
  in `facts.laterSpecs` is a free variable too, and is treated as a lemma
  when it is used

  Note that `MetaState.withTemporaryLCtx` is used to isolate the prover from the
  current local context. This is necessary because `lean-auto` assumes that the prover
  does not use free variables introduced during monomorphization
-/
def callNativeWithAtomAsFVar
  (facts : NativeInterface (REntry × DTr)) (prover : NativeInterface Lemma → MetaM Expr) :
  ExternM (Expr × LamTerm × Array Nat × Array REntry × Array REntry) := MetaState.withTemporaryLCtx {} {} <| do
  let (ss, ts, lemmas, inhLemmas) ← withAll facts.nonempties facts.valids
  let (specTs, specFVars, laterSpecs) ← withLaterSpecs facts.laterSpecs
  let getFid (lem : Lemma) : ExternM FVarId := do
    match lem.proof with
    | .fvar id => return id
    | _ => throwError "{decl_name%} :: Unexpected error"
  let hypFVars ← lemmas.mapM getFid
  let inhFVars ← inhLemmas.mapM getFid
  -- Note that we're not introducing bound variables into local context
  --   in the above action, so it's reasonable to use `runMetaM`
  let atomsToAbstract ← getAtomsToAbstract
  let etomsToAbstract ← getEtomsToAbstract
  let lamEVarTy ← getLamEVarTy
  runMetaM (do
    -- It is important to add `Meta.withNewMCtxDepth`, otherwise exprmvars
    --   or levelmvars of the current level will be assigned, and we'll
    --   get weird proof reconstruction error
    let mut expr ← Meta.withNewMCtxDepth <| prover { valids := lemmas, nonempties := inhLemmas, laterSpecs }
    let mut usedHyps := []
    let hypREntries := facts.valids.map Prod.fst ++ facts.laterSpecs.toArray.map Prod.fst
    let hyps := (hypFVars ++ specFVars).zip (hypREntries.zip (ts ++ specTs))
    for (fvar, re_t) in hyps.reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedHyps := re_t :: usedHyps
    let mut usedInhs := []
    for (fvar, re_s) in (inhFVars.zip ((facts.nonempties.map Prod.fst).zip ss)).reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedInhs := re_s :: usedInhs
    let mut usedEtoms := []
    for (fvar, eidx) in etomsToAbstract.reverse do
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
    let proofLamTerm := usedEtomTys.foldr (fun s cur => LamTerm.mkForallEF s cur) proofLamTermPre
    let proof := mkAppN expr ⟨usedVals⟩
    trace[auto.lam2D.printProof] "Found proof of {proofLamTerm}\n\n{proof}"
    return (proof, proofLamTerm, ⟨usedEtoms⟩, ⟨usedInhs.map Prod.fst⟩, ⟨usedHyps.map Prod.fst⟩))

@[inherit_doc callNativeWithAtomAsFVar]
def callMkMVarWithAtomAsFVar
  (nonemptiesWithDTr : Array (REntry × DTr)) (validsWithDTr : Array (REntry × DTr)) :
  ExternM (MVarId × Expr × LamTerm × Array Expr × Array Nat) := MetaState.withTemporaryLCtx {} {} <| do
  let (ss, ts, lemmas, inhLemmas) ← withAll nonemptiesWithDTr validsWithDTr
  let getFid (lem : Lemma) : ExternM FVarId := do
    match lem.proof with
    | .fvar id => return id
    | _ => throwError "{decl_name%} :: Unexpected error"
  let hypFVars ← lemmas.mapM getFid
  let inhFVars ← inhLemmas.mapM getFid
  -- Note that we're not introducing bound variables into local context
  --   in the above action, so it's reasonable to use `runMetaM`
  let atomsToAbstract ← getAtomsToAbstract
  let etomsToAbstract ← getEtomsToAbstract
  let lamEVarTy ← getLamEVarTy
  let allFVars :=
    atomsToAbstract.map Prod.fst ++ etomsToAbstract.map Prod.fst ++
    inhFVars ++ hypFVars
  let proofLamTermPre := ts.foldr (fun t' t => t'.mkImp t) (.base .falseE)
  let proofLamTermPre := ss.foldr (fun s t => t.mkForallEF s) proofLamTermPre
  let proofLamTermPre := proofLamTermPre.abstractsRevImp (etomsToAbstract.map (fun (_, id) => .etom id))
  let usedEtomTys ← etomsToAbstract.mapM (fun (_, etom) => do
    let .some ty := lamEVarTy[etom]?
      | throwError "{decl_name%} :: Unexpected error"
    return ty)
  let proofLamTerm := usedEtomTys.foldr (fun s cur => LamTerm.mkForallEF s cur) proofLamTermPre
  let (proof, goalId) ← runMetaM (do
    let .mvar mProofId ← Meta.mkFreshExprMVar (mkConst ``False)
      | throwError "{decl_name%} :: Unexpected error"
    let (fvars, goalId) ← mProofId.revert allFVars (preserveOrder:=true)
    let proof ← Meta.mkLambdaFVars (fvars.map Expr.fvar) (← instantiateMVars (.mvar mProofId))
    let proof ← Meta.instantiateLambda proof (atomsToAbstract.map Prod.snd)
    return (proof, goalId))
  return (goalId, proof, proofLamTerm, atomsToAbstract.map Prod.snd, etomsToAbstract.map Prod.snd)

end Auto.Lam2DAAF
