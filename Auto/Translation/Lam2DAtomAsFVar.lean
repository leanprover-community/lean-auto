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

namespace Auto.Lam2AAF

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
  atomsToAbstract : Array (FVarId × Expr)  := #[]
  -- Etoms to be abstracted
  etomsToAbstract : Array (FVarId × Nat)   := #[]
  -- Type atoms that are used in the expressions sent to external prover
  typeAtomFVars   : HashMap Nat FVarId     := {}
  -- Term atoms that are used in the expressions sent to external prover
  termAtomFVars   : HashMap Nat FVarId     := {}
  -- Etoms that are used in the expression sent to external prover
  etomFVars       : HashMap Nat FVarId     := {}

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
      | throwError "withTypeAtomAsFVar :: Unknown type atom {atom}"
    let name := (`_exTy).appendIndexAfter (← getTypeAtomFVars).size
    let newFVarId ← withLocalDecl name .default (.sort lvl) .default
    setAtomsToAbstract ((← getAtomsToAbstract).push (newFVarId, e))
    setTypeAtomFVars ((← getTypeAtomFVars).insert atom newFVarId)

/--
  Takes a `s : LamSort` and produces the `un-lifted` version of `s.interp`
    (note that `s.interp` is lifted)
  This function should be called after we've called
    `withTypeAtomAsFVar` on all the type atoms occurring in `s`
-/
def interpLamSortAsUnlifted : LamSort → ExternM Expr
| .atom n => do
  let .some fid := (← getTypeAtomFVars).find? n
    | throwError "interpLamSortAsUnlifted :: Cannot find fvarId assigned to type atom {n}"
  return .fvar fid
| .base b => return Lam2D.interpLamBaseSortAsUnlifted b
| .func s₁ s₂ => do
  return .forallE `_ (← interpLamSortAsUnlifted s₁) (← interpLamSortAsUnlifted s₂) .default

def withTermAtomsAsFVar (atoms : Array Nat) : ExternM Unit :=
  for atom in atoms do
    if (← getTermAtomFVars).contains atom then
      continue
    let .some (e, s) := (← getVarVal)[atom]?
      | throwError "withTermAtomAsFVar :: Unknown term atom {atom}"
    let sinterp ← interpLamSortAsUnlifted s
    let name := (`e!).appendIndexAfter (← getTermAtomFVars).size
    let newFVarId ← withLocalDecl name .default sinterp .default
    setAtomsToAbstract ((← getAtomsToAbstract).push (newFVarId, e))
    setTermAtomFVars ((← getTermAtomFVars).insert atom newFVarId)

def withEtomsAsFVar (etoms : Array Nat) : ExternM Unit :=
  for etom in etoms do
    if (← getEtomFVars).contains etom then
      return
    let .some s := (← getLamEVarTy)[etom]?
      | throwError "withEtomAsFVar :: Unknown etom {etom}"
    let sinterp ← interpLamSortAsUnlifted s
    let name := (`e?).appendIndexAfter (← getEtomFVars).size
    let newFVarId ← withLocalDecl name .default sinterp .default
    setEtomsToAbstract ((← getEtomsToAbstract).push (newFVarId, etom))
    setEtomFVars ((← getEtomFVars).insert etom newFVarId)

open Embedding in
def interpOtherConstAsUnlifted (oc : OtherConst) : ExternM Expr := do
  let .some (.defnInfo constIdVal) := (← getEnv).find? ``constId
    | throwError "interpOtherConstAsUnlifted :: Unexpected error"
  let constIdExpr := fun params => constIdVal.value.instantiateLevelParams constIdVal.levelParams params
  match oc with
  | .smtAttr1T _ sattr sterm => do
    let tyattr ← interpLamSortAsUnlifted sattr
    let sortattr ← runMetaM <| Expr.normalizeType (← MetaState.inferType tyattr)
    let Expr.sort lvlattr := sortattr
      | throwError "interpOtherConstAsUnlifted :: Unexpected sort {sortattr}"
    let tyterm ← interpLamSortAsUnlifted sterm
    let sortterm ← runMetaM <| Expr.normalizeType (← MetaState.inferType tyterm)
    let Expr.sort lvlterm := sortterm
      | throwError "interpOtherConstAsUnlifted :: Unexpected sort {sortterm}"
    return Lean.mkApp2 (constIdExpr [lvlattr, lvlterm]) tyattr tyterm

open Embedding in
def interpLamBaseTermAsUnlifted : LamBaseTerm → ExternM Expr
| .pcst pc    => Lam2D.interpPropConstAsUnlifted pc
| .bcst bc    => return Lam2D.interpBoolConstAsUnlifted bc
| .ncst nc    => return Lam2D.interpNatConstAsUnlifted nc
| .icst ic    => return Lam2D.interpIntConstAsUnlifted ic
| .scst sc    => return Lam2D.interpStringConstAsUnlifted sc
| .bvcst bvc  => return Lam2D.interpBitVecConstAsUnlifted bvc
| .ocst oc    => interpOtherConstAsUnlifted oc
| .eqI _      => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .forallEI _ => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .existEI _  => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .iteI _     => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .eq s       => do
  return ← runMetaM <| Meta.mkAppOptM ``Eq #[← interpLamSortAsUnlifted s]
| .forallE s  => do
  let ty ← interpLamSortAsUnlifted s
  let sort ← runMetaM <| Expr.normalizeType (← MetaState.inferType ty)
  let Expr.sort lvl := sort
    | throwError "interpLamBaseTermAsUnlifted :: Unexpected sort {sort}"
  let .some (.defnInfo forallVal) := (← getEnv).find? ``forallF
    | throwError "interpLamBaseTermAsUnlifted :: Unexpected error"
  let forallFExpr := forallVal.value.instantiateLevelParams forallVal.levelParams [lvl, .zero]
  return mkAppN forallFExpr #[← interpLamSortAsUnlifted s]
| .existE s  => do
  return ← runMetaM <| Meta.mkAppOptM ``Exists #[← interpLamSortAsUnlifted s]
| .ite s     => do
  return ← runMetaM <| Meta.mkAppOptM ``Bool.ite' #[← interpLamSortAsUnlifted s]

/--
  Takes a `t : LamTerm` and produces the `un-lifted` version of `t.interp`.
  This function should be called after we've called
    `withTermAtomAsFVar` on all the term atoms occurring in `t`
  `lctx` is for pretty printing
-/
def interpLamTermAsUnlifted (lctx : Nat) : LamTerm → ExternM Expr
| .atom n => do
  let .some fid := (← getTermAtomFVars).find? n
    | throwError "interpLamTermAsUnlifted :: Cannot find fvarId assigned to term atom {n}"
  return .fvar fid
| .etom n => do
  let .some fid := (← getEtomFVars).find? n
    | throwError "interpLamSortAsUnlifted :: Cannot find fvarId assigned to etom {n}"
  return .fvar fid
| .base b => interpLamBaseTermAsUnlifted b
| .bvar n => return .bvar n
| .lam s t => do
  let sinterp ← interpLamSortAsUnlifted s
  let tinterp ← interpLamTermAsUnlifted lctx.succ t
  let name := (`eb!).appendIndexAfter lctx
  return .lam name sinterp tinterp .default
| .app _ fn arg => do
  return .app (← interpLamTermAsUnlifted lctx fn) (← interpLamTermAsUnlifted lctx arg)

def withTranslatedLamSorts (ss : Array LamSort) : ExternM (Array Expr) := do
  let typeHs := collectLamSortsAtoms ss
  withTypeAtomsAsFVar typeHs.toArray
  ss.mapM interpLamSortAsUnlifted

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
  ts.mapM (interpLamTermAsUnlifted 0)

/--
  Given a list of non-dependent types `ty₁, ty₂, ⋯, tyₙ`, add
    free variables `x₁ : ty₁, x₂ : ty₂, ⋯, xₙ : tyₙ` into local context,
    and return `#[x₁, x₂, ⋯, xₙ]`
-/
def withHyps (hyps : Array Expr) : ExternM (Array FVarId) := do
  let mut ret := #[]
  for hyp in hyps do
    let name := "_exHyp" ++ (← mkFreshId).toString
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
  (nonempties : Array REntry) (validsWithDTr : Array (REntry × DTr)) (prover : Array Lemma → MetaM Expr) :
  ExternM (Expr × LamTerm × Array Nat × Array REntry × Array REntry) := MetaState.withTemporaryLCtx {} {} <| do
  let ss ← nonempties.mapM (fun re => do
    match re with
    | .nonempty s => return s
    | _ => throwError "callNativeWithAtomAsFVar :: {re} is not a `nonempty` entry")
  let inhs ← withTranslatedLamSorts ss
  for inh in inhs do
    trace[auto.printInhs] "{inh}"
  let inhFVars ← withHyps inhs
  let valids := validsWithDTr.map Prod.fst
  let hypDTrs := validsWithDTr.map Prod.snd
  let ts ← valids.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "callNativeWithAtomAsFVar :: {re} is not a `valid` entry")
  let hyps ← withTranslatedLamTerms ts
  for hyp in hyps do
    if !(← runMetaM <| Meta.isTypeCorrect hyp) then
      throwError "callNative :: Malformed hypothesis {hyp}"
    if !(← runMetaM <| Meta.isProp hyp) then
      throwError "callNative :: Hypothesis {hyp} is not a proposition"
    trace[auto.printHyps] "{hyp}"
  let hyps ← runMetaM <| hyps.mapM (fun e => Core.betaReduce e)
  let hypFvars ← withHyps hyps
  let lemmas : Array Lemma := ((hyps.zip hypFvars).zip hypDTrs).map
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
    let mut expr ← Meta.withNewMCtxDepth <| prover lemmas
    let mut usedHyps := []
    for (fvar, re_t) in (hypFvars.zip (valids.zip ts)).reverse do
      if expr.hasAnyFVar (· == fvar) then
        expr ← Meta.mkLambdaFVars #[.fvar fvar] expr
        usedHyps := re_t :: usedHyps
    let mut usedInhs := []
    for (fvar, re_s) in (inhFVars.zip (nonempties.zip ss)).reverse do
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
        | throwError "callNative :: Unexpected error"
      return ty)
    let proof := mkAppN expr ⟨usedVals⟩
    let proofLamTerm := usedEtomTys.foldr (fun s cur => LamTerm.mkForallEF s cur) proofLamTermPre
    trace[auto.lam2D.printProof] "Found proof of {proofLamTerm}\n\n{proof}"
    return (proof, proofLamTerm, ⟨usedEtoms⟩, ⟨usedInhs.map Prod.fst⟩, ⟨usedHyps.map Prod.fst⟩))

end Auto.Lam2AAF