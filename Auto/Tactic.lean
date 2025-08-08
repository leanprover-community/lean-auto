import Lean
import Auto.Translation
import Auto.Solver.SMT
import Auto.Solver.TPTP
import Auto.Solver.Native
import Auto.LemDB
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.tactic.printProof
  registerTraceClass `auto.printLemmas
  registerTraceClass `auto.runAuto.printLemmas

namespace Auto

/-- `*` : LCtxHyps, `* <ident>` : Lemma database -/
syntax hintelem := term <|> "*" (ident)?
syntax hints := ("[" hintelem,* "]")?
/-- Specify constants to unfold. `unfolds` Must not contain cyclic dependency -/
syntax unfolds := "u[" ident,* "]"
/-- Specify constants to collect definitional equality for -/
syntax defeqs := "d[" ident,* "]"
syntax uord := atomic(unfolds) <|> defeqs
syntax autoinstr := ("👍" <|> "👎")?
syntax (name := auto) "auto" autoinstr hints (uord)* : tactic
syntax (name := mononative) "mononative" hints (uord)* : tactic
syntax (name := mono) "mono" hints (uord)* : tactic

inductive Instruction where
  | none
  | useSorry

def parseInstr : TSyntax ``autoinstr → TacticM Instruction
| `(autoinstr|) => return .none
| `(autoinstr|👍) => throwError "Your flattery is appreciated 😎"
| `(autoinstr|👎) => do
  logInfo "I'm terribly sorry. A 'sorry' is sent to you as compensation."
  return .useSorry
| _ => throwUnsupportedSyntax

inductive HintElem where
  -- A user-provided term
  | term     : Term → HintElem
  -- Hint database, not yet supported
  | lemdb    : Name → HintElem
  -- `*` adds all hypotheses in the local context
  -- Also, if `[..]` is not supplied to `auto`, all
  --   hypotheses in the local context are
  --   automatically collected.
  | lctxhyps : HintElem
deriving Inhabited, BEq

def parseHintElem : TSyntax ``hintelem → TacticM HintElem
| `(hintelem| *) => return .lctxhyps
| `(hintelem| * $id:ident) => return .lemdb id.getId
| `(hintelem| $t:term) => return .term t
| _ => throwUnsupportedSyntax

structure InputHints where
  terms    : Array Term := #[]
  lemdbs   : Array Name := #[]
  lctxhyps : Bool       := false
deriving Inhabited, BEq

/-- Parse `hints` to an array of `Term`, which is still syntax -/
def parseHints : TSyntax ``hints → TacticM InputHints
| `(hints| [ $[$hs],* ]) => do
  let mut terms := #[]
  let mut lemdbs := #[]
  let mut lctxhyps := false
  let elems ← hs.mapM parseHintElem
  for elem in elems do
    match elem with
    | .term t => terms := terms.push t
    | .lemdb db => lemdbs := lemdbs.push db
    | .lctxhyps => lctxhyps := true
  return ⟨terms, lemdbs, lctxhyps⟩
| `(hints| ) => return ⟨#[], #[], true⟩
| _ => throwUnsupportedSyntax

private def defeqUnfoldErrHint :=
  "Note that auto does not accept defeq/unfold hints which" ++
  "are let-declarations in the local context, because " ++
  "let-declarations are automatically unfolded by auto."

def parseUnfolds : TSyntax ``unfolds → TacticM (Array Prep.ConstUnfoldInfo)
| `(unfolds| u[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "{decl_name%} :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "{decl_name%} :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    Prep.getConstUnfoldInfo name)
| _ => throwUnsupportedSyntax

def parseDefeqs : TSyntax ``defeqs → TacticM (Array Name)
| `(defeqs| d[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "{decl_name%} :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "{decl_name%} :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    return name)
| _ => throwUnsupportedSyntax

def parseUOrD : TSyntax ``uord → TacticM (Array Prep.ConstUnfoldInfo ⊕ Array Name)
| `(uord| $unfolds:unfolds) => Sum.inl <$> parseUnfolds unfolds
| `(uord| $defeqs:defeqs) => Sum.inr <$> parseDefeqs defeqs
| _ => throwUnsupportedSyntax

def parseUOrDs (stxs : Array (TSyntax ``uord)) : TacticM (Array Prep.ConstUnfoldInfo × Array Name) := do
  let mut hasUnfolds := false
  let mut hasDefeqs := false
  let mut unfolds := #[]
  let mut defeqs := #[]
  for stx in stxs do
    match ← parseUOrD stx with
    | .inl u =>
      if hasUnfolds then
        throwError "{decl_name%} :: Duplicated unfold hint"
      hasUnfolds := true
      unfolds := u
    | .inr d =>
      if hasDefeqs then
        throwError "{decl_name%} :: Duplicated defeq hint"
      hasDefeqs := true
      defeqs := defeqs.append d
  return (unfolds, defeqs)

def collectLctxLemmas (lctxhyps : Bool) (ngoalAndBinders : Array FVarId) : MetaM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let fVarIds ← if lctxhyps then pure (← getLCtx).getFVarIds else pure ngoalAndBinders
    let mut lemmas := #[]
    for fVarId in fVarIds do
      let decl ← FVarId.getDecl fVarId
      let type ← instantiateMVars decl.type
      if ← Prep.isNonemptyInhabited type then
        continue
      if ¬ decl.isAuxDecl ∧ (← Meta.isProp type) then
        let name ← fVarId.getUserName
        lemmas := lemmas.push ⟨⟨mkFVar fVarId, type, .leaf s!"lctxLem {name}"⟩, #[]⟩
    return lemmas

def collectUserLemmas (terms : Array Term) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let mut lemmas := #[]
    for term in terms do
      let ⟨⟨proof, type, deriv⟩, params⟩ ← Prep.elabLemma term (.leaf s!"❰{term}❱")
      if ← Prep.isNonemptyInhabited type then
        throwError "invalid lemma {type}, lemmas should not be inhabitation facts"
      else if ← Meta.isProp type then
        lemmas := lemmas.push ⟨⟨proof, ← instantiateMVars type, deriv⟩, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
    return lemmas

def collectHintDBLemmas (names : Array Name) : TacticM (Array Lemma) := do
  let mut hs : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  let mut ret : Array Lemma := #[]
  for name in names do
    let .some db ← findLemDB name
      | throwError "unknown lemma database {name}"
    let lemNames ← db.toHashSet
    for lname in lemNames do
      if !hs.contains lname then
        hs := hs.insert lname
        ret := ret.push (← Lemma.ofConst lname (.leaf s!"lemdb {name} {lname}"))
  return ret

def collectDefeqLemmas (names : Array Name) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let lemmas ← names.flatMapM Prep.elabDefEq
    lemmas.mapM (fun (⟨⟨proof, type, deriv⟩, params⟩ : Lemma) => do
      let type ← instantiateMVars type
      return ⟨⟨proof, type, deriv⟩, params⟩)

def unfoldConstAndPreprocessLemma (unfolds : Array Prep.ConstUnfoldInfo) (lem : Lemma) : MetaM Lemma := do
  let type ← prepReduceExpr (← instantiateMVars lem.type)
  let type := Prep.unfoldConsts unfolds type
  let type ← Core.betaReduce (← instantiateMVars type)
  let lem := {lem with type := type}
  return lem

/--
  We assume that all defeq facts have the form
    `∀ (x₁ : ⋯) ⋯ (xₙ : ⋯), c ... = ...`
  where `c` is a constant. To avoid `whnf` from reducing
  `c`, we call `forallTelescope`, then call `prepReduceExpr`
  on
  · All the arguments of `c`, and
  · The right-hand side of the equation
-/
def unfoldConstAndprepReduceDefeq (unfolds : Array Prep.ConstUnfoldInfo) (lem : Lemma) : MetaM Lemma := do
  let .some type ← prepReduceDefeq (← instantiateMVars lem.type)
    | throwError "unfoldConstAndprepReduceDefeq :: Unrecognized definitional equation {lem.type}"
  let type := Prep.unfoldConsts unfolds type
  let type ← Core.betaReduce (← instantiateMVars type)
  let lem := {lem with type := type}
  return lem

def traceLemmas (traceClass : Name) (pre : String) (lemmas : Array Lemma) : CoreM Unit := do
  let mut cnt : Nat := 0
  let mut mdatas : Array MessageData := #[]
  for lem in lemmas do
    mdatas := mdatas.push m!"\n{cnt}: {lem}"
    cnt := cnt + 1
  if ← isTracingEnabledFor traceClass then
    addTrace traceClass (mdatas.foldl MessageData.compose pre)

def checkDuplicatedFact (terms : Array Term) : TacticM Unit :=
  let n := terms.size
  for i in [0:n] do
    for j in [i+1:n] do
      if terms[i]? == terms[j]? then
        throwError "Auto does not accept duplicated input terms"

def checkDuplicatedLemmaDB (names : Array Name) : TacticM Unit :=
  let n := names.size
  for i in [0:n] do
    for j in [i+1:n] do
      if names[i]? == names[j]? then
        throwError "Auto does not accept duplicated lemma databases"

def collectAllLemmas
  (hintstx : TSyntax ``hints) (uords : Array (TSyntax `Auto.uord)) (ngoalAndBinders : Array FVarId) :
  -- The first `Array Lemma` are `Prop` lemmas
  -- The second `Array Lemma` are Inhabitation facts
  TacticM (Array Lemma × Array Lemma) := do
  let inputHints ← parseHints hintstx
  let (unfoldInfos, defeqNames) ← parseUOrDs uords
  let unfoldInfos ← Prep.topoSortUnfolds unfoldInfos
  let startTime ← IO.monoMsNow
  let lctxLemmas ← collectLctxLemmas inputHints.lctxhyps ngoalAndBinders
  let lctxLemmas ← lctxLemmas.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from local context:" lctxLemmas
  checkDuplicatedFact inputHints.terms
  checkDuplicatedLemmaDB inputHints.lemdbs
  let userLemmas := (← collectUserLemmas inputHints.terms) ++ (← collectHintDBLemmas inputHints.lemdbs)
  let userLemmas ← userLemmas.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from user-provided terms:" userLemmas
  let defeqLemmas ← collectDefeqLemmas defeqNames
  let defeqLemmas ← defeqLemmas.mapM (m:=MetaM) (unfoldConstAndprepReduceDefeq unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from user-provided defeq hints:" defeqLemmas
  trace[auto.tactic] "Preprocessing took {(← IO.monoMsNow) - startTime}ms"
  let inhFacts ← Inhabitation.getInhFactsFromLCtx
  let inhFacts ← inhFacts.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Inhabitation lemmas :" inhFacts
  return (lctxLemmas ++ userLemmas ++ defeqLemmas, inhFacts)

open Embedding.Lam in
def queryTPTP (exportFacts : Array REntry) : LamReif.ReifM (Option Expr × Option (Array REntry)) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "{decl_name%} :: Unexpected error")
  let query ← lam2TH0 lamVarTy lamEVarTy exportLamTerms
  trace[auto.tptp.printQuery] "\n{query}"
  let (proven, tptpProof) ← Solver.TPTP.querySolver query
  if !proven then
    return (.none, .none)
  try
    let proofSteps ← Parser.TPTP.getProof lamVarTy lamEVarTy tptpProof
    for step in proofSteps do
      trace[auto.tptp.printProof] "{step}"
  catch e =>
    trace[auto.tptp.printProof] "TPTP proof reification failed with {e.toMessageData}"
  let unsatCoreIds ← Parser.TPTP.unsatCore tptpProof
  let mut unsatCore := #[]
  for n in unsatCoreIds do
    let .some re := exportFacts[n]?
      | throwError "{decl_name%} :: Index {n} out of range"
    unsatCore := unsatCore.push re
  if (auto.tptp.trust.get (← getOptions)) then
    logWarning "Trusting TPTP solvers. `autoTPTPSorry` is used to discharge the goal."
    return (← Meta.mkAppM ``autoTPTPSorry #[Expr.const ``False []], unsatCore)
  else
    return (.none, unsatCore)

open Embedding.Lam in
def querySMT (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM (Option Expr × Option (Array REntry)) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "{decl_name%} :: Unexpected error")
  let sni : SMT.SMTNamingInfo :=
    {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
  let ((commands, validFacts), state) ← (lamFOL2SMT sni lamVarTy lamEVarTy exportLamTerms exportInds).run
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  if (auto.smt.save.get (← getOptions)) then
    Solver.SMT.saveQuery commands
  let .some (unsatCore, proof) ← Solver.SMT.querySolver commands
    | return (.none, .none)
  let unsatCoreIds ← Solver.SMT.validFactOfUnsatCore unsatCore
  -- **Print valuation of SMT atoms**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for (atomic, name) in state.h2lMap.toArray do
      let e ← SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap atomic
      trace[auto.smt.printValuation] "|{name}| : {e}"
    )
  -- **Print STerms corresponding to `validFacts` in unsatCore**
  for id in unsatCoreIds do
    let .some sterm := validFacts[id]?
      | throwError "{decl_name%} :: Index {id} of `validFacts` out of range"
    trace[auto.smt.unsatCore.smtTerms] "|valid_fact_{id}| : {sterm}"
  -- **Print Lean expressions correesponding to `validFacts` in unsatCore**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for id in unsatCoreIds do
      let .some t := exportLamTerms[id]?
        | throwError "{decl_name%} :: Index {id} of `exportLamTerms` out of range"
      let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
      trace[auto.smt.unsatCore.leanExprs] "|valid_fact_{id}| : {← Core.betaReduce e}"
    )
  -- **Print derivation of unsatCore**
  for id in unsatCoreIds do
    let .some t := exportLamTerms[id]?
      | throwError "{decl_name%} :: Index {id} of `exportLamTerm` out of range"
    let vderiv ← LamReif.collectDerivFor (.valid [] t)
    trace[auto.smt.unsatCore.deriv] "|valid_fact_{id}| : {vderiv}"
  -- **Getting unsatCore**
  let mut unsatCore := #[]
  for id in unsatCoreIds do
    let .some re := exportFacts[id]?
      | throwError "{decl_name%} :: Index {id}  of `exportFacts` out of range"
    unsatCore := unsatCore.push re
  if auto.smt.rconsProof.get (← getOptions) then
    let (_, _) ← Solver.SMT.getSexp proof
    logWarning "Proof reconstruction is not implemented."
  if (auto.smt.trust.get (← getOptions)) then
    logWarning "Trusting SMT solvers. `autoSMTSorry` is used to discharge the goal."
    return (← Meta.mkAppM ``autoSMTSorry #[Expr.const ``False []], unsatCore)
  else
    return (.none, unsatCore)

open LamReif Embedding.Lam in
/--
  Given
  · `nonempties = #[s₀, s₁, ⋯, sᵤ₋₁]`
  · `valids = #[t₀, t₁, ⋯, kₖ₋₁]`
  Invoke prover to get a proof of
    `proof : (∀ (_ : v₀) (_ : v₁) ⋯ (_ : vᵤ₋₁), w₀ → w₁ → ⋯ → wₗ₋₁ → ⊥).interp`
  and returns
  · `fun etoms => proof`
  · `∀ etoms, ∀ (_ : v₀) (_ : v₁) ⋯ (_ : vᵤ₋₁), w₀ → w₁ → ⋯ → wₗ₋₁ → ⊥)`
  · `etoms`
  · `[s₀, s₁, ⋯, sᵤ₋₁]`
  · `[w₀, w₁, ⋯, wₗ₋₁]`
  Here
  · `[v₀, v₁, ⋯, vᵤ₋₁]` is a subsequence of `[s₀, s₁, ⋯, sᵤ₋₁]`
  · `[w₀, w₁, ⋯, wₗ₋₁]` is a subsequence of `[t₀, t₁, ⋯, kₖ₋₁]`
  · `etoms` are all the etoms present in `w₀ → w₁ → ⋯ → wₗ₋₁ → ⊥`

  Note that `MetaState.withTemporaryLCtx` is used to isolate the prover from the
  current local context. This is necessary because `lean-auto` assumes that the prover
  does not use free variables introduced during monomorphization
-/
def callNative_checker
  (nonempties : Array REntry) (valids : Array REntry) (prover : Array Lemma → Array Lemma → MetaM Expr) :
  ReifM (Expr × LamTerm × Array Nat × Array REntry × Array REntry) := do
  let tyVal ← LamReif.getTyVal
  let varVal ← LamReif.getVarVal
  let lamEVarTy ← LamReif.getLamEVarTy
  let nonemptiesWithDTr ← nonempties.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let validsWithDTr ← valids.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  MetaState.runAtMetaM' <| (Lam2DAAF.callNativeWithAtomAsFVar nonemptiesWithDTr validsWithDTr prover).run'
    { tyVal := tyVal, varVal := varVal, lamEVarTy := lamEVarTy }

open LamReif Embedding.Lam in
def callMkMVar_checker
  (nonempties : Array REntry) (valids : Array REntry) :
  ReifM (Array (REntry × DTr) × Array (REntry × DTr) × MVarId × Expr × LamTerm × Nat × Array Nat) := do
  let tyVal ← LamReif.getTyVal
  let varVal ← LamReif.getVarVal
  let lamEVarTy ← LamReif.getLamEVarTy
  let nonemptiesWithDTr ← nonempties.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let validsWithDTr ← valids.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let result ← MetaState.runAtMetaM' <| (Lam2DAAF.callMkMVarWithAtomAsFVar nonemptiesWithDTr validsWithDTr).run'
    { tyVal := tyVal, varVal := varVal, lamEVarTy := lamEVarTy }
  return (nonemptiesWithDTr, validsWithDTr, result)

open LamReif Embedding.Lam in
/--
  Similar in functionality compared to `callNative_checker`, but
  all `valid` entries are supposed to be reified facts (so there should
  be no `etom`s). We invoke the prover to get the same `proof` as
  `callNativeChecker`, but we return a proof of `⊥` by applying `proof`
  to un-reified facts.

  Note that `MetaState.withTemporaryLCtx` is used to isolate the prover from the
  current local context. This is necessary because `lean-auto` assumes that the prover
  does not use free variables introduced during monomorphization
-/
def callNative_direct
  (nonempties : Array REntry) (valids : Array REntry) (prover : Array Lemma → Array Lemma → MetaM Expr) : ReifM Expr := do
  let tyVal ← LamReif.getTyVal
  let varVal ← LamReif.getVarVal
  let lamEVarTy ← LamReif.getLamEVarTy
  let nonemptiesWithDTr ← nonempties.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let validsWithDTr ← valids.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let (proof, _, usedEtoms, usedInhs, usedHyps) ← MetaState.runAtMetaM' <|
    (Lam2DAAF.callNativeWithAtomAsFVar nonemptiesWithDTr validsWithDTr prover).run'
      { tyVal := tyVal, varVal := varVal, lamEVarTy := lamEVarTy }
  if usedEtoms.size != 0 then
    throwError "{decl_name%} :: etoms should not occur here"
  let ss ← usedInhs.mapM (fun re => do
    match ← lookupREntryProof! re with
    | .inhabitation e _ _ => return e
    | .chkStep (.n (.nonemptyOfAtom n)) =>
      match varVal[n]? with
      | .some (e, _) => return e
      | .none => throwError "{decl_name%} :: Unexpected error"
    | _ => throwError "{decl_name%} :: Cannot find external proof of {re}")
  let ts ← usedHyps.mapM (fun re => do
    let .assertion e _ _ ← lookupREntryProof! re
      | throwError "{decl_name%} :: Cannot find external proof of {re}"
    return e)
  return mkAppN proof (ss ++ ts)

open Embedding.Lam in
/--
  If `prover?` is specified, use the specified one.
  Otherwise use the one determined by `Solver.Native.queryNative`
-/
def queryNative
  (declName? : Option Name) (exportFacts exportInhs : Array REntry)
  (prover? : Option (Array Lemma → Array Lemma → MetaM Expr) := .none) : LamReif.ReifM Expr := do
  let (proof, proofLamTerm, usedEtoms, usedInhs, unsatCore) ←
    callNative_checker exportInhs exportFacts (prover?.getD Solver.Native.queryNative)
  LamReif.newAssertion proof (.leaf "by_native::queryNative") proofLamTerm
  let etomInstantiated ← LamReif.validOfInstantiateForall (.valid [] proofLamTerm) (usedEtoms.map .etom)
  let forallElimed ← LamReif.validOfElimForalls etomInstantiated usedInhs
  let contra ← LamReif.validOfImps forallElimed unsatCore
  LamReif.printProofs
  Reif.setDeclName? declName?
  let checker ← LamReif.buildCheckerExprFor contra
  Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]

def rewriteIteCondDecide (lemmas : Array Lemma) : MetaM (Array Lemma) := do
  -- Simplify `ite`
  let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
  -- Simplify `cond`
  let cond_simp_lem ← Lemma.ofConst ``Auto.Bool.cond_simp (.leaf "hw Auto.Bool.cond_simp")
  -- Simplify `decide`
  let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigidNonDep
    lem #[ite_simp_lem, cond_simp_lem, decide_simp_lem])
  return lemmas

/--
  Run `auto`'s preprocessing and monomorphization, then send the
  problem to different solvers
-/
def runAuto
  (declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    trace[auto.tactic.printProof] "{proof}"
    return proof
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM Expr := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- **TPTP invocation and Premise Selection**
    if auto.tptp.get (← getOptions) then
      let (proof, unsatCore) ← queryTPTP exportFacts
      if let .some proof := proof then
        return proof
      let premiseSel? := auto.tptp.premiseSelection.get (← getOptions)
      if premiseSel? then
        if let .some unsatCore := unsatCore then
          exportFacts := unsatCore
    -- **SMT**
    if auto.smt.get (← getOptions) then
      let (proof, _) ← querySMT exportFacts exportInds
      if let .some proof := proof then
        return proof
    -- **Native Prover**
    exportFacts := exportFacts.append (← LamReif.auxLemmas exportFacts)
    if auto.native.get (← getOptions) then
      return ← queryNative declName? exportFacts exportInhs
    throwError "Auto failed to find proof"

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $instr $hints $[$uords]*) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{decl_name%} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let instr ← parseInstr instr
    match instr with
    | .none =>
      let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
      let declName? ← Elab.Term.getDeclName?
      let proof ← runAuto declName? lemmas inhFacts
      absurd.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax

/--
  Run `auto`'s preprocessing and monomorphization to abstract the
  problem into an essentially higher-order problem

  Input
  · `declName?`   : The name of the declaration where you're calling `mono` from
  · `lemmas`      : An array of lemmas that you want to monomorphize. They are meant to
                    be generated by `collectAllLemmas`
  · `inhFacts`    : An array of inhabitation lemmas that you want to monomorphize. They
                    are meant to be generated by `collectAllLemmas`

  Return Value
  · `e : Expr`    : An term of type `False`, which contains one metavariable yet to be assigned
  · `id : MVarId` : The ID of the metavariable in `e` yet to be assigned
  · `derivs : Array (FVarId × DTr)`
                    The `DTr`s associated with (monomorphized) lemmas and inhabitation lemmas
                    in the context of `id`. Using this information you can obtain the
                    correspondence between monomorphized lemmas and the original lemmas
-/
def runMono
  (declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma) :
  MetaM (Expr × MVarId × Array (FVarId × DTr)) :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let ((proof, goalId, derivs), _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM _) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    trace[auto.tactic.printProof] "{proof}"
    return (proof, goalId, derivs)
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM (Expr × MVarId × Array (FVarId × DTr)) := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', _) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'.append (← LamReif.auxLemmas exportFacts)
    -- **Query the dummy prover which creates a metavariable**
    let (nonemptyWithDTrs, validWithDTrs, goalId, proof, proofLamTerm, natoms, etoms) ←
      callMkMVar_checker exportInhs exportFacts
    LamReif.newAssertion proof (.leaf "by_native::queryNative") proofLamTerm
    let etomInstantiated ← LamReif.validOfInstantiateForall (.valid [] proofLamTerm) (etoms.map .etom)
    let forallElimed ← LamReif.validOfElimForalls etomInstantiated exportInhs
    let contra ← LamReif.validOfImps forallElimed exportFacts
    LamReif.printProofs
    Reif.setDeclName? declName?
    let checker ← LamReif.buildCheckerExprFor contra
    let contra ← Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]
    let (_, goalId) ← goalId.introN (natoms + etoms.size)
    let (goalCtx, goalId) ← goalId.introN (exportInhs.size + exportFacts.size)
    let goalCtxWithDeriv := goalCtx.zip ((nonemptyWithDTrs ++ validWithDTrs).map Prod.snd)
    return (contra, goalId, goalCtxWithDeriv)

@[tactic mono]
def evalMono : Tactic
| `(mono | mono $hints $[$uords]*) => withMainContext do
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{decl_name%} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  let (mvarId, _) ← withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let declName? ← Elab.Term.getDeclName?
    let (proof, mvarId) ← runMono declName? lemmas inhFacts
    absurd.assign proof
    return mvarId
  replaceMainGoal [mvarId]
| _ => throwUnsupportedSyntax

/--
  A monomorphization interface that can be invoked by repos dependent on `lean-auto`.
-/
def monoInterface
  (lemmas : Array Lemma) (inhFacts : Array Lemma)
  (prover : Array Lemma → Array Lemma → MetaM Expr) : MetaM Expr := do
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    LamReif.printValuation
    callNative_direct exportInhs exportFacts prover)
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let uvalids ← liftM <| Reif.getFacts
    let uinhs ← liftM <| Reif.getInhTys
    let u ← computeMaxLevel uvalids
    (afterReify uvalids uinhs).run' {u := u})
  return proof

/--
  Run native `prover` with monomorphization and preprocessing of `auto`
-/
def runNativeProverWithAuto
  (declName? : Option Name) (prover : Array Lemma → Array Lemma → MetaM Expr)
  (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr := do
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    LamReif.printValuation
    let (exportFacts, _) ← LamReif.preprocess exportFacts #[]
    return ← queryNative declName? exportFacts exportInhs prover)
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let s ← get
    let u ← computeMaxLevel s.facts
    (afterReify s.facts s.inhTys).run' {u := u})
  trace[auto.tactic] "{decl_name%} :: Found proof of {← Meta.inferType proof}"
  return proof

@[tactic mononative]
def evalMonoNative : Tactic
| `(mononative | mononative $hints $[$uords]*) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{decl_name%} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let proof ← monoInterface lemmas inhFacts Solver.Native.queryNative
    absurd.assign proof
| _ => throwUnsupportedSyntax

end Auto
