import Lean
import Auto.Translation
import Auto.Solver.SMT
import Auto.Solver.TPTP
import Auto.Solver.Native
import Auto.LemDB
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.printLemmas

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
syntax (name := intromono) "intromono" hints (uord)* : tactic

inductive Instruction where
  | none
  | useSorry

def parseInstr : TSyntax ``Auto.autoinstr → TacticM Instruction
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
      | throwError "parseUnfolds :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "parseUnfolds :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    Prep.getConstUnfoldInfo name)
| _ => throwUnsupportedSyntax

def parseDefeqs : TSyntax ``defeqs → TacticM (Array Name)
| `(defeqs| d[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "parseDefeqs :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "parseDefeqs :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
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
        throwError "Auto :: Duplicated unfold hint"
      hasUnfolds := true
      unfolds := u
    | .inr d =>
      if hasDefeqs then
        throwError "Auto :: Duplicated defeq hint"
      hasDefeqs := true
      defeqs := defeqs.append d
  return (unfolds, defeqs)

def collectLctxLemmas (lctxhyps : Bool) (ngoalAndBinders : Array FVarId) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let fVarIds := (if lctxhyps then (← getLCtx).getFVarIds else ngoalAndBinders)
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
  let mut hs : HashSet Name := HashSet.empty
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
    let lemmas ← names.concatMapM Prep.elabDefEq
    lemmas.mapM (fun (⟨⟨proof, type, deriv⟩, params⟩ : Lemma) => do
      let type ← instantiateMVars type
      return ⟨⟨proof, type, deriv⟩, params⟩)

def unfoldConstAndPreprocessLemma (unfolds : Array Prep.ConstUnfoldInfo) (lem : Lemma) : MetaM Lemma := do
  let type ← prepReduceExpr (← instantiateMVars lem.type)
  let type := Prep.unfoldConsts unfolds type
  let type ← Core.betaReduce (← instantiateMVars type)
  let lem := {lem with type := type}
  let lem ← lem.reorderForallInstDep
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
  let lem ← lem.reorderForallInstDep
  return lem

def traceLemmas (pre : String) (lemmas : Array Lemma) : TacticM Unit := do
  let mut cnt : Nat := 0
  let mut mdatas : Array MessageData := #[]
  for lem in lemmas do
    mdatas := mdatas.push m!"\n{cnt}: {lem}"
    cnt := cnt + 1
  trace[auto.printLemmas] mdatas.foldl MessageData.compose pre

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
  traceLemmas "Lemmas collected from local context:" lctxLemmas
  checkDuplicatedFact inputHints.terms
  checkDuplicatedLemmaDB inputHints.lemdbs
  let userLemmas := (← collectUserLemmas inputHints.terms) ++ (← collectHintDBLemmas inputHints.lemdbs)
  let userLemmas ← userLemmas.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Lemmas collected from user-provided terms:" userLemmas
  let defeqLemmas ← collectDefeqLemmas defeqNames
  let defeqLemmas ← defeqLemmas.mapM (m:=MetaM) (unfoldConstAndprepReduceDefeq unfoldInfos)
  traceLemmas "Lemmas collected from user-provided defeq hints:" defeqLemmas
  trace[auto.tactic] "Preprocessing took {(← IO.monoMsNow) - startTime}ms"
  let inhFacts ← Inhabitation.getInhFactsFromLCtx
  let inhFacts ← inhFacts.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Inhabitation lemmas :" inhFacts
  return (lctxLemmas ++ userLemmas ++ defeqLemmas, inhFacts)

open Embedding.Lam in
/--
  If TPTP succeeds, return unsat core
  If TPTP fails, return none
-/
def queryTPTP (exportFacts : Array REntry) : LamReif.ReifM (Array Embedding.Lam.REntry) := do
    let lamVarTy := (← LamReif.getVarVal).map Prod.snd
    let lamEVarTy ← LamReif.getLamEVarTy
    let exportLamTerms ← exportFacts.mapM (fun re => do
      match re with
      | .valid [] t => return t
      | _ => throwError "runAuto :: Unexpected error")
    let query ← lam2TH0 lamVarTy lamEVarTy exportLamTerms
    trace[auto.tptp.printQuery] "\n{query}"
    let tptpProof ← Solver.TPTP.querySolver query
    try
      let proofSteps ← Parser.TPTP.getProof lamVarTy lamEVarTy tptpProof
      for step in proofSteps do
        trace[auto.tptp.printProof] "{step}"
    catch e =>
      trace[auto.tptp.printProof] "TPTP proof reification failed with {e.toMessageData}"
    let unsatCore ← Parser.TPTP.unsatCore tptpProof
    let mut ret := #[]
    for n in unsatCore do
      let .some re := exportFacts[n]?
        | throwError "queryTPTP :: Index {n} out of range"
      ret := ret.push re
    return ret

-- Note: This code is taken from Aesop's Util/Basic.lean file
def addTryThisTacticSeqSuggestion (ref : Syntax) (suggestion : TSyntax ``Lean.Parser.Tactic.tacticSeq)
  (origSpan? : Option Syntax := none) : MetaM Unit := do
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq suggestion
  let msgText := fmt.pretty (indent := 0) (column := 0)
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn map range
    dbg_trace s!"indent: {indent}, column: {column}"
    let text := fmt.pretty (width := Std.Format.defWidth) indent column
    let suggestion := {
      -- HACK: The `tacticSeq` syntax category is pretty-printed with each line
      -- indented by two spaces (for some reason), so we remove this
      -- indentation.
      suggestion := .string $ dedent text
      toCodeActionTitle? := some λ _ => "Create lemmas"
      messageData? := some msgText
      preInfo? := "  "
    }
    Lean.Meta.Tactic.TryThis.addSuggestion ref suggestion (origSpan? := origSpan?)
      (header := "Try this:\n")
where
  dedent (s : String) : String :=
    s.splitOn "\n"
    |>.map (λ line => line.dropPrefix? "  " |>.map (·.toString) |>.getD line)
    |> String.intercalate "\n"

open Embedding.Lam in
def querySMT (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM (Option Expr) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "runAuto :: Unexpected error")
  let commands ← (lamFOL2SMT lamVarTy lamEVarTy exportLamTerms exportInds).run'
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  if (auto.smt.save.get (← getOptions)) then
    Solver.SMT.saveQuery commands
  let .some (unsatCore, proof) ← Solver.SMT.querySolver commands
    | return .none
  for id in ← Solver.SMT.validFactOfUnsatCore unsatCore do
    let .some t := exportLamTerms[id]?
      | throwError "runAuto :: Index {id} of `exportLamTerm` out of range"
    let vderiv ← LamReif.collectDerivFor (.valid [] t)
    trace[auto.smt.unsatCore] "valid_fact_{id}: {vderiv}"
  if auto.smt.rconsProof.get (← getOptions) then
    let (_, _) ← Solver.SMT.getTerm proof
    logWarning "Proof reconstruction is not implemented."
  if (auto.smt.trust.get (← getOptions)) then
    logWarning "Trusting SMT solvers. `autoSMTSorry` is used to discharge the goal."
    return .some (← Meta.mkAppM ``Solver.SMT.autoSMTSorry #[Expr.const ``False []])
  else
    return .none

open Embedding.Lam in
def querySMTForHints (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM (Option (List Expr)) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "runAuto :: Unexpected error")
  let (commands, l2hMap) ← (lamFOL2SMTWithL2hMap lamVarTy lamEVarTy exportLamTerms exportInds).run'
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  if (auto.smt.save.get (← getOptions)) then
    Solver.SMT.saveQuery commands
  let .some (unsatCore, theoryLemmas, proof) ← Solver.SMT.querySolverWithHints commands
    | return .none
  for id in ← Solver.SMT.validFactOfUnsatCore unsatCore do
    let .some t := exportLamTerms[id]?
      | throwError "runAuto :: Index {id} of `exportLamTerm` out of range"
    let vderiv ← LamReif.collectDerivFor (.valid [] t)
    trace[auto.smt.unsatCore] "valid_fact_{id}: {vderiv}"
  let mut symbolMap : HashMap String Expr := HashMap.empty
  let varVal ← LamReif.getVarVal
  for (varName, varAtom) in l2hMap.toArray do
    match varAtom with
    | .term termNum =>
      let vExp := varVal[termNum]!.1
      symbolMap := symbolMap.insert varName vExp
    | _ => logWarning s!"varName: {varName} maps to an atom other than term"
  let lemmaExps ← theoryLemmas.mapM (fun lemTerm => Parser.SMTTerm.parseTerm lemTerm symbolMap)
  return some lemmaExps

open Embedding.Lam in
/--
  If `prover?` is specified, use the specified one.
  Otherwise use the one determined by `Solver.Native.queryNative`
-/
def queryNative
  (declName? : Option Name) (exportFacts exportInhs : Array REntry)
  (prover? : Option (Array Lemma → MetaM Expr) := .none) : LamReif.ReifM (Option Expr) := do
  let (proof, proofLamTerm, usedEtoms, usedInhs, unsatCore) ←
    Lam2D.callNative_checker exportInhs exportFacts (prover?.getD Solver.Native.queryNative)
  LamReif.newAssertion proof (.leaf "by_native::queryNative") proofLamTerm
  let etomInstantiated ← LamReif.validOfInstantiateForall (.valid [] proofLamTerm) (usedEtoms.map .etom)
  let forallElimed ← LamReif.validOfElimForalls etomInstantiated usedInhs
  let contra ← LamReif.validOfImps forallElimed unsatCore
  LamReif.printValuation
  LamReif.printProofs
  Reif.setDeclName? declName?
  let checker ← LamReif.buildCheckerExprFor contra
  let contra ← Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]
  let proof ← Meta.mkLetFVars ((← Reif.getFvarsToAbstract).map Expr.fvar) contra
  return .some proof

/--
  Run native `prover` with monomorphization and preprocessing of `auto`
-/
def runNativeProverWithAuto
  (declName? : Option Name) (prover : Array Lemma → MetaM Expr)
  (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr := do
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let (exportFacts, _) ← LamReif.preprocess exportFacts #[]
    if let .some expr ← queryNative declName? exportFacts exportInhs prover then
      return expr
    else
      throwError "runNativeProverWithAuto :: Failed to find proof")
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let s ← get
    let u ← computeMaxLevel s.facts
    (afterReify s.facts s.inhTys).run' {u := u})
  trace[auto.tactic] "runNativeProverWithAuto :: Found proof of {← Meta.inferType proof}"
  return proof

/--
  Run `auto`'s monomorphization and preprocessing, then send the problem to different solvers
-/
def runAuto (declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr := do
  -- Simplify `ite`
  let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
  -- Simplify `decide`
  let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) (minds : Array (Array SimpleIndVal)) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let exportInds ← LamReif.reifMutInds minds
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- **TPTP invocation and Premise Selection**
    if auto.tptp.get (← getOptions) then
      let premiseSel? := auto.tptp.premiseSelection.get (← getOptions)
      let unsatCore ← queryTPTP exportFacts
      if premiseSel? then
        exportFacts := unsatCore
    -- **SMT**
    if auto.smt.get (← getOptions) then
      if let .some proof ← querySMT exportFacts exportInds then
        return proof
    -- **Native Prover**
    exportFacts := exportFacts.append (← LamReif.auxLemmas exportFacts)
    if auto.native.get (← getOptions) then
      if let .some proof ← queryNative declName? exportFacts exportInhs then
        return proof
    throwError "Auto failed to find proof"
    )
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let s ← get
    let u ← computeMaxLevel s.facts
    (afterReify s.facts s.inhTys s.inds).run' {u := u})
  trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
  return proof

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $instr $hints $[$uords]*) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let instr ← parseInstr instr
    match instr with
    | .none =>
      let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
      let declName? ← Elab.Term.getDeclName?
      let proof ← runAuto declName? lemmas inhFacts
      IO.println s!"Auto found proof. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      absurd.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax

/-- Run `auto`'s monomorphization and preprocessing, then return the list of preprocessing and theory lemmas output
    by the SMT solver. -/
def runAutoGetHints (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM (List Expr) := do
  -- Simplify `ite`
  let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
  -- Simplify `decide`
  let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) (minds : Array (Array SimpleIndVal))
    : LamReif.ReifM (List Expr) := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInds ← LamReif.reifMutInds minds
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- runAutoGetHints only supports SMT right now
    -- **SMT**
    if auto.smt.get (← getOptions) then
      if let .some lemmas ← querySMTForHints exportFacts exportInds then
        return lemmas
    throwError "autoGetHints only implemented for cvc5 (enable option auto.smt)"
    )
  let (lemmas, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM (List Expr)) do
    let s ← get
    let u ← computeMaxLevel s.facts
    (afterReify s.facts s.inhTys s.inds).run' {u := u})
  trace[auto.tactic] "Auto found preprocessing and theory lemmas: {lemmas}"
  return lemmas

syntax (name := autoGetHints) "autoGetHints" autoinstr hints (uord)* : tactic

@[tactic autoGetHints]
def evalAutoGetHints : Tactic
| `(autoGetHints | autoGetHints%$stxRef $instr $hints $[$uords]*) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let instr ← parseInstr instr
    match instr with
    | .none =>
      let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
      let lemmas ← runAutoGetHints lemmas inhFacts
      IO.println s!"Auto found hints. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      let lemmasStx ← lemmas.mapM (fun lemExp => PrettyPrinter.delab lemExp)
      if lemmasStx.length = 0 then
        IO.println "SMT solver did not generate any theory lemmas"
      else
        let mut tacticsArr : Array Syntax.Tactic := #[]
        for lemmaStx in lemmasStx do
          tacticsArr := tacticsArr.push $ ← `(tactic| have : $lemmaStx := sorry)
        let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $tacticsArr*)
        withOptions (fun o => (o.set `pp.analyze true).set `pp.funBinderTypes true) $
          addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax

@[tactic intromono]
def evalIntromono : Tactic
| `(intromono | intromono $hints $[$uords]*) => withMainContext do
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, _) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let newMid ← Monomorphization.intromono lemmas absurd
    replaceMainGoal [newMid]
| _ => throwUnsupportedSyntax

/--
  A monomorphization interface that can be invoked by repos dependent on `lean-auto`.
  **TODO: Change `prover : Array Lemma → MetaM Expr` to have type `proverName : String`**
-/
def monoInterface
  (lemmas : Array Lemma) (inhFacts : Array Lemma)
  (prover : Array Lemma → MetaM Expr) : MetaM Expr := do
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let proof ← Lam2D.callNative_direct exportInhs exportFacts prover
    Meta.mkLetFVars ((← Reif.getFvarsToAbstract).map Expr.fvar) proof)
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let uvalids ← liftM <| Reif.getFacts
    let uinhs ← liftM <| Reif.getInhTys
    let u ← computeMaxLevel uvalids
    (afterReify uvalids uinhs).run' {u := u})
  return proof

@[tactic mononative]
def evalMonoNative : Tactic
| `(mononative | mononative $hints $[$uords]*) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let proof ← monoInterface lemmas inhFacts Solver.Native.queryNative
    IO.println s!"Auto found proof. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
    absurd.assign proof
| _ => throwUnsupportedSyntax

end Auto
