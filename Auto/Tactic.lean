import Lean
import Auto.Translation
import Auto.Solver.SMT
import Auto.Solver.TPTP
import Auto.Solver.Native
import Auto.HintDB
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.printLemmas

namespace Auto

syntax hintelem := term <|> "*"
syntax hints := ("[" hintelem,* "]")?
-- Must be topologically sorted, refer to `Lemma.unfoldConsts`
-- **TODO**: Automatically topological sort
syntax unfolds := ("u[" ident,* "]")?
syntax defeqs := ("d[" ident,* "]")?
syntax autoinstr := ("👍" <|> "👎")?
syntax (name := auto) "auto" autoinstr hints unfolds defeqs : tactic
syntax (name := mononative) "mononative" hints unfolds defeqs : tactic
syntax (name := intromono) "intromono" hints unfolds defeqs : tactic

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
  | hintdb   : HintElem
  -- `*` adds all hypotheses in the local context
  -- Also, if `[..]` is not supplied to `auto`, all
  --   hypotheses in the local context are
  --   automatically collected.
  | lctxhyps : HintElem
deriving Inhabited, BEq

def parseHintElem : TSyntax ``hintelem → TacticM HintElem
| `(hintelem| *)       => return .lctxhyps
| `(hintelem| $t:term) => return .term t
| _ => throwUnsupportedSyntax

structure InputHints where
  terms    : Array Term := #[]
  hintdbs  : Array Unit := #[]
  lctxhyps : Bool       := false
deriving Inhabited, BEq

/-- Parse `hints` to an array of `Term`, which is still syntax -/
def parseHints : TSyntax ``hints → TacticM InputHints
| `(hints| [ $[$hs],* ]) => do
  let mut terms := #[]
  let mut lctxhyps := false
  let elems ← hs.mapM parseHintElem
  for elem in elems do
    match elem with
    | .term t => terms := terms.push t
    | .lctxhyps => lctxhyps := true
    | _ => throwError "parseHints :: Not implemented"
  return ⟨terms, #[], lctxhyps⟩
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
| `(unfolds|) => pure #[]
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
| `(defeqs|) => pure #[]
| _ => throwUnsupportedSyntax

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
        lemmas := lemmas.push ⟨mkFVar fVarId, type, #[]⟩
    return lemmas

def collectUserLemmas (terms : Array Term) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let mut lemmas := #[]
    for ⟨proof, type, params⟩ in ← terms.mapM Prep.elabLemma do
      if ← Prep.isNonemptyInhabited type then
        throwError "invalid lemma {type}, lemmas should not be inhabitation facts"
      else if ← Meta.isProp type then
        lemmas := lemmas.push ⟨proof, ← instantiateMVars type, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
    return lemmas

def collectDefeqLemmas (names : Array Name) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let lemmas ← names.concatMapM Prep.elabDefEq
    lemmas.mapM (fun (⟨proof, type, params⟩ : Lemma) => do
      let type ← instantiateMVars type
      return ⟨proof, type, params⟩)

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

def collectAllLemmas (hintstx : TSyntax ``hints) (unfolds : TSyntax `Auto.unfolds)
  (defeqs : TSyntax `Auto.defeqs) (ngoalAndBinders : Array FVarId) :
  -- The first `Array Lemma` are `Prop` lemmas
  -- The second `Array Lemma` are Inhabitation facts
  TacticM (Array Lemma × Array Lemma) := do
  let inputHints ← parseHints hintstx
  let unfoldInfos ← parseUnfolds unfolds
  let defeqNames ← parseDefeqs defeqs
  let startTime ← IO.monoMsNow
  let lctxLemmas ← collectLctxLemmas inputHints.lctxhyps ngoalAndBinders
  let lctxLemmas ← lctxLemmas.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Lemmas collected from local context:" lctxLemmas
  checkDuplicatedFact inputHints.terms
  let userLemmas ← collectUserLemmas inputHints.terms
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

/-- `ngoal` means `negated goal` -/
def runAuto (declName? : Option Name) (prover : Option (Array Lemma → MetaM Expr) := none)
  (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr := do
  -- Simplify `ite`
  let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
  -- Simplify `decide`
  let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp
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
      let queryResult ← queryTPTP exportFacts
      if premiseSel? then
        match queryResult with
        | .some unsatCore =>
          for re in unsatCore do
            trace[auto.tptp.premiseSelection] "{re}"
          exportFacts := unsatCore
        | .none => trace[auto.tptp.premiseSelection] "TPTP invocation failed, skipping TPTP premise selection"
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
    let uvalids ← liftM <| Reif.getFacts
    let uinhs ← liftM <| Reif.getInhTys
    let inds ← liftM <| Reif.getInds
    let u ← computeMaxLevel uvalids
    (afterReify uvalids uinhs inds).run' {u := u})
  trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
  return proof
where
  /--
    If TPTP succeeds, return unsat core
    If TPTP fails, return none
  -/
  queryTPTP exportFacts : LamReif.ReifM (Option (Array Embedding.Lam.REntry)) := do
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
    return .some ret
  querySMT exportFacts exportInds : LamReif.ReifM (Option Expr) := do
    let lamVarTy := (← LamReif.getVarVal).map Prod.snd
    let lamEVarTy ← LamReif.getLamEVarTy
    let exportLamTerms ← exportFacts.mapM (fun re => do
      match re with
      | .valid [] t => return t
      | _ => throwError "runAuto :: Unexpected error")
    let commands ← (lamFOL2SMT lamVarTy lamEVarTy exportLamTerms exportInds).run'
    for cmd in commands do
      trace[auto.smt.printCommands] "{cmd}"
    let .some _ ← Solver.SMT.querySolver commands
      | return .none
    if (auto.smt.trust.get (← getOptions)) then
      logWarning "Trusting SMT solvers. `autoSMTSorry` is used to discharge the goal."
      return .some (← Meta.mkAppM ``Solver.SMT.autoSMTSorry #[Expr.const ``False []])
    else
      return .none
  queryNative declName? exportFacts exportInhs : LamReif.ReifM (Option Expr) := do
    let (proof, proofLamTerm, usedEtoms, usedInhs, unsatCore) ←
      -- If a prover function is provided use that. Otherwise, use the function indicated by auto.native.solver.func
      match prover with
      | none => Lam2D.callNative_checker exportInhs exportFacts Solver.Native.queryNative
      | some prover => Lam2D.callNative_checker exportInhs exportFacts (Solver.Native.queryNativeFromFunction prover)
    LamReif.newAssertion proof proofLamTerm
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

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $instr $hints $unfolds $defeqs) => withMainContext do
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
      let (lemmas, inhFacts) ← collectAllLemmas hints unfolds defeqs (goalBinders.push ngoal)
      let declName? ← Elab.Term.getDeclName?
      let proof ← runAuto declName? none lemmas inhFacts
      IO.println s!"Auto found proof. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      absurd.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax

@[tactic intromono]
def evalIntromono : Tactic
| `(intromono | intromono $hints $unfolds $defeqs) => withMainContext do
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, _) ← collectAllLemmas hints unfolds defeqs (goalBinders.push ngoal)
    let newMid ← Monomorphization.intromono lemmas absurd
    replaceMainGoal [newMid]
| _ => throwUnsupportedSyntax

/--
  An interface to monomorphization and preprocessing by verified checker
-/
def monoPrepInterface
  (declName? : Option Name) (prover : Array Lemma → MetaM Expr)
  (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr :=
  withOptions (fun opts =>
    let opts := opts.set ``auto.smt false
    let opts := opts.set ``auto.tptp false
    let opts := opts.set ``auto.native true
    opts) (runAuto declName? (.some prover) lemmas inhFacts)

/--
  A monomorphization interface that can be invoked by repos dependent
    on `lean-auto`.
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
| `(mononative | mononative $hints $unfolds $defeqs) => withMainContext do
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
    let (lemmas, inhFacts) ← collectAllLemmas hints unfolds defeqs (goalBinders.push ngoal)
    let proof ← monoInterface lemmas inhFacts Solver.Native.queryNative
    IO.println s!"Auto found proof. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
    absurd.assign proof
| _ => throwUnsupportedSyntax

end Auto
