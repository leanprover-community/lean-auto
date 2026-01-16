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

register_option auto.getHints.failOnParseError : Bool := {
  defValue := false
  descr := "Whether to throw an error or ignore smt lemmas that can not be parsed"
}

def auto.getHints.getFailOnParseError (opts : Options) : Bool :=
  auto.getHints.failOnParseError.get opts

def auto.getHints.getFailOnParseErrorM : CoreM Bool := do
  let opts ← getOptions
  return getHints.getFailOnParseError opts

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
        lemmas := lemmas.push ⟨⟨mkFVar fVarId, type, .leaf s!"lctxLem {name} (fvarId: {fVarId.name})"⟩, #[]⟩
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

/-- Returns the longest common prefix of two substrings.
    The returned substring will use the same underlying string as `s`.

    Note: Code taken from Std -/
def commonPrefix (s t : Substring.Raw) : Substring.Raw :=
  { s with stopPos := loop s.startPos t.startPos }
where
  /-- Returns the ending position of the common prefix, working up from `spos, tpos`. -/
  loop spos tpos :=
    if h : spos < s.stopPos ∧ tpos < t.stopPos then
      if String.Pos.Raw.get s.str spos == String.Pos.Raw.get t.str tpos then
        have := Nat.sub_lt_sub_left h.1 (String.Pos.Raw.byteIdx_lt_byteIdx_next s.str spos)
        loop (String.Pos.Raw.next s.str spos) (String.Pos.Raw.next t.str tpos)
      else
        spos
    else
      spos
  termination_by s.stopPos.byteIdx - spos.byteIdx

/-- If `pre` is a prefix of `s`, i.e. `s = pre ++ t`, returns the remainder `t`. -/
def dropPrefix? (s : Substring.Raw) (pre : Substring.Raw) : Option Substring.Raw :=
  let t := commonPrefix s pre
  if Substring.Raw.bsize t = Substring.Raw.bsize pre then
    some { s with startPos := t.stopPos }
  else
    none

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
    |>.map (λ line => dropPrefix? line.toRawSubstring "  ".toRawSubstring |>.map (·.toString) |>.getD line)
    |> String.intercalate "\n"

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
    let (_, _) ← Solver.SMT.getTerm proof
    logWarning "Proof reconstruction is not implemented."
  if (auto.smt.trust.get (← getOptions)) then
    logWarning "Trusting SMT solvers. `autoSMTSorry` is used to discharge the goal."
    return (← Meta.mkAppM ``autoSMTSorry #[Expr.const ``False []], unsatCore)
  else
    return (.none, unsatCore)

/-- `solverHints` includes:
    - `unsatCoreDerivLeafStrings` an array of Strings that appear as leaves in any derivation for any fact in the unsat core
    - `selectorInfos` which is an array of
      - The SMT selector name (String)
      - The constructor that the selector is for (Expr)
      - The index of the argument it is a selector for (Nat)
      - The type of the selector function (Expr)
    - `preprocessFacts` : List Expr
    - `theoryLemmas` : List Expr
    - `instantiations` : List Expr
    - `computationLemmas` : List Expr
    - `polynomialLemmas` : List Expr
    - `rewriteFacts` : List (List Expr)

    Note 1: In all fields except `selectorInfos`, there may be loose bound variables. The loose bound variable `#i` corresponds to
    the selector indicated by `selectorInfos[i]`

    Note 2: When the external solver is cvc5, all fields can be populated, but when the external solver is Zipperposition, only the
    first field (`unsatCoreDerivLeafStrings`) will be populated -/
abbrev solverHints := Array String × Array (String × Expr × Nat × Expr) × List Expr × List Expr × List Expr × List Expr × List Expr × List (List Expr)

open Embedding.Lam in
def querySMTForHints (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM (Option solverHints) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => pure t
    | _ => throwError "runAuto :: Unexpected error")
  let sni : SMT.SMTNamingInfo :=
    {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
  let ((commands, validFacts, l2hMap, wfPredicatesInvMap, selInfos), state) ←
    (lamFOL2SMTWithExtraInfo sni lamVarTy lamEVarTy exportLamTerms exportInds).run
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  if (auto.smt.save.get (← getOptions)) then
    Solver.SMT.saveQuery commands
  let some (unsatCore, solverHints, _proof) ← Solver.SMT.querySolverWithHints commands
    | return none
  let unsatCoreIds ← Solver.SMT.validFactOfUnsatCore unsatCore
  -- **Print valuation of SMT atoms**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for (atomic, name) in state.h2lMap.toArray do
      let e ← SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap atomic
      trace[auto.smt.printValuation] "|{name}| : {e}"
    )
  -- **Print STerms corresponding to `validFacts` in unsatCore**
  for id in unsatCoreIds do
    let some sterm := validFacts[id]?
      | throwError "runAuto :: Index {id} of `validFacts` out of range"
    trace[auto.smt.unsatCore.smtTerms] "|valid_fact_{id}| : {sterm}"
  -- **Print Lean expressions correesponding to `validFacts` in unsatCore**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for id in unsatCoreIds do
      let some t := exportLamTerms[id]?
        | throwError "runAuto :: Index {id} of `exportLamTerms` out of range"
      let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
      trace[auto.smt.unsatCore.leanExprs] "|valid_fact_{id}| : {← Core.betaReduce e}"
    )
  -- **Print derivation of unsatCore and collect unsatCore derivation leaves**
  -- `unsatCoreDerivLeafStrings` contains all of the strings that appear as leaves in any derivation for any fact in the unsat core
  let mut unsatCoreDerivLeafStrings := #[]
  for id in unsatCoreIds do
    let some t := exportLamTerms[id]?
      | throwError "runAuto :: Index {id} of `exportLamTerm` out of range"
    let vderiv ← LamReif.collectDerivFor (.valid [] t)
    unsatCoreDerivLeafStrings := unsatCoreDerivLeafStrings ++ vderiv.collectLeafStrings
    trace[auto.smt.unsatCore.deriv] "|valid_fact_{id}| : {vderiv}"
  -- **Build symbolPrecMap using l2hMap, wfPredicatesInvMap, and selInfos**
  let (preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts) := solverHints
  let mut symbolMap : Std.HashMap String Expr := Std.HashMap.emptyWithCapacity
  for (varName, varAtom) in l2hMap.toArray do
    let varLeanExp ←
      SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
        SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap varAtom)
    symbolMap := symbolMap.insert varName varLeanExp
  for (wfPredicateName, wfPredicateSort) in wfPredicatesInvMap.toArray do
    let ty ← SMT.withExprValuation sni state.h2lMap (fun tyValMap _ _ => Lam2D.interpLamSortAsUnlifted tyValMap wfPredicateSort)
    let tyPred := .lam .anonymous ty (mkConst ``True) .default -- Interpret `_wf_α` as `fun _ : α => True`
    symbolMap := symbolMap.insert wfPredicateName tyPred
  /- `selectorArr` has entries containing:
     - The name of an SMT selector function
     - The constructor it is a selector for
     - The index of the argument it is a selector for
     - The mvar used to represent the selector function -/
  let mut selectorArr : Array (String × Expr × Nat × Expr) := #[]
  for (selName, selIsProjection, selCtor, argIdx, datatypeName, _selInputType, selOutputType) in selInfos do
    if !selIsProjection then -- Projections already have corresponding values in Lean and therefore don't need to be added to `selectorArr`
      let selCtor ←
        SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
          SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap selCtor)
      let selOutputType ←
        SMT.withExprValuation sni state.h2lMap (fun tyValMap _ _ => Lam2D.interpLamSortAsUnlifted tyValMap selOutputType)
      let selDatatype ←
        match symbolMap.get? datatypeName with
        | some selDatatype => pure selDatatype
        | none => throwError "querySMTForHints :: Could not find the datatype {datatypeName} corresponding to selector {selName}"
      let selType := Expr.forallE `x selDatatype selOutputType .default
      let selMVar ← Meta.mkFreshExprMVar selType
      selectorArr := selectorArr.push (selName, selCtor, argIdx, selMVar)
      symbolMap := symbolMap.insert selName selMVar
  let selectorMVars := selectorArr.map (fun (_, _, _, selMVar) => selMVar)
  -- Change the last argument of selectorArr from the mvar used to represent the selector function to its type
  selectorArr ← selectorArr.mapM
    (fun (selName, selCtor, argIdx, selMVar) => return (selName, selCtor, argIdx, ← Meta.inferType selMVar))
  -- **Extract solverLemmas from solverHints**
  if ← auto.getHints.getFailOnParseErrorM then
    try
      let preprocessFacts ← preprocessFacts.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let theoryLemmas ← theoryLemmas.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let instantiations ← instantiations.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let computationLemmas ← computationLemmas.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let polynomialLemmas ← polynomialLemmas.mapM
        (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      let rewriteFacts ← rewriteFacts.mapM
        (fun rwFacts => do
          match rwFacts with
          | [] => return []
          | rwRule :: ruleInstances =>
            /- Try to parse `rwRule`. If succesful, just return that. If unsuccessful (e.g. because the rule contains approximate types),
              then parse each quantifier-free instance of `rwRule` in `ruleInstances` and return all of those. -/
            match ← Parser.SMTTerm.tryParseTermAndAbstractSelectors rwRule symbolMap selectorMVars with
            | some parsedRule => return [parsedRule]
            | none => ruleInstances.mapM (fun lemTerm => Parser.SMTTerm.parseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
        )
      return some (unsatCoreDerivLeafStrings, selectorArr, preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts)
    catch e =>
      throwError "querySMTForHints :: Encountered error trying to parse SMT solver's hints. Error: {e.toMessageData}"
  else
    let preprocessFacts ← preprocessFacts.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let theoryLemmas ← theoryLemmas.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let instantiations ← instantiations.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let computationLemmas ← computationLemmas.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let polynomialLemmas ← polynomialLemmas.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
    let rewriteFacts ← rewriteFacts.mapM
      (fun rwFacts => do
        match rwFacts with
        | [] => return []
        | rwRule :: ruleInstances =>
          /- Try to parse `rwRule`. If succesful, just return that. If unsuccessful (e.g. because the rule contains approximate types),
             then parse each quantifier-free instance of `rwRule` in `ruleInstances` and return all of those. -/
          match ← Parser.SMTTerm.tryParseTermAndAbstractSelectors rwRule symbolMap selectorMVars with
          | some parsedRule => return [some parsedRule]
          | none => ruleInstances.mapM (fun lemTerm => Parser.SMTTerm.tryParseTermAndAbstractSelectors lemTerm symbolMap selectorMVars)
      )
    -- Filter out `none` results from the above lists (so we can gracefully ignore lemmas that we couldn't parse)
    let preprocessFacts := preprocessFacts.filterMap id
    let theoryLemmas := theoryLemmas.filterMap id
    let instantiations := instantiations.filterMap id
    let computationLemmas := computationLemmas.filterMap id
    let polynomialLemmas := polynomialLemmas.filterMap id
    let rewriteFacts := rewriteFacts.map (fun rwFacts => rwFacts.filterMap id)
    return some (unsatCoreDerivLeafStrings, selectorArr, preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts)

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
  ReifM (Array (REntry × DTr) × Array (REntry × DTr) × MVarId ×
         Expr × LamTerm × Array Expr × Array Nat) := do
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

/-- Runs `auto`'s monomorphization and preprocessing, then returns `solverHints` determined by the external prover's output -/
def runAutoGetHints (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM solverHints :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let (solverHints, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM solverHints) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    return solverHints
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM solverHints := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- **TPTP invocation and Premise Selection**
    if auto.tptp.get (← getOptions) then
      if auto.tptp.premiseSelection.get (← getOptions) then
        let (_, some unsatCore) ← queryTPTP exportFacts
          | throwError "runAutoGetHints :: External TPTP solver unable to solve the goal"
        let mut unsatCoreDerivLeafStrings := #[]
        for fact in unsatCore do
          let factDTR ← LamReif.collectDerivFor fact
          unsatCoreDerivLeafStrings := unsatCoreDerivLeafStrings ++ factDTR.collectLeafStrings
          trace[auto.tptp.unsatCore.deriv] "{fact} DTR: {factDTR}"
        -- When the external prover uses the TPTP format, only information about the unsat core can be collected
        return (unsatCoreDerivLeafStrings, #[], [], [], [], [], [], [])
      else
        throwError "runAutoGetHints :: No hints to return if auto.tptp is enabled but auto.tptp.premiseSelection is disabled"
    -- **SMT**
    else if auto.smt.get (← getOptions) then
      if let .some solverHints ← querySMTForHints exportFacts exportInds then
        return solverHints
      else
        throwError "runAutoGetHints :: SMT solver was unable to find a proof"
    -- **Native Prover**
    else
      throwError "runAutoGetHints :: Either auto.smt or auto.tptp must be enabled"

syntax (name := autoGetHints) "autoGetHints" autoinstr hints (uord)* : tactic

/-- Given an expression `∀ x1 : t1, x2 : t2, ... xn : tn, b`, returns `[t1, t2, ..., tn]`. If the given expression is not
    a forall expression, then `getForallArgumentTypes` just returns the empty list -/
partial def getForallArgumentTypes (e : Expr) : List Expr :=
  match e.consumeMData with
  | Expr.forallE _ t b _ => t :: (getForallArgumentTypes b)
  | _ => []

/-- Given the constructor `selCtor` of some inductive datatype and an `argIdx` which is less than `selCtor`'s total number
    of fields, `buildSelectorForInhabitedType` uses the datatype's recursor to build a function that takes in the datatype
    and outputs a value of the same type as the argument indicated by `argIdx`. This function has the property that if it is
    passed in `selCtor`, it returns the `argIdx`th argument of `selCtor`, and if it is passed in a different constructor, it
    returns the default value of the appropriate type. -/
def buildSelectorForInhabitedType (selCtor : Expr) (argIdx : Nat) : MetaM Expr := do
  let (cval, lvls) ← matchConstCtor selCtor.getAppFn'
    (fun _ => throwError "buildSelectorForInhabitedType :: {selCtor} is not a constructor")
    (fun cval lvls => pure (cval, lvls))
  let selCtorParams := selCtor.getAppArgs
  let selCtorType ← Meta.inferType selCtor
  let selCtorFieldTypes := (getForallArgumentTypes selCtorType).toArray
  let selectorOutputType ←
    match selCtorFieldTypes[argIdx]? with
    | some outputType => pure outputType
    | none => throwError "buildSelectorForInhabitedType :: argIdx {argIdx} out of bounds for constructor {selCtor}"
  let selectorOutputUniverseLevel ← do
    let selectorOutputTypeSort ← Meta.inferType selectorOutputType
    pure selectorOutputTypeSort.sortLevel!
  let datatypeName := cval.induct
  let datatype ← Meta.mkAppM' (mkConst datatypeName lvls) selCtorParams
  let ival ← matchConstInduct datatype.getAppFn
    (fun _ => throwError "buildSelectorForInhabitedType :: The datatype of {selCtor} ({datatype}) is not a datatype")
    (fun ival _ => pure ival)
  let mutuallyRecursiveDatatypes ← ival.all.mapM
    (fun n => do
      let nConst ← Meta.mkAppM' (mkConst n lvls) selCtorParams
      matchConstInduct nConst.getAppFn
        (fun _ => throwError "buildSelectorForInhabitedType :: Error in gathering InductiveVal for {nConst} which should be mutually recursive with {datatype}")
        (fun ival _ => pure (nConst, ival)))
  let recursor := (mkConst (.str datatypeName "rec") (selectorOutputUniverseLevel :: lvls))
  let mut recursorArgs := selCtorParams
  let motives := mutuallyRecursiveDatatypes.map (fun (t, _) => Expr.lam `_ t selectorOutputType .default)
  recursorArgs := recursorArgs ++ motives.toArray
  let datatypesAndMotives := mutuallyRecursiveDatatypes.zip motives
  for (curDatatype, curDatatypeInfo) in mutuallyRecursiveDatatypes do
    for curCtorIdx in [:curDatatypeInfo.ctors.length] do
      if curDatatype == datatype && curCtorIdx == cval.cidx then
        let decls := selCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) curCtorFields[argIdx]!
        recursorArgs := recursorArgs.push nextRecursorArg
      else
        let curCtor := mkConst curDatatypeInfo.ctors[curCtorIdx]! lvls
        let curCtor ← Meta.mkAppOptM' curCtor (selCtorParams.map some)
        let curCtorType ← Meta.inferType curCtor
        let curCtorFieldTypes := (getForallArgumentTypes curCtorType).toArray
        let decls := curCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) $ ← Meta.mkAppOptM `Inhabited.default #[some selectorOutputType, none]
        recursorArgs := recursorArgs.push nextRecursorArg
  Meta.mkAppOptM' recursor $ recursorArgs.map some

/-- Given the constructor `selCtor` of some inductive datatype and an `argIdx` which is less than `selCtor`'s total number
    of fields, `buildSelectorForUninhabitedType` uses the datatype's recursor to build a function that takes in the datatype
    and outputs a value of the same type as the argument indicated by `argIdx`. This function has the property that if it is
    passed in `selCtor`, it returns the `argIdx`th argument of `selCtor`, and if it is passed in a different constructor, it
    returns `sorry`. -/
def buildSelectorForUninhabitedType (selCtor : Expr) (argIdx : Nat) : MetaM Expr := do
  let (cval, lvls) ← matchConstCtor selCtor.getAppFn'
    (fun _ => throwError "buildSelectorForUninhabitedType :: {selCtor} is not a constructor")
    (fun cval lvls => pure (cval, lvls))
  let selCtorParams := selCtor.getAppArgs
  let selCtorType ← Meta.inferType selCtor
  let selCtorFieldTypes := (getForallArgumentTypes selCtorType).toArray
  let selectorOutputType ←
    match selCtorFieldTypes[argIdx]? with
    | some outputType => pure outputType
    | none => throwError "buildSelectorForUninhabitedType :: argIdx {argIdx} out of bounds for constructor {selCtor}"
  let selectorOutputUniverseLevel ← do
    let selectorOutputTypeSort ← Meta.inferType selectorOutputType
    pure selectorOutputTypeSort.sortLevel!
  let datatypeName := cval.induct
  let datatype ← Meta.mkAppM' (mkConst datatypeName lvls) selCtorParams
  let ival ← matchConstInduct datatype.getAppFn
    (fun _ => throwError "buildSelectorForUninhabitedType :: The datatype of {selCtor} ({datatype}) is not a datatype")
    (fun ival _ => pure ival)
  let mutuallyRecursiveDatatypes ← ival.all.mapM
    (fun n => do
      let nConst ← Meta.mkAppM' (mkConst n lvls) selCtorParams
      matchConstInduct nConst.getAppFn
        (fun _ => throwError "buildSelectorForUninhabitedType :: Error in gathering InductiveVal for {nConst} which should be mutually recursive with {datatype}")
        (fun ival _ => pure (nConst, ival)))
  let recursor := (mkConst (.str datatypeName "rec") (selectorOutputUniverseLevel :: lvls))
  let mut recursorArgs := selCtorParams
  let motives := mutuallyRecursiveDatatypes.map (fun (t, _) => Expr.lam `_ t selectorOutputType .default)
  recursorArgs := recursorArgs ++ motives.toArray
  let datatypesAndMotives := mutuallyRecursiveDatatypes.zip motives
  for (curDatatype, curDatatypeInfo) in mutuallyRecursiveDatatypes do
    for curCtorIdx in [:curDatatypeInfo.ctors.length] do
      if curDatatype == datatype && curCtorIdx == cval.cidx then
        let decls := selCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) curCtorFields[argIdx]!
        recursorArgs := recursorArgs.push nextRecursorArg
      else
        let curCtor := mkConst curDatatypeInfo.ctors[curCtorIdx]! lvls
        let curCtor ← Meta.mkAppOptM' curCtor (selCtorParams.map some)
        let curCtorType ← Meta.inferType curCtor
        let curCtorFieldTypes := (getForallArgumentTypes curCtorType).toArray
        let decls := curCtorFieldTypes.mapFinIdx fun idx ty _ => (.str .anonymous ("arg" ++ idx.repr), fun prevArgs => pure (ty.instantiate prevArgs))
        let nextRecursorArg ←
          Meta.withLocalDeclsD decls fun curCtorFields => do
            let recursiveFieldMotiveDecls ← curCtorFields.filterMapM
              (fun ctorFieldFVar => do
                let ctorFieldFVarType ← Meta.inferType ctorFieldFVar
                match datatypesAndMotives.find? (fun ((t, _), _) => t == ctorFieldFVarType) with
                | none => return none
                | some (_, ctorMotive) => return some $ (`_, ((fun _ => Meta.mkAppM' ctorMotive #[ctorFieldFVar]) : Array Expr → MetaM Expr))
              )
            Meta.withLocalDeclsD recursiveFieldMotiveDecls fun recursiveFieldMotiveFVars => do
              Meta.mkLambdaFVars (curCtorFields ++ recursiveFieldMotiveFVars) $ ← Meta.mkSorry selectorOutputType false
        recursorArgs := recursorArgs.push nextRecursorArg
  Meta.mkAppOptM' recursor $ recursorArgs.map some

/-- Given the constructor `selCtor` of some inductive datatype and an `argIdx` which is less than `selCtor`'s total number
    of fields, `buildSelectorForInhabitedType` uses the datatype's recursor to build a function that takes in the datatype
    and outputs a value of the same type as the argument indicated by `argIdx`. This function has the property that if it is
    passed in `selCtor`, it returns the `argIdx`th argument of `selCtor`. -/
def buildSelector (selCtor : Expr) (argIdx : Nat) : MetaM Expr := do
  try
    buildSelectorForInhabitedType selCtor argIdx
  catch _ =>
    buildSelectorForUninhabitedType selCtor argIdx

/-- Given the information relating to a selector of type `idt → argType`, returns the selector fact entailed by SMT-Lib's semantics
    (`∃ f : idt → argType, ∀ ctor_fields, f (ctor ctor_fields) = ctor_fields[argIdx]`)-/
def buildSelectorFact (selName : String) (selCtor selType : Expr) (argIdx : Nat) : MetaM Expr := do
  let selCtorType ← Meta.inferType selCtor
  let selCtorFieldTypes := getForallArgumentTypes selCtorType
  let selCtorDeclInfos : Array (Name × (Array Expr → MetaM Expr)) ← do
    let mut declInfos := #[]
    let mut declCounter := 0
    let baseName := "arg"
    for selCtorFieldType in selCtorFieldTypes do
      let argName := Name.str .anonymous (baseName ++ declCounter.repr)
      let argConstructor : Array Expr → MetaM Expr := (fun _ => pure selCtorFieldType)
      declInfos := declInfos.push (argName, argConstructor)
      declCounter := declCounter + 1
    pure declInfos
  Meta.withLocalDeclD (.str .anonymous selName) selType $ fun selectorFVar => do
    Meta.withLocalDeclsD selCtorDeclInfos $ fun selCtorArgFVars => do
      let selCtorWithFields ← Meta.mkAppM' selCtor selCtorArgFVars
      let selectedArg := selCtorArgFVars[argIdx]!
      let existsBody ← Meta.mkForallFVars selCtorArgFVars $ ← Meta.mkAppM ``Eq #[← Meta.mkAppM' selectorFVar #[selCtorWithFields], selectedArg]
      let existsArg ← Meta.mkLambdaFVars #[selectorFVar] existsBody (binderInfoForMVars := .default)
      Meta.mkAppM ``Exists #[existsArg]

/-- `ppOptionsSetting` is used to ensure that the tactics suggested by `autoGetHints` are pretty printed correctly -/
def ppOptionsSetting (o : Options) : Options :=
  let o := o.set `pp.analyze true
  let o := o.set `pp.proofs true
  let o := o.set `pp.funBinderTypes true
  o.set `pp.piBinderTypes true

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
      let (_, selectorInfos, lemmas) ← runAutoGetHints lemmas inhFacts
      IO.println s!"Auto found hints. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      let allLemmas :=
        lemmas.1 ++ lemmas.2.1 ++ lemmas.2.2.1 ++ lemmas.2.2.2.1 ++ lemmas.2.2.2.2.1 ++
        (lemmas.2.2.2.2.2.foldl (fun acc l => acc ++ l) [])
      if allLemmas.length = 0 then
        IO.println "SMT solver did not generate any theory lemmas"
      else
        let mut tacticsArr := #[]
        for (selName, selCtor, argIdx, selType) in selectorInfos do
          let selFactName := selName ++ "Fact"
          let selector ← buildSelector selCtor argIdx
          let selectorStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selector
          let selectorFact ← buildSelectorFact selName selCtor selType argIdx
          let selectorFactStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selectorFact
          let existsIntroStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab (mkConst ``Exists.intro)
          tacticsArr := tacticsArr.push $
            ← `(tactic|
                have ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                  apply $existsIntroStx:term $selectorStx:term
                  intros
                  rfl
              )
          evalTactic $ -- Eval to add selector and its corresponding fact to lctx
            ← `(tactic|
                have ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                  apply $existsIntroStx:term $selectorStx:term
                  intros
                  rfl
              )
        let lemmasStx ← withMainContext do -- Use updated main context so that newly added selectors are accessible
          let lctx ← getLCtx
          let mut selectorFVars := #[]
          for (selUserName, _, _, _) in selectorInfos do
            match lctx.findFromUserName? (.str .anonymous selUserName) with
            | some decl => selectorFVars := selectorFVars.push (.fvar decl.fvarId)
            | none => throwError "evalAutoGetHints :: Error in trying to access selector definition for {selUserName}"
          let allLemmas := allLemmas.map (fun lem => lem.instantiateRev selectorFVars)
          trace[auto.tactic] "allLemmas: {allLemmas}"
          allLemmas.mapM (fun lemExp => withOptions ppOptionsSetting $ PrettyPrinter.delab lemExp)
        for lemmaStx in lemmasStx do
          tacticsArr := tacticsArr.push $ ← `(tactic| have : $lemmaStx := sorry)
        tacticsArr := tacticsArr.push $ ← `(tactic| sorry)
        let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $tacticsArr*)
        withOptions ppOptionsSetting $ addTryThisTacticSeqSuggestion stxRef tacticSeq (← getRef)
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      let finalGoal ← getMainGoal -- Need to update main goal because running evalTactic to add selectors can change the main goal
      finalGoal.assign proof
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
  · `atomVals : Array (FVarId × Expr)`
                    The values of the type lam-atoms and term lam-atoms
  · `derivs : Array (FVarId × DTr)`
                    The `DTr`s associated with (monomorphized) lemmas and inhabitation lemmas
                    in the context of `id`. Using this information you can obtain the
                    correspondence between monomorphized lemmas and the original lemmas
-/
def runMono
  (declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma) :
  MetaM (Expr × MVarId × Array (FVarId × Expr) × Array (FVarId × DTr)) :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let ((proof, goalId, atomVals, derivs), _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM _) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    trace[auto.tactic.printProof] "{proof}"
    return (proof, goalId, atomVals, derivs)
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM (Expr × MVarId × Array (FVarId × Expr) × Array (FVarId × DTr)) := do
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
    let (nonemptyWithDTrs, validWithDTrs, goalId, proof, proofLamTerm, atomVals, etoms) ←
      callMkMVar_checker exportInhs exportFacts
    LamReif.newAssertion proof (.leaf "by_native::queryNative") proofLamTerm
    let etomInstantiated ← LamReif.validOfInstantiateForall (.valid [] proofLamTerm) (etoms.map .etom)
    let forallElimed ← LamReif.validOfElimForalls etomInstantiated exportInhs
    let contra ← LamReif.validOfImps forallElimed exportFacts
    LamReif.printProofs
    Reif.setDeclName? declName?
    let checker ← LamReif.buildCheckerExprFor contra
    let contra ← Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]
    let (goalFVars, goalId) ← goalId.introN (atomVals.size + etoms.size)
    let (goalCtx, goalId) ← goalId.introN (exportInhs.size + exportFacts.size)
    let goalCtxWithDeriv := goalCtx.zip ((nonemptyWithDTrs ++ validWithDTrs).map Prod.snd)
    return (contra, goalId, goalFVars.zip atomVals, goalCtxWithDeriv)

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
