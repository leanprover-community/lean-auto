import Lean
import Auto.Preprocessing
import Auto.Translation
import Auto.Solver.SMT
import Auto.HintDB
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.printLemmas
  registerTraceClass `auto.printProof

namespace Auto

-- **TODO**: Extend
syntax hintelem := term <|> "*"
syntax hints := ("[" hintelem,* "]")?
syntax autoinstr := ("👍")?
syntax (name := auto) "auto" autoinstr hints : tactic

inductive Instruction where
  | none

def parseInstr : TSyntax ``Auto.autoinstr → TacticM Instruction
| `(autoinstr|) => return .none
| `(autoinstr|👍) => throwError "We appreciate your flatter 😎"
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

-- Parse `hints` to an array of `Term`, which is still syntax
-- `Array Term`
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

inductive Result where
  -- Unsatisfiable, witnessed by `e`
  | unsat : (e : Expr) → Result
  -- Satisfiable, witnessed by an assignment to free variables
  | sat : (es : Array (FVarId × Expr)) → Result
  -- Unknown
  | unknown : Result

instance : ToMessageData Result where
  toMessageData : Result → MessageData
  | .unsat e => m!"Result.unsat {e}"
  | .sat es => .compose m!"Result.sat "
    (MessageData.array es (fun (id, e) => m!"{mkFVar id} := {e}"))
  | .unknown => m!"Result.unknown"

def collectLctxLemmas (lctxhyps : Bool) (ngoal : FVarId) : TacticM (Array Lemma) := do
  let fVarIds := (if lctxhyps then (← getLCtx).getFVarIds else #[ngoal])
  let mut lemmas := #[]
  for fVarId in fVarIds do
    let decl ← FVarId.getDecl fVarId
    if ¬ decl.isAuxDecl ∧ (← Meta.isProp decl.type) then
      let declType ← Prep.preprocessTerm (← instantiateMVars decl.type)
      lemmas := lemmas.push ⟨mkFVar fVarId, declType, #[]⟩
  return lemmas

def collectUserLemmas (terms : Array Term) : TacticM (Array Lemma) := do
  let mut lemmas := #[]
  for lems in ← terms.mapM Prep.elabLemma do
    for ⟨proof, type, params⟩ in lems do
      if ← Meta.isProp type then
        let type ← Prep.preprocessTerm (← instantiateMVars type)
        lemmas := lemmas.push ⟨proof, type, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
  return lemmas

def traceLemmas (pre : String) (lemmas : Array Lemma) : TacticM Unit := do
  let mut cnt : Nat := 0
  let mut mdatas : Array MessageData := #[]
  for lem in lemmas do
    mdatas := mdatas.push m!"\n{cnt}: {lem}"
    cnt := cnt + 1
  trace[auto.printLemmas] mdatas.foldl MessageData.compose pre

-- `ngoal` means `negated goal`
def runAuto
  (instrstx : TSyntax ``autoinstr)
  (hintstx : TSyntax ``hints) (ngoal : FVarId) : TacticM Result := do
  let instr ← parseInstr instrstx
  let inputHints ← parseHints hintstx
  let lctxLemmas ← collectLctxLemmas inputHints.lctxhyps ngoal
  traceLemmas "Lemmas collected from local context:" lctxLemmas
  let userLemmas ← collectUserLemmas inputHints.terms
  traceLemmas "Lemmas collected from user-provided terms:" userLemmas
  let lemmas := lctxLemmas ++ userLemmas
  match instr with
  | .none =>
    -- Testing. Skipping universe level instantiation and monomorphization
    let afterReify (arr : Array Nat) : LamReif.ReifM Expr := (do
      let valids ← arr.mapM LamReif.lookupValidTable!
      let exportFacts := valids.map (·.2)
      for (id, lams) in (← LamReif.getVarVal) do
        trace[auto.tactic] "FVar: {Expr.fvar id}, λ Sort: {repr lams}"
      let proof ← Lam2D.callDuper exportFacts
      let proofLamTerm := exportFacts.foldr (fun t' t => t'.mkImp t) (.base .falseE)
      trace[auto.printProof] "Duper found proof {← instantiateMVars proof}"
      let imp ← LamReif.newAssertion proof (← LamReif.mkImportVersion proofLamTerm)
      let contra ← LamReif.impApps imp arr
      let checker ← LamReif.buildCheckerExpr contra
      let contra ← Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]
      Meta.mkLetFVars ((← Reif.getFvarsToAbstract).map Expr.fvar) contra
      -- let commands := (← (lamFOL2SMT (← LamReif.getVarVal) exportFacts).run {}).1
      -- let _ ← liftM <| commands.mapM (fun c => IO.println s!"Command: {c}")
      -- Solver.SMT.querySolver commands
      )
    let afterMonomorphization : Reif.ReifM Expr := (do
      let ufacts ← liftM <| Reif.getFacts
      ((LamReif.uLiftAndReify ufacts afterReify).run' {}).run')
    let proof ← Monomorphization.collectPolyLog (fun hmap mfacts =>
      let hmaprev := hmap.toList.foldl (fun hm (key, val) => hm.insert val key) HashMap.empty
      -- Skipping monomorphization
      afterMonomorphization.run' { facts := mfacts, iPolyLog := hmaprev })
      (lemmas.map (fun x => (x.proof, x.type)))
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    return .unsat proof

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $instr $hints) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  Elab.Tactic.evalTactic (← `(tactic| intros))
  let [nngoal] ← (← getMainGoal).apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let result ← runAuto instr hints ngoal
    match result with
    | Result.unsat e => do
      IO.println s!"Unsat. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      absurd.assign e
    | Result.sat assig => throwError "Sat"
    | Result.unknown => throwError "Unknown"
| _ => throwUnsupportedSyntax

end Auto