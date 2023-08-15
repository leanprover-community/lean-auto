import Lean
import Auto.Preprocessing
import Auto.Translation
import Auto.Solver.SMT
import Auto.HintDB
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.printLemmas

namespace Auto

-- **TODO**: Extend
syntax hintelem := term <|> "*"
syntax hints := ("[" hintelem,* "]")?
syntax autoinstr := ("@p")?
syntax (name := auto) "auto" autoinstr hints : tactic

inductive Instruction where
  | none
  | p

def parseInstr : TSyntax ``Auto.autoinstr → TacticM Instruction
| `(autoinstr|) => return .none
| `(autoinstr|@p) => return .p
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
    (Util.MessageData.array es (fun (id, e) => m!"{mkFVar id} := {e}"))
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
    let afterReify : LamReif.ReifM PUnit := (do
      let s ← get
      let assertions := s.assertions
      for (expr, lterm) in assertions do
        trace[auto.tactic] "Proof: {expr}, λ Term: {repr lterm}"
      let lamVarTy := s.lamVarTy
      for (id, lams) in lamVarTy do
        trace[auto.tactic] "FVar: {Expr.fvar id}, λ Sort: {repr lams}"
      let commands := (← (lamFOL2SMT s).run {}).1
      let _ ← liftM <| commands.mapM (fun c => IO.println s!"Command: {c}")
      Solver.SMT.querySolver commands)
    let afterMonomorphization : Reif.ReifM Unit := (do
      let ufacts ← liftM <| Reif.getFacts
      ((LamReif.uLiftAndReify ufacts afterReify).run' {}).run')
    Monomorphization.collectPolyLog (fun hmap mfacts =>
      let hmaprev := hmap.toList.foldl (fun hm (key, val) => hm.insert val key) HashMap.empty
      -- Skipping monomorphization
      afterMonomorphization.run' { facts := mfacts, iPolyLog := hmaprev })
      (lemmas.map (fun x => (x.proof, x.type)))
    throwError "runAuto :: Not implemented"
    -- testing
  | .p =>
    let types := lemmas.map (fun x => x.type)
    let PState := (← (types.mapM (fun e => do
        PReif.addAssertion (ω := Expr) (← D2P e))).run {}).2
    let commands := (← (P2SMT PState).run {}).1
    let _ ← liftM <| commands.mapM (fun c => IO.println s!"Command: {c}")
    Solver.SMT.querySolver commands
    throwError "runAuto :: Not implemented"

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
      IO.println s!"Unsat. Time: {(← IO.monoMsNow) - startTime}"
      throwError "Unsat"
    | Result.sat assig => throwError "Sat"
    | Result.unknown => throwError "Unknown"
| _ => throwUnsupportedSyntax

end Auto