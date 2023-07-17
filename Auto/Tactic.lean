import Lean
import Auto.Preprocessing
import Auto.Translation
import Auto.Solver.SMT
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.printLemmas

namespace Auto

-- **TODO**: Extend
syntax hintelem := term
syntax hints := ("[" hintelem,* "]")?
syntax (name := auto) "auto" hints : tactic

def parseHintElem : TSyntax ``hintelem → TacticM Term
  | `(hintelem| $t:term) => return t
  | _ => throwUnsupportedSyntax

-- Parse `hints` to an array of `Term`, which is still syntax
def parseHints : TSyntax ``hints → TacticM (Array Term)
  | `(hints| [ $[$hs],* ]) => hs.mapM parseHintElem
  | `(hints| ) => return #[]
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

def collectLctxLemmas : TacticM (Array Lemma) := do
  let mut lemmas := #[]
  for fVarId in (← getLCtx).getFVarIds do
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

def runAuto (stx : TSyntax ``hints) : TacticM Result := do
  let lctxLemmas ← collectLctxLemmas
  traceLemmas "Lemmas collected from local context:" lctxLemmas
  let userLemmas ← collectUserLemmas (← parseHints stx)
  traceLemmas "Lemmas collected from user-provided terms:" userLemmas
  let lemmas := lctxLemmas ++ userLemmas
  -- testing
  let types := lemmas.map (fun x => x.type)
  let PState := (← (types.mapM (fun e => do
      ReifP.addAssertion (ω := Expr) (← D2P e))).run {}).2
  let commands := (← (P2SMT PState).run {}).1
  let _ ← liftM <| commands.mapM (fun c => IO.println s!"Command: {c}")
  Solver.SMT.querySolver commands
  -- testing
  throwError "runAuto :: Not implemented"

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $hints) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  -- Then, apply `Classical.byContradiction` to change the goal into `False`
  --  and put `¬ G` into the local context
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  -- Now the main goal has changed
  withMainContext do
    let result ← runAuto hints
    match result with
    | Result.unsat e => do
      IO.println s!"Unsat. Time: {(← IO.monoMsNow) - startTime}"
      throwError "Unsat"
    | Result.sat assig => throwError "Sat"
    | Result.unknown => throwError "Unknown"
| _ => throwUnsupportedSyntax

end Auto