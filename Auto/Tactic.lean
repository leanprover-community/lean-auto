import Lean
import Auto.Preprocessing
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic

namespace Auto

syntax hints := ("[" term,* "]")?
syntax (name := auto) "auto" hints : tactic

-- Parse `hints` to an array of `Term`, which is still syntax
def parseHints : TSyntax ``hints → TacticM (Array Term)
  | `(hints| [ $[$hs],* ]) => return hs
  | `(hints| ) => return #[]
  | _ => throwUnsupportedSyntax

inductive Result where
  -- Unsatisfiable, witnessed by `e`
  | unsat : (e : Expr) → Result
  -- Satisfiable, witnessed by an assignment to free variables
  | sat : (es : Array (FVarId × Expr)) → Result
  -- Unknown
  | unknown : Result

def collectLctxLemmas : TacticM (Array Lemma) := do
  let mut lemmas := #[]
  for fVarId in (← getLCtx).getFVarIds do
    let decl ← FVarId.getDecl fVarId
    if ¬ decl.isAuxDecl ∧ (← instantiateMVars decl.type).isProp then
      let declType ← Prep.preprocessTerm (← instantiateMVars decl.type)
      lemmas := lemmas.push ⟨mkFVar fVarId, declType, #[]⟩
  return lemmas

def collectUserLemmas (terms : Array Term) : TacticM (Array Lemma) := do
  let mut lemmas := #[]
  for lems in ← terms.mapM Prep.elabLemma do
    for ⟨proof, type, params⟩ in lems do
      if ← Meta.isProp type then
        let type ← Prep.preprocessTerm (← instantiateMVars type)
        -- **TODO**: Instantiate mvars in proof?
        lemmas := lemmas.push ⟨proof, type, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
  return lemmas

def runAuto (stx : TSyntax ``hints) : TacticM Result := do
  let lctxAssumptions ← collectLctxLemmas
  let userAssumptions ← collectUserLemmas (← parseHints stx)
  sorry

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