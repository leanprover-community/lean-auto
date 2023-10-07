import Lean
import Auto.Lib.ExprExtra
open Lean Meta Elab

initialize
  registerTraceClass `auto.metaExtra

namespace Auto

def Meta.withoutMVarAssignments (m : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  Meta.withMCtx {mctx with eAssignment := {}, lAssignment := {}} m

initialize
  registerTraceClass `auto.inspectMVarAssignments

def Meta.inspectMVarAssignments : MetaM Unit := do
  let mctx ← getMCtx
  let eAssignmentList := mctx.eAssignment.toList
  let lAssignmentList := mctx.lAssignment.toList
  let composeAssignMessage (ms : List MessageData) : MetaM MessageData := do
    let mut rm := m!"["
    let mut fst := true
    for m in ms do
      if fst then
        fst := false
      else
        rm := .compose rm m!", "
      rm := .compose rm m
    return .compose rm "]"
  Meta.withMCtx {mctx with eAssignment := {}, lAssignment := {}} <| do
    let ems := eAssignmentList.map (fun (id, e) => MessageData.compose m!"{Expr.mvar id} := " m!"{e}")
    trace[auto.inspectMVarAssignments] .compose "ExprMVar Assignments: " (← composeAssignMessage ems)
    let lms := lAssignmentList.map (fun (id, l) => MessageData.compose m!"{Level.mvar id} := " m!"{l}")
    trace[auto.inspectMVarAssignments] .compose "LevelMVar Assignments: " (← composeAssignMessage lms)

/-- Synthesize inhabited instance for a given type -/
def Meta.trySynthInhabited (e : Expr) : MetaM (Option Expr) := do
  let eSort ← Expr.normalizeType (← instantiateMVars (← Meta.inferType e))
  let .sort lvl := eSort
    | throwError "trySynthInhabited :: {e} is not a type"
  try
    if let .some inh ← Meta.synthInstance? e then
      return .some inh
  catch _ =>
    pure .unit
  if let .some inh ← Meta.synthInstance? (Lean.mkApp (.const ``Inhabited [lvl]) e) then
    return .some (Lean.mkApp2 (.const ``Inhabited.default [lvl]) e inh)
  if let .some inh ← Meta.synthInstance? (Lean.mkApp (.const ``Nonempty [lvl]) e) then
    return .some (Lean.mkApp2 (.const ``Classical.choice [lvl]) e inh)
  return .none

syntax (name := fromMetaTactic) "fromMetaTactic" "[" ident "]" : tactic

@[tactic fromMetaTactic]
unsafe def evalFromMetaTactic : Tactic.Tactic
| `(fromMetaTactic | fromMetaTactic [ $i ]) => do
  let some iexpr ← Term.resolveId? i
    | throwError "evalFromMetaTactic :: Unknown identifier {i}"
  let mtname := iexpr.constName!
  let Except.ok mt := (← getEnv).evalConst (MVarId → MetaM (List MVarId)) (← getOptions) mtname
    | throwError "evalFromMetaTactic :: Failed to evaluate {mtname} to a term of type (Expr → TermElabM Unit)"
  Tactic.liftMetaTactic mt
| _ => Elab.throwUnsupportedSyntax

/-- We assume that `value` contains no free variables or metavariables -/
def Meta.exprAddAndCompile (value : Expr) (declName : Name) : MetaM Unit := do
  let type ← inferType value
  let us := collectLevelParams {} value |>.params
  let decl := Declaration.defnDecl {
    name        := declName
    levelParams := us.toList
    type        := type
    value       := value
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.unsafe
  }
  addDecl decl

def Meta.coreCheck (e : Expr) : MetaM Unit := do
  let startTime ← IO.monoMsNow
  let mut curr := e
  -- **TODO: Fix**
  while true do
    let next ← instantiateMVars (← zetaReduce curr)
    if next == curr then
      break
    curr := next
  let e := curr
  -- Now `(e == (← instantiateMVars) e) && (e == (← zetaReduce e))`
  let res ← Meta.abstractMVars e
  -- Now metavariables in `e` are abstracted
  let mut e := res.expr
  -- **TODO: Fix**
  while true do
    let (_, collectFVarsState) ← e.collectFVars.run {}
    -- Now free variables in `e` are abstracted
    e ← mkLambdaFVars (collectFVarsState.fvarIds.map Expr.fvar) e
    if !e.hasFVar then
      break
  -- Use `Core.addAndCompile` to typecheck `e`
  let coreChkStart ← IO.monoMsNow
  trace[auto.metaExtra] "Meta.coreCheck :: Preprocessing done in {coreChkStart - startTime}"
  let env ← getEnv
  try
    Meta.exprAddAndCompile e `_coreCheck
  finally
    trace[auto.metaExtra] "Meta.coreCheck :: Core check done in {(← IO.monoMsNow) - coreChkStart}"
    setEnv env

def Meta.isTypeCorrectCore (e : Expr) : MetaM Bool := do
  try
    Meta.coreCheck e
    pure true
  catch e =>
    let msg := MessageData.compose "Meta.isTypeCorrectCore failed with message : \n" e.toMessageData
    trace[auto.metaExtra] msg
    pure false

end Auto