import Lean
import Auto.Lib.ExprExtra
open Lean Meta Elab

initialize
  registerTraceClass `auto.metaExtra

namespace Auto

def Meta.isDefEqD (t s : Expr) : MetaM Bool := Meta.withDefault <| Meta.isDefEq t s

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
    | throwError "{decl_name%} :: {e} is not a type"
  try
    if let .some inh ← Meta.synthInstance? e then
      return .some inh
    if let .some inh ← Meta.synthInstance? (Lean.mkApp (.const ``Inhabited [lvl]) e) then
      return .some (Lean.mkApp2 (.const ``Inhabited.default [lvl]) e inh)
    if let .some inh ← Meta.synthInstance? (Lean.mkApp (.const ``Nonempty [lvl]) e) then
      return .some (Lean.mkApp2 (.const ``Classical.choice [lvl]) e inh)
    return .none
  catch _ =>
    return .none

syntax (name := fromMetaTactic) "fromMetaTactic" "[" ident "]" : tactic

@[tactic fromMetaTactic]
unsafe def evalFromMetaTactic : Tactic.Tactic
| `(fromMetaTactic | fromMetaTactic [ $i ]) => do
  let some iexpr ← Term.resolveId? i
    | throwError "{decl_name%} :: Unknown identifier {i}"
  let mtname := iexpr.constName!
  let Except.ok mt := (← getEnv).evalConst (MVarId → MetaM (List MVarId)) (← getOptions) mtname
    | throwError "{decl_name%} :: Failed to evaluate {mtname} to a term of type (Expr → TermElabM Unit)"
  Tactic.liftMetaTactic mt
| _ => Elab.throwUnsupportedSyntax

-- **-TODO: Deal with mutual dependencies between mvar and fvar**
-- **-      Maybe inspect the LocalContext in the metavariable declaration**
def Meta.abstractAllMVarFVar (e : Expr) : MetaM Expr := do
  let mut curr := e
  -- **TODO: Fix**
  while true do
    let next ← instantiateMVars (← zetaReduce curr)
    if next == curr then
      break
    curr := next
  let e := curr
  -- Now `(e == (← instantiateMVars) e) && (e == (← zetaReduce e))`
  let res ← Meta.abstractMVars (levels := false) e
  -- Now expr mvars in `e` are abstracted
  let mut e := res.expr
  -- **TODO: Fix**
  while true do
    let (_, collectFVarsState) ← e.collectFVars.run {}
    -- Now free variables in `e` are abstracted
    e ← mkLambdaFVars (collectFVarsState.fvarIds.map Expr.fvar) e
    if !e.hasFVar then
      break
  let res ← Meta.abstractMVars (levels := true) e
  -- Now level mvars in `e` are abstracted
  -- Level mvars must be abstracted after fvars are abstracted,
  --   because they may occur in fvars
  return res.expr

def Meta.coreCheck (e : Expr) : MetaM (Option Expr) := do
  let e ← Meta.abstractAllMVarFVar e
  match Kernel.check (← getEnv) {} e with
  | Except.ok type => return .some type
  | Except.error _ => return .none

def Meta.isTypeCorrectCore (e : Expr) : MetaM Bool := do
  let type? ← Meta.coreCheck e
  return type?.isSome

def Meta.withMaxHeartbeats [Monad m] [MonadLiftT BaseIO m]
    [MonadWithReaderOf Core.Context m] (n : Nat) (x : m α) : m α := do
  let numHeartbeats ← IO.getNumHeartbeats
  let f s := {
    s with
    initHeartbeats := numHeartbeats
    maxHeartbeats := n * 1000
  }
  withReader f x

def Meta.exToExcept (x : MetaM α) : MetaM (Except Exception α) :=
  try
    let v ← x
    return .ok v
  catch e =>
    return .error e

def Meta.runtimeExToExcept (x : MetaM α) : MetaM (Except Exception α) :=
  tryCatchRuntimeEx (do let v ← x; return .ok v) (fun e => return .error e)

end Auto
