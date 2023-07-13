import Lean
open Lean Meta Elab

namespace Auto.Util

def Meta.withoutMVarAssignments (m : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  Meta.withMCtx {mctx with eAssignment := {}, lAssignment := {}} m

initialize Lean.registerTraceClass `Meta.inspectMVarAssignments

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
    trace[Meta.inspectMVarAssignments] .compose "ExprMVar Assignments: " (← composeAssignMessage ems)
    let lms := lAssignmentList.map (fun (id, l) => MessageData.compose m!"{Level.mvar id} := " m!"{l}")
    trace[Meta.inspectMVarAssignments] .compose "LevelMVar Assignments: " (← composeAssignMessage lms)

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

end Auto.Util