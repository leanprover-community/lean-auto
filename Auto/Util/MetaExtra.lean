import Lean
open Lean Meta Elab

namespace Auto.Util

def Meta.withoutMVarAssignments (m : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  Meta.withMCtx {mctx with eAssignment := {}, lAssignment := {}} m

-- Given a list of non-dependent types `ty₁, ty₂, ⋯, tyₙ`, add
--   free variables `x₁ : ty₁, x₂ : ty₂, ⋯, xₙ : tyₙ` into local context,
--   and supply `#[x₁, x₂, ⋯, xₙ]` to `cont`
private def Meta.withHypsImp (tys : Array Expr) (cont : Array FVarId → MetaM α) : MetaM α :=
  let aux (ty : Expr) (cont : Array FVarId → MetaM α) (arr : Array FVarId) : MetaM α :=
    withLocalDeclD `_ ty fun fvar => cont (arr.push fvar.fvarId!)
  let cont' := tys.reverse.foldl (β := Array FVarId → MetaM α) (fun cont ty => aux ty cont) cont
  cont' #[]

def Meta.withHyps [Monad n] [MonadControlT MetaM n] (tys : Array Expr) (k : Array FVarId → n α) : n α :=
  map1MetaM (fun k => withHypsImp tys k) k

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