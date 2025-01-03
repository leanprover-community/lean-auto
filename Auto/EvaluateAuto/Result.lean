import Lean
open Lean

namespace EvalAuto

inductive Result
  | success
  | nonProp
  | typeCheckFail
  | typeUnequal
  -- `auto` does not produce subgoals, but other tactics we test might (such as `simp`)
  | subGoals
  | exception (e : Exception)

instance : ToMessageData Result where
  toMessageData : Result → MessageData
  | .success         => "Result.success"
  | .nonProp         => "Result.nonProp"
  | .typeCheckFail   => "Result.typeCheckFail"
  | .typeUnequal     => "Result.typeUnequal"
  | .subGoals        => "Result.subGoals"
  | .exception e     => m!"Result.exception ::\n{e.toMessageData}"

def Result.concise : Result → String
| .success => "S"
| .nonProp => "N"
| .typeCheckFail => "F"
| .typeUnequal => "U"
| .subGoals => "G"
| .exception _ => "E"


open Elab Tactic in
/--
  Run `tactic` on a metavariable with type `e` and obtain the result
-/
def Result.ofTacticOnExpr (e : Expr) (tactic : TacticM Unit) : TermElabM Result := do
  let .mvar mid ← Meta.mkFreshExprMVar e
    | throwError "{decl_name%} : Unexpected error"
  let result : List MVarId ⊕ Exception ← tryCatchRuntimeEx
    (do let goals ← Term.TermElabM.run' (Tactic.run mid tactic) {}; return .inl goals)
    (fun e => return .inr e)
  match result with
  | .inl goals =>
    if goals.length >= 1 then
      return .subGoals
    let proof ← instantiateMVars (.mvar mid)
    match Kernel.check (← getEnv) {} proof with
    | Except.ok autoProofType =>
      match Kernel.isDefEq (← getEnv) {} autoProofType e with
      | Except.ok true => return .success
      | _ => return .typeUnequal
    | Except.error _ => return .typeCheckFail
  | .inr e => return (.exception e)

end EvalAuto
