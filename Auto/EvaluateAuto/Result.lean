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

end EvalAuto
