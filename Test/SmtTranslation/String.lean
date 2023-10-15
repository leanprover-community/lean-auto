import Auto.Tactic

set_option auto.proofReconstruction false
set_option auto.smt true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

example : "|,\\|" = "|,\\|" := by auto

example : "&" = "&" := by auto

example (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by auto

example (a b c : String) (_ : a < b) : c ++ a < c ++ b := by auto

example (a b c : String) (_ : Auto.String.le a b) (_ : a ≠ b) : a < b := by auto
