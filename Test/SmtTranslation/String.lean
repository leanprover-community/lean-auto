import Auto.Tactic

set_option auto.smt true
set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.duper false

example : "|,\\|" = "|,\\|" := by auto

example : "&" = "&" := by auto

example (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by auto

set_option auto.smt.solver.name "cvc5" in
example (a b c : String) (_ : a < b) : c ++ a < c ++ b := by auto

example (a b : String) (_ : Auto.String.le a b) (_ : a ≠ b) : a < b := by auto

example : String.length "abc" = 3 := by auto

example : String.isPrefixOf "ab" "abcd" := by auto

example : String.replace "aaaaa" "aa" "ba" = "babaa" := by auto
