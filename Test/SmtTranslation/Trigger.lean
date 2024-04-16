import Auto.Tactic
import Auto.Embedding.LamBase

set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.unsatCore true
-- set_option auto.smt.save true
-- set_option auto.smt.savepath "output.smt2"

set_option auto.smt true

axiom f : Int -> Int

open Auto.SMT.Attribute
axiom fGreater : forall x, trigger (f x) (f x > x)

theorem fPlusOneGreater : forall x, (f x) + 1 > x := by auto [fGreater] u[]
