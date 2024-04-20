import Auto.Tactic

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"
-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport-fo"
set_option auto.tptp.zeport.path "/home/indprinciple/Programs/zipperposition/portfolio"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
set_option auto.native.solver.func "Auto.Solver.Native.emulateNative"

set_option auto.native true
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

-- set_option auto.tptp true
-- set_option trace.auto.tptp.premiseSelection true

set_option trace.auto.mono true

example (h1 : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0) (h2 : 3 > 0) : ∃ z : Fin 3, z.1 = 0 := by
  auto

example : @Auto.Embedding.forallF Nat = @Auto.Embedding.forallF Nat := by
  auto
