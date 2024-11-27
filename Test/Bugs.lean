import Auto.Tactic
import Auto.EvaluateAuto.TestCode

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
-- Emulate native solver
set_option trace.auto.native.printFormulas true
attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

set_option auto.native true
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

-- set_option auto.tptp true
-- set_option trace.auto.tptp.premiseSelection true

set_option trace.auto.mono true

/--
  h₁ : ∀ x : Nat, x > 0 → ∃ y : Fin x, @Fin.val x y = 0
  h₂ : 3 > 0
  ngoal : ¬ ∃ z : Fin 3, @Fin.val 3 z = 0

  Abstracted: fun x => ∃ y : Fin x, @Fin.val x y
-/
example
  (h₁ : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0)
  (h₂ : 3 > 0) : ∃ z : Fin 3, z.1 = 0 := by
  auto

/--
  h₁ : ∀ x : Nat, x > 0 → ∃ y : Fin x, @Fin.val x y = 0
  h₂ : 3 > 0
  ngoal : ¬ ∃ z : Fin (f 3), @Fin.val (f 3) z = 0

  Abstracted: fun x => ∃ y : Fin x, @Fin.val x y
-/
example
  (f : Nat → Nat)
  (h₁ : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0)
  (h₂ : ∀ x, f x > 0):
  ∃ z : Fin (f 3), @Fin.val (f 3) z = 0 := by
  generalize f 3 = u

section Set

  opaque Set : Type u → Type u

  opaque mem_set : ∀ {α : Type u}, Set α → (α → Prop)

  axiom setOf.{u} : ∀ (α : Type u), (α → Prop) → Set α

  axiom iUnion.{u, v} : ∀ (α : Type u) (ι : Sort v), (ι → Set α) → Set α

  axiom mem_iUion.{u, v} : ∀ {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α}, mem_set (iUnion _ _ s) x ↔ ∃ i, mem_set (s i) x

  example
    (dvd : Nat → Nat → Prop)
    (primeset : Set Nat) :
    iUnion Nat Nat (fun p => iUnion Nat (mem_set primeset p) (fun h => setOf Nat (fun x => dvd p x))) =
    setOf Nat (fun x => ∃ p, mem_set primeset p ∧ dvd p x) := by
    auto

end Set

/--
  ∃ (i : Nat) (i_1 : primeset i), dvd i x

  Abstracted : fun i f => ∃ (i_1 : primeset i), f i
-/
example (x : Nat) (primeset : Nat → Prop) (dvd : Nat → Nat → Prop) :
  ((∃ (i : _) (i_1 : primeset i), dvd i x) ↔ (∃ p, primeset p ∧ dvd p x)) := by
  auto

-- bug
set_option trace.auto.tactic true in
#eval do
  let m ← Auto.runAutoOnConst ``Nat.sub_one_lt_of_lt
  trace[auto.tactic] m!"{m}"
