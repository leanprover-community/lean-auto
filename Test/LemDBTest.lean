import Auto.Tactic
import Std.Data.BitVec
set_option auto.smt true
set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

inductive Zone where
  | Z1 | Z2 | Z3 | Z4
  -- Ask Lean to automatically show that type is not empty, has a representation function, and
  -- equality is decidable
  deriving Inhabited, Repr, DecidableEq

abbrev Area : Type := Int

def Zone.MinArea1 : Zone → Area
  | .Z1 => 10000
  | .Z2 => 5000
  | .Z3 => 3500
  | .Z4 => 2500

theorem Zone.MinArea1.defeq :
  Zone.MinArea1 .Z1 = 10000 ∧ Zone.MinArea1 .Z2 = 5000 ∧
  Zone.MinArea1 .Z3 = 3500 ∧ Zone.MinArea1 .Z4 = 2500 := by simp

example (x : Zone) : x.MinArea1 >= 2500 := by cases x <;> simp -- succeeds
example (x : Zone) : x.MinArea1 >= 2500 := by auto [Zone.MinArea1.defeq]

def Zone.MinArea2 : Zone → Area
  | .Z1 => 0
  | .Z2 => 5000
  | .Z3 => 6500
  | .Z4 => 7500

theorem Zone.MinArea2.defeq :
  Zone.MinArea2 .Z1 = 0 ∧ Zone.MinArea2 .Z2 = 5000 ∧
  Zone.MinArea2 .Z3 = 6500 ∧ Zone.MinArea2 .Z4 = 7500 := by simp

example (x : Zone) : x.MinArea1 + x.MinArea2 = 10000 := by
  auto [Zone.MinArea1.defeq, Zone.MinArea2.defeq]
example (x : Zone) (_ : x = .Z1) : x.MinArea1 = 10000 && x.MinArea2 = 0 := by
  auto [*, Zone.MinArea1.defeq, Zone.MinArea2.defeq]

#declare_lemdb zone_defeq
open Zone in
attribute [lemdb zone_defeq] MinArea1.defeq MinArea2.defeq

example (x : Zone) : x.MinArea1 + x.MinArea2 = 10000 := by
  auto [*zone_defeq]

example (x : Zone) : x.MinArea1 >= 2500 && x.MinArea2 <= 7500 := by
  auto [*zone_defeq]
