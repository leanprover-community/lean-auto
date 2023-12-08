import Auto.Tactic

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

theorem Zone.MinArea1.spec :
  Zone.MinArea1 .Z1 = 10000 ∧ Zone.MinArea1 .Z2 = 5000 ∧
  Zone.MinArea1 .Z3 = 3500 ∧ Zone.MinArea1 .Z4 = 2500 := by simp

example (x : Zone) : x.MinArea1 >= 2500 := by cases x <;> simp -- succeeds
example (x : Zone) : x.MinArea1 >= 2500 := by auto [Zone.MinArea1.spec]

def Zone.MinArea2 : Zone → Area
  | .Z1 => 0
  | .Z2 => 5000
  | .Z3 => 6500
  | .Z4 => 7500

theorem Zone.MinArea2.spec :
  Zone.MinArea2 .Z1 = 0 ∧ Zone.MinArea2 .Z2 = 5000 ∧
  Zone.MinArea2 .Z3 = 6500 ∧ Zone.MinArea2 .Z4 = 7500 := by simp

example (x : Zone) : x.MinArea1 + x.MinArea2 = 10000 := by
  auto [Zone.MinArea1.spec, Zone.MinArea2.spec]
example (x : Zone) (_ : x = .Z1) : x.MinArea1 = 10000 && x.MinArea2 = 0 := by
  auto [*, Zone.MinArea1.spec, Zone.MinArea2.spec]

#declare_lemdb zone_spec
open Zone in
attribute [lemdb zone_spec] MinArea1.spec MinArea2.spec

example (x : Zone) : x.MinArea1 + x.MinArea2 = 10000 := by
  auto [*zone_spec]

example (x : Zone) : x.MinArea1 >= 2500 && x.MinArea2 <= 7500 := by
  auto [*zone_spec]

def Nat.op1 : Nat → Nat
| 0 => 10
| _ + 1 => 2

theorem Nat.op1.spec : Nat.op1 0 = 10 ∧ Nat.op1 (.succ n) = 2 := And.intro rfl rfl

def Nat.op2 (n : Nat) : Nat :=
  if n < 10 then 10 else n

theorem Nat.op2.spec : (n < 10 → Nat.op2 n = 10) ∧ (n >= 10 → Nat.op2 n = n) := by
  apply And.intro <;> intro h <;> unfold op2
  case left => simp [h]
  case right => simp [Nat.not_lt_of_le h]

#declare_lemdb op_spec
attribute [lemdb op_spec] Nat.op1.spec Nat.op2.spec

example : Nat.op1 n >= 2 ∧ Nat.op2 n >= 10 := by
  auto [*op_spec]

#compose_lemdb all_spec [zone_spec, op_spec]
example (x : Zone) : x.MinArea1 + x.MinArea2 = 10000 ∧ Nat.op1 n >= 2 ∧ Nat.op2 n >= 10 := by
  auto [*all_spec]
