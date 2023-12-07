import Auto
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


def Zone.MinArea1.defeq1 : Zone.MinArea1 .Z1 = 10000 := rfl
def Zone.MinArea1.defeq2 : Zone.MinArea1 .Z2 = 5000  := rfl
def Zone.MinArea1.defeq3 : Zone.MinArea1 .Z3 = 3500  := rfl
def Zone.MinArea1.defeq4 : Zone.MinArea1 .Z4 = 2500  := rfl

#declare_lemdb zone_defeq1
attribute[lemdb zone_defeq1] Zone.MinArea1.defeq1 Zone.MinArea1.defeq2 Zone.MinArea1.defeq3 Zone.MinArea1.defeq4

example (x: Zone) : x.MinArea1 >= 2500 := by cases x <;> simp -- succeeds
example (x: Zone) : x.MinArea1 >= 2500 := by auto [*zone_defeq1]

def Zone.MinArea2 : Zone → Area
  | .Z1 => 0
  | .Z2 => 5000
  | .Z3 => 6500
  | .Z4 => 7500

def Zone.MinArea2.defeq1 : Zone.MinArea2 .Z1 = 0 := rfl
def Zone.MinArea2.defeq2 : Zone.MinArea2 .Z2 = 5000 := rfl
def Zone.MinArea2.defeq3 : Zone.MinArea2 .Z3 = 6500 := rfl
def Zone.MinArea2.defeq4 : Zone.MinArea2 .Z4 = 7500 := rfl

#declare_lemdb zone_defeq2
attribute[lemdb zone_defeq2] Zone.MinArea2.defeq1 Zone.MinArea2.defeq2 Zone.MinArea2.defeq3 Zone.MinArea2.defeq4

example (x: Zone) : x.MinArea1 + x.MinArea2 = 10000 := by
  auto [*zone_defeq1, *zone_defeq2]
example (x: Zone) (_ : x = .Z1) : x.MinArea1 = 10000 && x.MinArea2 = 0 := by
  auto [*, *zone_defeq1, *zone_defeq2]

#compose_lemdb zone_defeqAll [zone_defeq1, zone_defeq2]
example (x: Zone) : x.MinArea1 + x.MinArea2 = 10000 := by
  auto [*zone_defeqAll]
