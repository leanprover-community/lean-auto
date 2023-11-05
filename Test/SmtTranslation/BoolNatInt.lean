import Auto.Tactic

set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

set_option auto.smt true

example (a : Nat) : a = a := by auto

example : nat_lit 2 = 2 := by auto

example : max 3 4 = 4 ∧ min 1 2 = 1 := by auto

example : (2 : Int) = ((nat_lit 2) : Int) := by auto

example : max (-3) 4 = 4 ∧ min 1 (-2) = -2 := by auto

example {α β : Type} (f : α → Nat → β → α → Nat) :
  ∀ a b c, f a 1 b c = f a 1 b c := by auto

example {α : Type} (f : α → Nat → Nat → α → Nat) :
  ∀ a b c, f a 1 b c = f a 1 b c := by auto

example (a b : Nat) (_ : a ≤ b) : a - b = 0 := by auto

example : Nat.succ x = x + 1 := by auto

example : String.length "abc" = 3 := by auto

example (_ : ∃ b, !(!b) ≠ b) : False := by auto

-- Mixed integer-bool
example {a b c d : Bool} (h : if (if (2 < 3) then a else b) then c else d) :
  (a → c) ∧ (¬ a → d) := by auto

example {a : Bool} : decide a = a := by auto

#check Lean.Elab.Command.elabStructure
