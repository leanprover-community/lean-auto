namespace Auto

theorem Bool.beq_refl {a : Bool} : a == a := by
  cases a <;> rfl

theorem Bool.eq_of_beq_eq_true {a b : Bool} (h : a == b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem Bool.eq_false_of_ne_true {a : Bool} : a ≠ true → a = false := by
  cases a <;> decide

theorem Bool.ne_true_of_eq_false {a : Bool} : a = false → a ≠ true := by
  cases a <;> decide

theorem Bool.eq_false_eq_not_eq_true {a : Bool} : (a ≠ true) = (a = false) := by
  cases a <;> decide

theorem Bool.and_comm {a b : Bool} : (a && b) = (b && a) := by
  cases a <;> cases b <;> decide

theorem Bool.or_comm {a b : Bool} : (a || b) = (b || a) := by
  cases a <;> cases b <;> decide

end Auto