namespace Auto

theorem Bool.eq_false_of_ne_true {a : Bool} : a ≠ true → a = false := by
  cases a <;> decide

theorem Bool.ne_true_of_eq_false {a : Bool} : a = false → a ≠ true := by
  cases a <;> decide

theorem Bool.eq_false_eq_not_eq_true {a : Bool} : (a ≠ true) = (a = false) := by
  cases a <;> decide

end Auto