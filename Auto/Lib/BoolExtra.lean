namespace Auto

theorem Bool.beq_true {a : Bool} : (a == true) = a := by
  cases a <;> rfl

theorem Bool.beq_false {a : Bool} : (a == false) = !a := by
  cases a <;> rfl

theorem Bool.not_beq_swap {a b : Bool} : (!a == b) = (a == !b) := by
  cases a <;> cases b <;> decide

theorem Bool.eq_false_of_ne_true {a : Bool} : a ≠ true → a = false := by
  cases a <;> decide

theorem Bool.ne_true_of_eq_false {a : Bool} : a = false → a ≠ true := by
  cases a <;> decide

theorem Bool.eq_false_eq_not_eq_true {a : Bool} : (a ≠ true) = (a = false) := by
  cases a <;> decide

theorem Bool.and_eq_false (a b : Bool) : ((a && b) = false) = ((a = false) ∨ (b = false)) := by
  cases a <;> cases b <;> decide

theorem Bool.or_eq_false (a b : Bool) : ((a || b) = false) = ((a = false) ∧ (b = false)) := by
  cases a <;> cases b <;> decide

theorem Bool.and_comm {a b : Bool} : (a && b) = (b && a) := by
  cases a <;> cases b <;> decide

theorem Bool.or_comm {a b : Bool} : (a || b) = (b || a) := by
  cases a <;> cases b <;> decide

noncomputable def Bool.ofProp (c : Prop) : Bool :=
  match Classical.propDecidable c with
  | .isTrue _ => true
  | .isFalse _ => false

theorem Bool.ofProp_spec (c : Prop) : Bool.ofProp c ↔ c := by
  dsimp [ofProp]
  cases h : Classical.propDecidable c <;> simp [*]

theorem Bool.ofProp_spec' (c : Prop) : Bool.ofProp c = false ↔ ¬ c := by
  conv => enter [2, 1]; rw [← Bool.ofProp_spec c]
  simp

/--
  Similar to `Bool.cond`, but allows `Prop` argument
-/
def Bool.cond' {α : Sort u} (b : Bool) (x y : α) :=
  match b with
  | true => x
  | false => y

theorem Bool.ite_eq_true (p : Prop) [inst : Decidable p] (a b : α) : p → ite p a b = a := by
  intro hp; dsimp [ite]; cases inst
  case isFalse hnp => apply False.elim (hnp hp)
  case isTrue _ => rfl

theorem Bool.ite_eq_false (p : Prop) [inst : Decidable p] (a b : α) : ¬ p → ite p a b = b := by
  intro hnp; dsimp [ite]; cases inst
  case isFalse _ => rfl
  case isTrue hp => apply False.elim (hnp hp)

/--
  Invoke `simp_only` at the beginning of `auto`
-/
theorem Bool.ite_simp {α : Sort u} (p : Prop) [Decidable p] (x y : α) :
  ite p x y = cond' (Bool.ofProp p) x y := by
  cases h : Bool.ofProp p
  case false => rw [Bool.ite_eq_false]; rfl; apply (Bool.ofProp_spec' _).mp h
  case true  => rw [Bool.ite_eq_true]; rfl; apply (Bool.ofProp_spec _).mp h

/--
  Invoke `simp_only` at the beginning of `auto`
-/
theorem Bool.decide_simp (p : Prop) [Decidable p] : decide p = Bool.ofProp p := by
  cases h : Bool.ofProp p
  case false => rw [decide_eq_false]; apply (Bool.ofProp_spec' _).mp h
  case true  => rw [decide_eq_true]; apply (Bool.ofProp_spec _).mp h

end Auto