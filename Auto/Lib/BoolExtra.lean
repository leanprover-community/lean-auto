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

theorem Bool.eq_false_eq_not_eq_true {a : Bool} : (a = false) = (a ≠ true) := by
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
  cases Classical.propDecidable c <;> simp [*]

theorem Bool.ofProp_spec' (c : Prop) : Bool.ofProp c = false ↔ ¬ c := by
  conv => enter [2, 1]; rw [← Bool.ofProp_spec c]
  simp

theorem Bool.ite_eq_true (p : Prop) [inst : Decidable p] (a b : α) : p → ite p a b = a := by
  intro hp; dsimp [ite]; cases inst
  case isFalse hnp => apply False.elim (hnp hp)
  case isTrue _ => rfl

theorem Bool.ite_eq_false (p : Prop) [inst : Decidable p] (a b : α) : ¬ p → ite p a b = b := by
  intro hnp; dsimp [ite]; cases inst
  case isFalse _ => rfl
  case isTrue hp => apply False.elim (hnp hp)

theorem Bool.dite_eq_true (p : Prop) [inst : Decidable p] (a : p → α) (b : ¬ p → α) (proof : p) : dite p a b = a proof := by
  dsimp [dite]; cases inst
  case isFalse hnp => apply False.elim (hnp proof)
  case isTrue _ => rfl

theorem Bool.dite_eq_false (p : Prop) [inst : Decidable p] (a : p → α) (b : ¬ p → α) (proof : ¬ p) : dite p a b = b proof := by
  dsimp [dite]; cases inst
  case isFalse _ => rfl
  case isTrue hp => apply False.elim (proof hp)

/--
  Similar to `ite`, but does not have complicated dependent types
-/
noncomputable def Bool.ite' {α : Sort u} (p : Prop) (x y : α) :=
  match Bool.ofProp p with
  | true => x
  | false => y

/--
  Invoke `rw` at the beginning of `auto`
-/
theorem Bool.ite_simp.{u} : @ite = fun (α : Sort u) p _ => @ite' α p := by
  funext α p _ x y
  dsimp [ite']; cases h : Bool.ofProp p
  case false => rw [Bool.ite_eq_false]; apply (Bool.ofProp_spec' _).mp h
  case true  => rw [Bool.ite_eq_true]; apply (Bool.ofProp_spec _).mp h

theorem Bool.ite'_eq_true (p : Prop) (a b : α) : p → ite' p a b = a := by
  intro hp; apply Bool.ite_simp ▸ @Bool.ite_eq_true _ p (Classical.propDecidable _) a b hp

theorem Bool.ite'_eq_false (p : Prop) (a b : α) : ¬ p → ite' p a b = b := by
  intro hp; apply Bool.ite_simp ▸ @Bool.ite_eq_false _ p (Classical.propDecidable _) a b hp

/--
  Invoke `rw` at the beginning of `auto`
-/
theorem Bool.cond_simp.{u} : @cond = fun (α : Sort u) b => @ite' α (b = true) := by
  funext α b x y; cases b
  case false => rw [cond_false, Bool.ite'_eq_false]; exact Bool.false_ne_true
  case true => rw [cond_true, Bool.ite'_eq_true]; rfl

/--
  Invoke `rw` at the beginning of `auto`
-/
theorem Bool.decide_simp : @decide = fun p _ => Bool.ofProp p := by
  funext p _
  cases h : Bool.ofProp p
  case false => rw [decide_eq_false]; apply (Bool.ofProp_spec' _).mp h
  case true  => rw [decide_eq_true]; apply (Bool.ofProp_spec _).mp h

theorem Bool.ite_comm [inst : Decidable p] {x y : α} (f : α → β) : f (ite p x y) = ite p (f x) (f y) := by
  cases inst <;> rfl

theorem Bool.ite'_comm {x y : α} (f : α → β) : f (Bool.ite' p x y) = Bool.ite' p (f x) (f y) := by
  have h := @Bool.ite_comm _ _ _ (Classical.propDecidable p) x y f
  rw [Bool.ite_simp, Bool.ite_simp] at h; exact h

end Auto
