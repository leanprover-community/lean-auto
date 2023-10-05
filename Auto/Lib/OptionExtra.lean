namespace Auto

@[always_inline, inline] def Option.allp (p : α → Prop) : Option α → Prop
  | some a => p a
  | none   => True

theorem Option.all_allp (p : α → Bool) (x : Option α) :
  (x.all p = true) = Option.allp (fun x => p x = true) x :=
  match x with
  | .none => by
    dsimp [Option.all, Option.allp]; simp
  | .some x => by
    dsimp [Option.all, Option.allp]

theorem Option.allp_uniform (p : α → Prop) (x : Option α) :
  (∀ (x : α), p x) → Option.allp p x := by
  cases x <;> intro h
  case none => exact True.intro
  case some v => apply h

theorem Option.isNone_eq_not_isSome {x : Option α} : x.isNone = !x.isSome := by
  cases x <;> rfl

theorem Option.isSome_eq_not_isNone {x : Option α} : x.isSome = !x.isNone := by
  cases x <;> rfl

theorem Option.beq_none_none [BEq α] : (none (α:=α) == none) = true := rfl

theorem Option.beq_none_some [BEq α] : (none (α:=α) == some x) = false := rfl

theorem Option.beq_some_none [BEq α] : (some (α:=α) x == none) = false := rfl

theorem Option.beq_some_some [BEq α] : (some (α:=α) x == some y) = (x == y) := rfl

theorem Option.beq_refl [BEq α] (α_beq_refl : ∀ (x : α), x == x)
  {x : Option α} : x == x := by
  cases x
  case none => rfl
  case some => rw [beq_some_some]; rw [α_beq_refl]

theorem Option.eq_of_beq_eq_true [BEq α] (α_eq_of_beq_eq_true : ∀ (x y : α), ((x == y) = true) → x = y)
  {x y : Option α} (H : (x == y) = true) : x = y := by
  cases x <;> cases y <;> try cases H <;> try rfl
  rw [beq_some_some (α:=α)] at H; apply congrArg; apply α_eq_of_beq_eq_true _ _ H

end Auto