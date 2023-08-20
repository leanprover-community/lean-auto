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

end Auto