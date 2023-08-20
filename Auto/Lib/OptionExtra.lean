namespace Auto

@[always_inline, inline] def Option.allp (p : α → Prop) : Option α → Prop
  | some a => p a
  | none   => True

theorem Option.p_all_eq_true (p : α → Bool) (x : Option α) :
  (x.all p = true) = Option.allp (fun x => p x = true) x :=
  match x with
  | .none => by
    dsimp [Option.all, Option.allp]; simp
  | .some x => by
    dsimp [Option.all, Option.allp]

end Auto