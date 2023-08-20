namespace Auto

@[always_inline, inline] def Option.allp (p : α → Prop) : Option α → Prop
  | some a => p a
  | none   => True

end Auto