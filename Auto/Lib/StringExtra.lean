namespace Auto

@[reducible] def String.le (a b : String) : Prop := a = b ∨ a < b

@[reducible] def String.ge (a b : String) : Prop := a = b ∨ b < a

def String.lt (a b : String) : Prop := a < b

def String.gt (a b : String) : Prop := b < a

end Auto