namespace Auto

@[reducible] def String.le (a b : String) : Prop := a = b ∨ a < b

def String.lt (a b : String) : Prop := a < b

end Auto