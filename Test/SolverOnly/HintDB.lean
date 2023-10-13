import Lean
import Auto.HintDB

namespace Space1

#declare_hintdb testdb

@[hintdb testdb] def test₁ := 2

@[hintdb testdb] def test₂ := 2

end Space1

attribute [hintdb testdb] Nat.add_comm

#print_hintdb testdb



#declare_hintdb logic

attribute [hintdb logic] Or.inl Or.inr

#declare_hintdb arith

attribute [hintdb arith] Nat.add_comm Nat.add_assoc

#compose_hintdb arithlogic [arith, logic]

#print_hintdb arithlogic

attribute [hintdb arith] Nat.mul_assoc

#print_hintdb arithlogic

#check ULift Nat