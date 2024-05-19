namespace Auto.LamCstrD

abbrev Nat.modEq (n a b : Nat) := a % n = b % n
abbrev Nat.ge (x y : Nat) := Nat.le y x
abbrev Nat.gt (x y : Nat) := Nat.lt y x
abbrev Nat.max (x y : Nat) : Nat := Max.max x y
abbrev Nat.min (x y : Nat) : Nat := Min.min x y
abbrev Int.modEq (n a b : Int) := a % n = b % n
abbrev Int.ge (a b : Int) := Int.le b a
abbrev Int.gt (a b : Int) := Int.lt b a
abbrev Int.max (x y : Int) : Int := Max.max x y
abbrev Int.min (x y : Int) : Int := Min.min x y
abbrev String.ge (a b : String) : Prop := b = a ∨ b < a
abbrev String.gt (a b : String) : Prop := b < a
abbrev BitVec.uge (a b : BitVec n) : Bool := BitVec.ule b a
abbrev BitVec.ugt (a b : BitVec n) : Bool := BitVec.ult b a
abbrev BitVec.sge (a b : BitVec n) : Bool := BitVec.sle b a
abbrev BitVec.sgt (a b : BitVec n) : Bool := BitVec.slt b a
abbrev BitVec.propule (a b : BitVec n) : Prop := a.toFin <= b.toFin
abbrev BitVec.propult (a b : BitVec n) : Prop := a.toFin < b.toFin
abbrev BitVec.propsle (a b : BitVec n) : Prop := a.toInt <= b.toInt
abbrev BitVec.propslt (a b : BitVec n) : Prop := a.toInt < b.toInt
abbrev BitVec.propuge (a b : BitVec n) : Prop := BitVec.propule b a
abbrev BitVec.propugt (a b : BitVec n) : Prop := BitVec.propult b a
abbrev BitVec.propsge (a b : BitVec n) : Prop := BitVec.propsle b a
abbrev BitVec.propsgt (a b : BitVec n) : Prop := BitVec.propslt b a
abbrev BitVec.smtHshiftLeft (a : BitVec n) (b : BitVec m) := BitVec.shiftLeft a b.toNat
abbrev BitVec.smtHushiftRight (a : BitVec n) (b : BitVec m) := BitVec.ushiftRight a b.toNat
abbrev BitVec.smtHsshiftRight (a : BitVec n) (b : BitVec m) := BitVec.sshiftRight a b.toNat

end Auto.LamCstrD
