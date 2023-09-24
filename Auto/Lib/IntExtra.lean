namespace Auto

-- A version of `Nat.beq_refl` that reduces to `Eq.refl`
def Nat.beq_refl' : (a : Nat) → (a.beq a) = true
| 0 => rfl
| n + 1 => Nat.beq_refl' n

def Int.beq : Int → Int → Bool
| .ofNat n₁,   .ofNat n₂   => n₁.beq n₂
| .negSucc n₁, .negSucc n₂ => n₁.beq n₂
| _,           _           => false

def Int.beq_refl : (i : Int) → (Int.beq i i) = true
| .ofNat n => Nat.beq_refl' n
| .negSucc n => Nat.beq_refl' n

def Int.eq_of_beq_eq_true {i₁ i₂ : Int} : Int.beq i₁ i₂ → i₁ = i₂ :=
  match i₁, i₂ with
  | .ofNat n₁, .ofNat n₂ => fun H => congrArg _ (Nat.eq_of_beq_eq_true H)
  | .negSucc n₁, .negSucc n₂ => fun H => congrArg _ (Nat.eq_of_beq_eq_true H)
  | .ofNat n₁, .negSucc n₂ => fun H => by cases H
  | .negSucc n₁, .ofNat n₂ => fun H => by cases H

end Auto