namespace Auto

-- This function is slow and is not meant to be used in
--   computation. It's main use is in the pushs_pops theorems
def List.ofFun (f : Nat → α) (n : Nat) : List α :=
  match n with
  | 0 => .nil
  | .succ n' => f 0 :: ofFun (fun n => f (.succ n)) n'

theorem List.ofFun_length (f : Nat → α) (n : Nat) :
  (List.ofFun f n).length = n := by
  revert f; induction n <;> intros f
  case zero => rfl
  case succ n IH => dsimp [ofFun]; rw [IH]

theorem List.ofFun_get?_eq_some (f : Nat → α) (n m : Nat) (h : n > m) :
  (List.ofFun f n).get? m = .some (f m) := by
  revert f n; induction m <;> intros f n h
  case zero =>
    cases n
    case zero => cases h
    case succ n => rfl
  case succ m IH =>
    cases n
    case zero => cases h
    case succ n =>
      let h' := Nat.le_of_succ_le_succ h
      dsimp [ofFun, List.get?]; rw [IH (fun n => f (.succ n)) _ h']

end Auto