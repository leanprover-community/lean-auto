namespace Auto.Bin

theorem wfAux (n : Nat) : (n + 2).div 2 < n + 2 := by
  apply Nat.div_lt_self
  case hLtN => apply Nat.succ_le_succ; apply Nat.zero_le
  case hLtK => apply Nat.le_refl

def inductionOn.{u}
  {motive : Nat → Sort u} (x : Nat)
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : motive x :=
  match x with
  | 0 => base₀
  | 1 => base₁
  | x' + 2 => ind x' (inductionOn ((x' + 2) / 2) ind base₀ base₁)

@[irreducible] def induction.{u}
  {motive : Nat → Sort u}
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : ∀ x, motive x :=
  fun x => inductionOn x ind base₀ base₁

end Auto.Bin
