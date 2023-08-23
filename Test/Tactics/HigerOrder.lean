import Auto.Tactic

open Auto Embedding

set_option trace.auto.tactic true in
set_option trace.auto.lamReif true in
example (H : (fun (x y z t : Nat) => x) = (fun x y z t => x)) : True := by
  try auto [H]
  sorry

set_option trace.auto.lamReif true in
set_option trace.auto.buildChecker true in
example
  {α : Sort u}
  (add : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hadd : ∀ x y f n, add x y f n = (x f) ((y f) n))
  (mul : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hmul : ∀ x y f, mul x y f = x (y f))
  (w₁ w₂ : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hw₁₂ : (w₁ = w₂) = (w₂ = w₁)) : True := by 
  try auto [Hadd, Hmul, Hw₁₂]
  sorry