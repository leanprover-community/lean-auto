import Auto.Tactic

def hello := "world"

example
  {α : So}
  (add : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hadd : ∀ x y f n, add x y f n = (x f) ((y f) n))
  (mul : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hmul : ∀ x y f, mul x y f = x (y f))
  (w₁ w₂ : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hw₁₂ : (w₁ = w₂) = (w₂ = w₁)) : True := by 
  auto [Hadd, Hmul, Hw₁₂]
  sorry