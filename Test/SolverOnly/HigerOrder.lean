import Auto.Tactic

open Auto Embedding

set_option auto.optimizeCheckerProof false

set_option trace.auto.tactic true in
example (H : (fun x : Nat => x) = (fun x => x)) : True := by
  auto [H]

set_option trace.auto.tactic true in
example (H : (fun (x y z t : Nat) => x) = (fun x y z t => x)) : True := by
  auto [H]

-- ULift test
set_option trace.auto.buildChecker true in
example (f : Nat → Nat → Nat)
  (H : (fun (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) =>
    f (f (f (f (f x0 x1) (f x2 x3)) (f (f x4 x5) (f x6 x7)))
         (f (f (f x8 x9) (f x10 x11)) (f (f x12 x13) (f x14 x15))))
      (f (f (f (f x16 x17) (f x18 x19)) (f (f x20 x21) (f x22 x23)))
         (f (f (f x24 x25) (f x26 x27)) (f (f x28 x29) (f x30 x31))))) =
        (fun (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) =>
    f (f (f (f (f x0 x1) (f x2 x3)) (f (f x4 x5) (f x6 x7)))
         (f (f (f x8 x9) (f x10 x11)) (f (f x12 x13) (f x14 x15))))
      (f (f (f (f x16 x17) (f x18 x19)) (f (f x20 x21) (f x22 x23)))
         (f (f (f x24 x25) (f x26 x27)) (f (f x28 x29) (f x30 x31)))))) : True := by
  auto [H]

set_option trace.auto.buildChecker true in
example
  {α : Sort u}
  (add : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hadd : ∀ x y f n, add x y f n = (x f) ((y f) n))
  (mul : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hmul : ∀ x y f, mul x y f = x (y f))
  (w₁ w₂ : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hw₁₂ : (w₁ = w₂) = (w₂ = w₁)) : True := by 
  auto [Hadd, Hmul, Hw₁₂]