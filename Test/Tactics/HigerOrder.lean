import Auto.Tactic

open Auto Embedding

set_option trace.auto.tactic true
set_option trace.auto.lamReif true
example (H : (fun (x y z t : Nat) => x) = (fun x y z t => x)) : True := by
  try auto [H]

-- Binder test
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
  try auto [H]