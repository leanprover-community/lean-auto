import Auto.Tactic

open Auto Embedding

set_option trace.auto.tactic true
set_option trace.auto.lamReif true
set_option trace.auto.metaExtra true
example (H : (fun (x y z t : Nat) => x) = (fun x y z t => x)) : True := by
  try auto [H]
  sorry