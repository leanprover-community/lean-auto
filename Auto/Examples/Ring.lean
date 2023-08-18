import Mathlib.Tactic.Ring

example (x y z : Int) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by
  ring

variable {R : Type _} [CommRing R]

example (x y z : R) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by
  ring
