/-
This typeclass is used to provide support for Mathlib Reals only if MathlibReal.lean is imported
`variable (R? : Option ((R : Type) × RealTy R))` is used throughout the embedding
to optionally pass in the Mathlib instance of Real, which is necessary in `LamBaseSort.interp`.
It ensures that all of the necessary typeclasses are present and uses them in the embedding.
-/
module

@[expose] public section

namespace Auto

class RealTy (α : Type) extends
    Zero α, One α, Add α, Sub α, Neg α, Mul α, Div α, Inv α,
    NatCast α, IntCast α, OfScientific α, LE α, LT α, Max α, Min α

end Auto
