import Auto.Tactic

/-!
  Native prover's handling of `Real` (a `LaterType`).

  `lean-auto` cannot import Mathlib, so this file uses a stand-in `Real`.
  When `Real` and its operations are treated like builtin types (e.g. `Nat`, `Int`),
  the hypotheses sent to the native prover (see `trace.auto.lam2D.printHyps`)
  should mention `Real`'s `+, -, *, /, -·, ·⁻¹` as-is, instead of free variables
  for uninterpreted atoms.
-/

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"

-- Only use the (emulated) native solver
set_option auto.tptp false
set_option auto.smt false
set_option auto.native true
attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

/--
  Stand-in for Mathlib's `Real`, mirroring `Mathlib/Basic/Real/Basic.lean`:
  `add, neg, mul, inv'` are private and irreducible, while `-` and `/`
  are defined in terms of them
-/
structure _root_.Real where
  val : Rat

namespace Real

@[irreducible] private def add (x y : Real) : Real := ⟨x.val + y.val⟩
@[irreducible] private def neg (x : Real) : Real := ⟨-x.val⟩
@[irreducible] private def mul (x y : Real) : Real := ⟨x.val * y.val⟩
@[irreducible] private def inv' (x : Real) : Real := ⟨x.val⁻¹⟩

instance : Add Real := ⟨add⟩
instance : Neg Real := ⟨neg⟩
instance : Mul Real := ⟨mul⟩
instance : Inv Real := ⟨inv'⟩
instance : Sub Real := ⟨fun a b => a + -b⟩
instance : Div Real := ⟨fun a b => a * b⁻¹⟩

end Real

set_option trace.auto.lam2D.printHyps true in
example (x y : Real) (h : x + y = x * y) : y + x = y * x - x / y := by auto [h]

set_option trace.auto.lam2D.printHyps true in
example (x y : Real) (h : -x = y⁻¹) : y⁻¹ = -x := by auto [h]

set_option trace.auto.lam2D.printHyps true in
example (x y : Real) (h : ∀ a b : Real, a * b = b * a) : x * y = y * x := by auto [h]

set_option trace.auto.lam2D.printHyps true in
example (f : Real → Real) (y z : Real) (h : ∀ x, f x = x + x) : f (y * z) = y * z + y * z := by auto [h]

set_option trace.auto.lam2D.printHyps true in
example (g : (Real → Real) → Prop) (y : Real) (h : g (y / ·)) : g (fun x => y / x) := by auto [h]

-- Partial application
set_option trace.auto.lam2D.printHyps true in
example (g : (Real → Real) → Prop) (y : Real) (h : g (HDiv.hDiv y)) : g (HDiv.hDiv y) := by auto [h]

set_option trace.auto.lam2D.printHyps true in
example : ∀ x : Real, ∃ y : Real, y = x - x := by auto

-- Mixing with builtin types
set_option trace.auto.lam2D.printHyps true in
example (n : Nat) (x : Real) (h₁ : n * n = n + n) (h₂ : x * x = x + x) :
  n + n = n * n ∧ x + x = x * x := by auto [h₁, h₂]
