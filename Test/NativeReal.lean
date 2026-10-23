import Auto.Tactic

/-!
  Native prover's handling of `Real` (a `LaterType`).

  `lean-auto` cannot import Mathlib, so this file uses a stand-in `Real`.
  When `Real` and its operations are treated like builtin types (e.g. `Nat`, `Int`),
  the hypotheses sent to the native prover should mention `Real`'s
  `+, -, *, /` as-is, instead of free variables for uninterpreted atoms.

  The `#guard_msgs` checks fail until reification of `Real` is implemented.
-/

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"

-- Only use the (emulated) native solver
set_option auto.tptp false
set_option auto.smt false
set_option auto.native true
attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

/-- Stand-in for Mathlib's `Real`. As in Mathlib, the operations are irreducible -/
structure _root_.Real where
  val : Rat

namespace Real

@[irreducible] def add (x y : Real) : Real := ⟨x.val + y.val⟩
@[irreducible] def sub (x y : Real) : Real := ⟨x.val - y.val⟩
@[irreducible] def mul (x y : Real) : Real := ⟨x.val * y.val⟩
@[irreducible] def div (x y : Real) : Real := ⟨x.val / y.val⟩

instance : Add Real := ⟨add⟩
instance : Sub Real := ⟨sub⟩
instance : Mul Real := ⟨mul⟩
instance : Div Real := ⟨div⟩

end Real

/--
trace: [auto.lam2D.printHyps] ¬e!_0 + e!_1 = e!_0 * e!_1 - e!_1 / e!_0
[auto.lam2D.printHyps] e!_1 + e!_0 = e!_1 * e!_0
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example (x y : Real) (h : x + y = x * y) : y + x = y * x - x / y := by auto [h]

/--
trace: [auto.lam2D.printHyps] ¬e!_0 * e!_1 = e!_1 * e!_0
[auto.lam2D.printHyps] (fun {α} p => ∀ (x : α), p x) fun eb!_0 =>
      (fun {α} p => ∀ (x : α), p x) fun eb!_1 => eb!_0 * eb!_1 = eb!_1 * eb!_0
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example (x y : Real) (h : ∀ a b : Real, a * b = b * a) : x * y = y * x := by auto [h]

/--
trace: [auto.lam2D.printHyps] ¬e!_0 * e!_1 + e!_0 * e!_1 = e!_0 * e!_1 + e!_0 * e!_1
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example (f : Real → Real) (y z : Real) (h : ∀ x, f x = x + x) : f (y * z) = y * z + y * z := by auto [h]

/--
trace: [auto.lam2D.printHyps] ¬e!_0 fun eb!_0 => e!_1 / eb!_0
[auto.lam2D.printHyps] e!_0 fun eb!_0 => e!_1 / eb!_0
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example (g : (Real → Real) → Prop) (y : Real) (h : g (y / ·)) : g (fun x => y / x) := by auto [h]

-- Partial application
/--
trace: [auto.lam2D.printHyps] ¬e!_0 (HDiv.hDiv e!_1)
[auto.lam2D.printHyps] e!_0 (HDiv.hDiv e!_1)
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example (g : (Real → Real) → Prop) (y : Real) (h : g (HDiv.hDiv y)) : g (HDiv.hDiv y) := by auto [h]

/--
trace: [auto.lam2D.printHyps] ¬∃ eb!_0, eb!_0 = e!_0 - e!_0
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example : ∀ x : Real, ∃ y : Real, y = x - x := by auto

-- Mixing with builtin types
/--
trace: [auto.lam2D.printHyps] ¬(e!_0.add e!_0 = e!_0.mul e!_0 ∧ e!_1 + e!_1 = e!_1 * e!_1)
[auto.lam2D.printHyps] e!_0.mul e!_0 = e!_0.add e!_0
[auto.lam2D.printHyps] e!_1 * e!_1 = e!_1 + e!_1
-/
#guard_msgs (trace, drop all) in
set_option trace.auto.lam2D.printHyps true in
example (n : Nat) (x : Real) (h₁ : n * n = n + n) (h₂ : x * x = x + x) :
  n + n = n * n ∧ x + x = x * x := by auto [h₁, h₂]
