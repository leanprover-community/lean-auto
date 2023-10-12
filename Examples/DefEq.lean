/-
These are examples that are DefEq to first-order problems, but the automation needs to figure
that out.
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime
import Auto.Tactic

open Set

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option trace.auto.lamReif.printResult true

-- automation has to unify the two descriptions of +
example (a b : ℕ) (P : ℕ → Prop) (h : P (a + b)) : P (b + a) := by
  auto [h, add_comm]

example (a b c d : ℤ) (h1 : a ≤ b) (h2 : c ≤ d) : Icc a b ⊆ Icc c d ↔ c ≤ a ∧ b ≤ d := by
  auto [subset_def, Set.mem_Icc, h1, h2, @le_trans, @le_total]

example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : Icc a b ⊆ Icc c d ↔ c ≤ a ∧ b ≤ d := by
  have h3 : ∀ s t : Set ℝ, s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := by intros; rfl
  auto [subset_def, Set.mem_Icc, h1, h2, h3, @le_trans, @le_total]

-- mathlib proof
theorem prime_def_lt'' {p : ℕ} : Nat.Prime p ↔ 2 ≤ p ∧ ∀ (m) (_ : m ∣ p), m = 1 ∨ m = p := by
  refine' ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => _⟩
  -- Porting note: needed to make ℕ explicit
  have h1 := (@one_lt_two ℕ ..).trans_le h.1
  refine' ⟨mt Nat.isUnit_iff.mp h1.ne', _⟩
  auto [Nat.isUnit_iff, mul_right_inj' (pos_of_gt h1).ne',
        mul_one, dvd_mul_right, h.2]

-- Zipperposition succeeds if `auto.lamReif.prep.def false`, but fails if `auto.lamReif.prep.def true`
set_option auto.lamReif.prep.def false in
set_option trace.auto.lamReif.prep.def true in
set_option trace.auto.lamReif.prep.printResult true in
-- Here we give all the theorem statements explicitly. We should be able to eliminate them.
theorem prime_def_lt''_new {p : ℕ} : Nat.Prime p ↔ 2 ≤ p ∧ ∀ (m) (_ : m ∣ p), m = 1 ∨ m = p := by
  have h1 : (1 : Nat) < 2 := @one_lt_two Nat _ _ _ _ _
  have h2 : ∀ {a b c : ℕ}, a < b → b ≤ c → a < c := @LT.lt.trans_le Nat _
  have h3 : ∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c) := @mul_right_inj' Nat _
  have h4 : ∀ {n m : ℕ}, n < m → 0 < m:= @pos_of_gt Nat _
  have h5 : ∀ (a b : ℕ), a ∣ a * b := @dvd_mul_right Nat _
  have h6 : ∀ (a : ℕ), a * 1 = a := @mul_one Nat _
  have h7 : ∀ {x y : ℕ}, x < y → y ≠ x := @LT.lt.ne' Nat _
  have h8 : ∀ {n : ℕ}, IsUnit n ↔ n = 1 := @Nat.isUnit_iff
  have h9 : ∀ {p : ℕ}, Nat.Prime p → 2 ≤ p := @Nat.Prime.two_le
  have h10 : ∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p := @Nat.Prime.eq_one_or_self_of_dvd
  have h11 := Nat.irreducible_iff_nat_prime
  have h12 : ∀ {p : ℕ}, Irreducible p ↔ ¬IsUnit p ∧ ∀ (a b : ℕ), p = a * b → IsUnit a ∨ IsUnit b := @irreducible_iff Nat _
  auto