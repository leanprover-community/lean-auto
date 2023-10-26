import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Order.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Auto.Tactic


set_option profiler true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport"
set_option auto.tptp.zeport.path "/home/indprinciple/Programs/zipperposition/portfolio/portfolio.fo.parallel.py"

set_option auto.duper true
set_option auto.tptp true



section SimpleClass

set_option auto.redMode "instances"
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

example (as bs cs ds : List β) : (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  auto [List.append_assoc]

example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  auto [List.append_assoc, List.map_append]

set_option auto.redMode "reducible"

set_option trace.auto.printLemmas true in
example (as bs cs ds : List β) : (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  auto [List.append_assoc]

set_option trace.auto.tactic true in
example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  auto [List.append_assoc, List.map_append]

end SimpleClass


section SimpleMathlib

set_option auto.redMode "reducible"
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

-- Testing SynthArg
set_option trace.auto.printLemmas true in
set_option trace.auto.mono.printLemmaInst true in
example (a b : ℝ) (h1 : a < b) : (∃ c, a < c ∧ c < b) := by
  auto [DenselyOrdered.dense, h1]

-- Testing SynthArg
example (a e : ℝ) (h1 : a < e) : (∃ b c d, a < b ∧ b < c ∧ c < d ∧ d < e) := by
  auto [DenselyOrdered.dense, h1]

set_option trace.auto.printLemmas true in
example (a b c d : ℝ) (h1 : a < b) :
  Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  rw [Set.subset_def]
  auto [Set.mem_Icc, Set.mem_Ico, @le_trans, @le_total, @lt_iff_not_le, h1]

set_option trace.auto.smt.result true in
example (a b c d : ℝ) (h1 : a < b) : Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  rw [Set.subset_def]
  auto [Set.mem_Icc, Set.mem_Ico, @le_trans, @le_total, @lt_iff_not_le, h1]

set_option trace.auto.lamReif.printValuation true in
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

example (h : Function.Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  auto [Set.subset_def, Set.mem_preimage, Function.Injective.mem_set_image, h]

example : f '' (f ⁻¹' u) ⊆ u := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

example (h : Function.Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage, h] d[Function.Surjective]

end SimpleMathlib



section Chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for both the real
(`Real.cos`) and complex (`Complex.cos`) cosine.
-/

set_option linter.uppercaseLean3 false

namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

@[simp]
theorem aeval_T (x : A) (n : ℕ) : aeval x (T R n) = (T A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_T]

@[simp]
theorem aeval_U (x : A) (n : ℕ) : aeval x (U R n) = (U A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_U]

@[simp]
theorem algebraMap_eval_T (x : R) (n : ℕ) :
    algebraMap R A ((T R n).eval x) = (T A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_T]

@[simp]
theorem algebraMap_eval_U (x : R) (n : ℕ) :
    algebraMap R A ((U R n).eval x) = (U A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_U]

-- Porting note: added type ascriptions to the statement
@[simp, norm_cast]
theorem complex_ofReal_eval_T : ∀ (x : ℝ) n, (((T ℝ n).eval x : ℝ) : ℂ) = (T ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_T ℝ ℂ _ _ _

-- Porting note: added type ascriptions to the statement
@[simp, norm_cast]
theorem complex_ofReal_eval_U : ∀ (x : ℝ) n, (((U ℝ n).eval x : ℝ) : ℂ) = (U ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_U ℝ ℂ _ _ _

/-! ### Complex versions -/


section Complex

open Complex

variable (θ : ℂ)

set_option profiler true
set_option trace.auto.lamReif.printProofs true
set_option trace.auto.tptp.result true

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_complex_cos : ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by auto [T_zero, eval_one, Nat.cast_zero, zero_mul, cos_zero]
  | 1 => by auto [eval_X, one_mul, T_one, Nat.cast_one]
  | n + 2 => by
    -- Porting note: partially rewrote proof for lean4 numerals.
    have : (2 : ℂ[X]) = (2 : ℕ) := by norm_num
    simp only [this, eval_X, eval_one, T_add_two, eval_sub, eval_mul, eval_nat_cast]
    simp only [Nat.cast_ofNat, Nat.cast_add]
    rw [T_complex_cos (n + 1), T_complex_cos n]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, cos_add, one_mul, mul_assoc, sin_two_mul,
      cos_two_mul]
    simp [mul_sub, pow_two]
    auto [sub_right_comm, mul_comm, mul_assoc]

/--
  Zipperposition portfolio mode times out, but duper succeeds
-/
theorem T_complex_cos' : ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by auto [T_zero, eval_one, Nat.cast_zero, zero_mul, cos_zero]
  | 1 => by auto [eval_X, one_mul, T_one, Nat.cast_one]
  | n + 2 => by
    -- Porting note: partially rewrote proof for lean4 numerals.
    have : (2 : ℂ[X]) = (2 : ℕ) := by norm_num
    simp only [this, eval_X, eval_one, T_add_two, eval_sub, eval_mul, eval_nat_cast]
    simp only [Nat.cast_ofNat, Nat.cast_add]
    rw [T_complex_cos' (n + 1), T_complex_cos' n]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, cos_add, one_mul, mul_assoc, sin_two_mul,
      cos_two_mul]
    simp [mul_sub, sub_right_comm]
    auto [pow_two, mul_comm, mul_assoc]

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_complex_cos (n : ℕ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction' n with d hd
  -- `auto` fails if we provide `CharP.cast_eq_zero` instead of `CharP.cast_eq_zero _ Nat.zero`
  · auto [U_zero, eval_one, zero_add, one_mul, Nat.zero_eq, CharP.cast_eq_zero _ Nat.zero]
  · rw [U_eq_X_mul_U_add_T]
    simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mul, mul_assoc, hd, one_mul]
    -- Porting note: added `trans` to prevent `rw` from going on a wild goose chase applying `rfl`
    push_cast; rw [sin_add ((↑d + 1) * θ)]
    auto [add_mul, one_mul, mul_comm]

end Complex

-- ### Real versions
section Real

open Real

variable (θ : ℝ) (n : ℕ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := by exact_mod_cast T_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  exact_mod_cast U_complex_cos θ n

end Real

end Polynomial.Chebyshev

end Chebyshev



section ShortFive

open Function

structure is_short_exact {A B C : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A → B) (g : B → C) :=
  (inj       : Injective f)
  (im_in_ker : ∀ a : A, g (f a) = 0)
  (ker_in_im : ∀ b : B, g b = 0 → ∃ a : A, f a = b)
  (surj      : Surjective g)

variable {A₀ B₀ C₀ A₁ B₁ C₁ : Type _}
variable [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀]
variable [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]

variable {f₀ : A₀ →+ B₀} {g₀ : B₀ →+ C₀}
variable {f₁ : A₁ →+ B₁} {g₁ : B₁ →+ C₁}
variable {h  : A₀ →+ A₁} {k  : B₀ →+ B₁} {l  : C₀ →+C₁}

variable (short_exact₀ : is_short_exact f₀ g₀)
variable (short_exact₁ : is_short_exact f₁ g₁)
variable (square₀      : ∀ a, k (f₀ a) = f₁ (h a))
variable (square₁      : ∀ b, l (g₀ b) = g₁ (k b))

open is_short_exact

set_option auto.duper true
set_option auto.redMode "reducible"
set_option trace.auto.lamReif.printProofs true
set_option trace.auto.lamReif.printValuation true

set_option auto.mono.saturationThreshold 500
theorem short_five_mono (injh : Injective h) (injl : Injective l) :
    Injective k := by
  auto [injective_iff_map_eq_zero, injl, injh, short_exact₁.inj,
       square₀, square₁, short_exact₀.ker_in_im, map_zero] u[Injective]

theorem short_five_epi (surjh : Surjective h) (surjl : Surjective l) :
    Surjective k := by
  intro b₁
  rcases surjl (g₁ b₁) with ⟨c₀, hlc₀⟩
  rcases short_exact₀.surj c₀ with ⟨b₀, hg₀b₀⟩
  have : g₁ (k b₀ - b₁) = 0 := by
    auto [map_sub, square₁, hg₀b₀, hlc₀, sub_self]
  rcases short_exact₁.ker_in_im _ this with ⟨a₁, hf₁a₁⟩
  auto [map_sub, square₀, surjh a₁, hf₁a₁, sub_sub_cancel]

end ShortFive
