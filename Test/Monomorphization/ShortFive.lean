import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Auto.Tactic

/-
It would be great if `short_five_mono` and `short_five_epi` could be proved fully automatically
with the relevant facts, but even getting some steps automatically would be good.

Each `short_exact` hypothesis can be split up into four hypotheses if necessary.

The morphisms `f : A →+ B` can be expressed instead as functions `f` satisfying
`map_zero_f : f 0 = 0` and `map_sub_f : ∀ a₀ a₁, f (a₀ - a₁) = f a₀ - f a₁`.

It would make sense to make a copy of this file with these simplifications but keep the
original.
-/

open Function

structure is_short_exact {A B C : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A → B) (g : B → C) :=
  (inj       : Injective f)
  (im_in_ker : ∀ a : A, g (f a) = 0)
  (ker_in_im : ∀ b : B, g b = 0 → ∃ a : A, f a = b)
  (surj      : Surjective g)

section ShortFive

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

set_option auto.prep.redMode "reducible"
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

-- set_option pp.explicit true
set_option trace.auto.printLemmas true
set_option trace.auto.tactic true
set_option auto.mono.saturationThreshold 500
theorem short_five_mono (injh : Injective h) (injl : Injective l) :
    Injective k := by
  auto [injective_iff_map_eq_zero, injl, injh, short_exact₁.inj,
       square₀, square₁, short_exact₀.ker_in_im, map_zero] u[Injective]

/- Duper fails violently
theorem short_five_mono' (injh : Injective h) (injl : Injective l) :
    Injective k := by
  rw [injective_iff_map_eq_zero]
  let injs := short_exact₁.inj
  dsimp [Injective] at injh injl injs
  duper [injl, injh, injs, square₀, square₁,
         is_short_exact.ker_in_im short_exact₀, map_zero]
-/

theorem short_five_epi (surjh : Surjective h) (surjl : Surjective l) :
    Surjective k := by
  intro b₁
  rcases surjl (g₁ b₁) with ⟨c₀, hlc₀⟩
  rcases short_exact₀.surj c₀ with ⟨b₀, hg₀b₀⟩
  have : g₁ (k b₀ - b₁) = 0 := by
    auto [map_sub, square₁, hg₀b₀, hlc₀, sub_self]
  rcases short_exact₁.ker_in_im _ this with ⟨a₁, hf₁a₁⟩
  auto [map_sub, square₀, surjh a₁, hf₁a₁, sub_sub_cancel]

-- What?
set_option auto.prep.redMode "instances" in
theorem short_five_mono' (injh : Injective h) (injl : Injective l) :
    Injective k := by
  auto [injective_iff_map_eq_zero, injl, injh, short_exact₁.inj,
       square₀, square₁, short_exact₀.ker_in_im, map_zero] u[Injective]

end ShortFive


