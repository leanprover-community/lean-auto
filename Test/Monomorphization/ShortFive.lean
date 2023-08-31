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

set_option trace.auto.printLemmas true
set_option trace.auto.tactic true
set_option auto.mono.saturationThreshold 500
set_option trace.auto.mono.printLemmaInst true
set_option trace.auto.mono true in
theorem short_five_mono_dbg (injh : Injective h) (injl : Injective l) :
    Injective k := by
  intro b kb0
  have : l (g₀ b) = l 0 := by
    try auto [square₁]
    sorry
  sorry

-- set_option pp.explicit true
set_option trace.auto.printLemmas true
set_option trace.auto.tactic true
set_option auto.mono.saturationThreshold 500
theorem short_five_mono (injh : Injective h) (injl : Injective l) :
    Injective k := by
  rw [injective_iff_map_eq_zero]
  intro b kb0
  have : l (g₀ b) = l 0 := by
    try auto [square₁, kb0, map_zero]
    sorry
  have : g₀ b = 0 := injl this
  rcases ker_in_im short_exact₀ _ this with ⟨a, f₀a⟩
  have : f₁ (h a) = f₁ (h 0) := by
    try auto [square₀, f₀a, kb0, map_zero]
    sorry
  have : h a = h 0 := short_exact₁.inj this
  have : a = 0 := injh this
  show b = 0
  rw [←f₀a, this, map_zero]

theorem short_five_epi (surjh : Surjective h) (surjl : Surjective l) :
    Surjective k := by
  intro b₁
  rcases surjl (g₁ b₁) with ⟨c₀, hlc₀⟩
  rcases short_exact₀.surj c₀ with ⟨b₀, hg₀b₀⟩
  have : g₁ (k b₀ - b₁) = 0 := by rw [map_sub, ←square₁, hg₀b₀, hlc₀, sub_self]
  rcases short_exact₁.ker_in_im _ this with ⟨a₁, hf₁a₁⟩
  rcases surjh a₁ with ⟨a₀, ha₀⟩
  use b₀ - f₀ a₀
  rw [map_sub, square₀, ha₀, hf₁a₁, sub_sub_cancel]

end ShortFive


