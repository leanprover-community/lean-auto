import Auto.Tactic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Order.Basic

set_option auto.prep.redMode "reducible"
set_option trace.auto.mono true
set_option trace.auto.tactic true

example (a b c d : ℝ) (h1 : a < b) : Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  rw [Set.subset_def]
  apply Iff.intro
  case mp =>
    let ⟨e, ltae, lteb⟩ := DenselyOrdered.dense a b h1
    intro h; let h' := h e; rw [Set.mem_Icc, Set.mem_Ico] at h'
    rw [lt_iff_not_le] at ltae lteb h'
    auto [ltae, lteb, h', @le_trans, @le_total]

set_option trace.auto.lamReif true
set_option trace.auto.lamReif.printValuation true
set_option maxHeartbeats 20000 in
example (a b c d : ℝ) (h1 : a < b) : Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  rw [Set.subset_def]
  auto [Set.mem_Icc, Set.mem_Ico, @le_refl, @le_trans, @le_total,
        @lt_iff_not_le, DenselyOrdered.dense a b h1]

set_option trace.auto.printLemmas true in
set_option trace.auto.mono.printLemmaInst true in
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

set_option trace.auto.mono.printLemmaInst true in
example (h : Function.Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  auto [Set.subset_def, Set.mem_preimage, Function.Injective.mem_set_image]

set_option trace.auto.mono.printLemmaInst true in
set_option trace.auto.mono.printConstInst true in
example : f '' (f ⁻¹' u) ⊆ u := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

set_option trace.auto.mono.printLemmaInst true in
set_option auto.mono.saturationThreshold 200 in
example (h : Function.Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  auto [Set.subset_def, Function.Surjective, Set.mem_image, Set.mem_preimage]

/-
[auto.lamReif] `(¬ ((∀ x0 : ?0, ((?0 x0 (?1 ?2 ?3)) → (?0 x0 (?4 ?5 ?6)))) ↔ ((?7 ?5 ?2) ∧ (¬ (?7 ?6 ?3)))))` 
[auto.lamReif] `(∀ x0 : ?0, (∀ x1 : ?0, (∀ x2 : ?0, ((?0 x2 (?1 x0 x1)) ↔ ((?7 x0 x2) ∧ (?7 x2 x1))))))` 
[auto.lamReif] `(∀ x0 : ?0, (∀ x1 : ?0, (∀ x2 : ?0, ((?0 x2 (?4 x0 x1)) ↔ ((?7 x0 x2) ∧ (?8 x2 x1))))))` 
[auto.lamReif] `(∀ x0 : ?0, (?7 x0 x0))` 
[auto.lamReif] `(∀ x0 : ?0, (∀ x1 : ?0, (∀ x2 : ?0, ((?7 x0 x1) → ((?7 x1 x2) → (?7 x0 x2))))))` 
[auto.lamReif] `(∀ x0 : ?0, (∀ x1 : ?0, ((?7 x0 x1) ∨ (?7 x1 x0))))` 
Term Atom 0 : (?0 → (?1 → Prop)) := Membership.mem 
Term Atom 1 : (?0 → (?0 → ?1)) := Set.Icc 
Term Atom 2 : ?0 := a 
Term Atom 3 : ?0 := b 
Term Atom 4 : (?0 → (?0 → ?1)) := Set.Ico 
Term Atom 5 : ?0 := c 
Term Atom 6 : ?0 := d 
Term Atom 7 : (?0 → (?0 → Prop)) := LE.le 
Term Atom 8 : (?0 → (?0 → Prop)) := LT.lt 
Type Atom 0 := ℝ : Type 
Type Atom 1 := Set ℝ : Type

-/