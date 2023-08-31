import Auto.Tactic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

set_option auto.prep.redMode "reducible"
set_option trace.auto.mono true
set_option trace.auto.tactic true

set_option trace.auto.lamReif true
set_option trace.auto.lamReif.printValuation true
example (a b c d : ℝ) (h1 : a < b) : Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  auto [Set.subset_def, Set.mem_Icc, Set.mem_Ico, @lt_iff_not_le, @le_refl, @le_trans]

set_option trace.auto.printLemmas true in
set_option trace.auto.mono.printLemmaInst true in
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  auto [Set.subset_def, Set.mem_preimage]

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

[auto.lamReif] `(¬ ((?0 (?1 ?2 ?3) (?4 ?5 ?6)) ↔ ((?7 ?5 ?2) ∧ (?8 ?3 ?6))))` 
[auto.lamReif] `(∀ x0 : ?0, (∀ x1 : ?0, ((?0 x0 x1) = (∀ x2 : ?1, ((?9 x2 x0) → (?9 x2 x1))))))` 
[auto.lamReif] `(∀ x0 : ?1, (∀ x1 : ?1, (∀ x2 : ?1, ((?9 x2 (?1 x0 x1)) ↔ ((?10 x0 x2) ∧ (?10 x2 x1))))))` 
[auto.lamReif] `(∀ x0 : ?1, (∀ x1 : ?1, (∀ x2 : ?1, ((?9 x2 (?4 x0 x1)) ↔ ((?10 x0 x2) ∧ (?11 x2 x1))))))` 
[auto.lamReif] `(∀ x0 : ?1, (∀ x1 : ?1, ((?12 x0 x1) ↔ (¬ (?13 x1 x0)))))` 
[auto.lamReif] `(∀ x0 : ?1, (?10 x0 x0))` 
[auto.lamReif] `(∀ x0 : ?1, (∀ x1 : ?1, (∀ x2 : ?1, ((?10 x0 x1) → ((?10 x1 x2) → (?10 x0 x2))))))` 
[auto.lamReif.printValuation] Term Atom 0 : (?0 → (?0 → Prop)) := Subset 
[auto.lamReif.printValuation] Term Atom 1 : (?1 → (?1 → ?0)) := Set.Icc 
[auto.lamReif.printValuation] Term Atom 2 : ?1 := a 
[auto.lamReif.printValuation] Term Atom 3 : ?1 := b 
[auto.lamReif.printValuation] Term Atom 4 : (?1 → (?1 → ?0)) := Set.Ico 
[auto.lamReif.printValuation] Term Atom 5 : ?1 := c 
[auto.lamReif.printValuation] Term Atom 6 : ?1 := d 
[auto.lamReif.printValuation] Term Atom 7 : (?1 → (?1 → Prop)) := LE.le 
[auto.lamReif.printValuation] Term Atom 8 : (?1 → (?1 → Prop)) := LT.lt 
[auto.lamReif.printValuation] Term Atom 9 : (?1 → (?0 → Prop)) := Membership.mem 
[auto.lamReif.printValuation] Term Atom 10 : (?1 → (?1 → Prop)) := LE.le 
[auto.lamReif.printValuation] Term Atom 11 : (?1 → (?1 → Prop)) := LT.lt 
[auto.lamReif.printValuation] Term Atom 12 : (?1 → (?1 → Prop)) := LT.lt 
[auto.lamReif.printValuation] Term Atom 13 : (?1 → (?1 → Prop)) := LE.le 
[auto.lamReif.printValuation] Type Atom 0 := Set ℝ : Type 
[auto.lamReif.printValuation] Type Atom 1 := ℝ : Type 

-/