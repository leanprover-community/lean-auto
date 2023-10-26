/-
Copied from `mathlib4/test/montonicity.lean`.

We can isolate the facts used.
-/
/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Tactic.Monotonicity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Ring.Defs
-- import measure_theory.measure.lebesgue
-- import measure_theory.function.locally_integrable
import Mathlib.Data.List.Defs
import Auto.Tactic

set_option auto.smt true
set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.duper false
set_option auto.smt.solver.name "cvc5"

open List Set

example (x y z k : ℕ)
    (h : 3 ≤ (4 : ℕ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by auto

example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by auto

example (x y z a b : ℕ)
    (h : a ≤ (b : ℕ))
    (h' : z ≤ y) :
    (1 + a + x) - y ≤ (1 + b + x) - z := by auto

example (x y z a b : ℤ)
    (h : a ≤ (b : ℤ))
    (h' : z ≤ y) :
    (1 + a + x) - y ≤ (1 + b + x) - z := by auto

example (x y z : ℤ)
    (h' : z ≤ y) :
    (1 + 3 + x) - y ≤ (1 + 4 + x) - z := by auto

example {x y z : ℕ} : true := by auto

-- Can't be modeled by auto
example {x y z : ℕ} : true := by
  suffices : x + y ≤ z + y; trivial
  mono
  guard_target = x ≤ z
  admit

-- Can't be modeled by auto
example {x y z w : ℕ} : true := by
  have : x + y ≤ z + w := by
    mono
    guard_target = x ≤ z; admit
    guard_target = y ≤ w; admit
  trivial

example
  (h : 3 + 6 ≤ 4 + 5) : 1 + 3 + 2 + 6 ≤ 4 + 2 + 1 + 5 := by auto

example
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
  : (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 := by auto

example
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
  : (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 := by auto

example (x y z : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y)
  : (1 + 3 + x) - y ≤ (1 + 4 + x) - z := by auto

@[simp]
def List.le' {α : Type _} [LE α] : List α → List α → Prop
| x::xs, y::ys => x ≤ y ∧ List.le' xs ys
| [],    []    => true
| _,      _    => false

@[simp]
instance list_has_le {α : Type _} [LE α] : LE (List α) := ⟨List.le'⟩

-- lemma list.le_refl {α : Type _} [Preorder α] {xs : LE α} : xs ≤ xs := by
--   induction' xs with x xs
--   · trivial
--   · simp [has_le.le,list.le]
--     split
--     · exact le_rfl
--     · apply xs_ih

-- -- @[trans]
-- lemma List.le_trans {α : Type _} [Preorder α]
--     {xs zs : List α} (ys : List α)
--     (h  : xs ≤ ys)
--     (h' : ys ≤ zs) :
--     xs ≤ zs := by
--   revert ys zs
--   induction' xs with x xs
--  ; intros ys zs h h'
--  ; cases ys with y ys
--  ; cases zs with z zs
--  ; try { cases h; cases h'; done },
--   { apply list.le_refl },
--   { simp [has_le.le,list.le],
--     split,
--     apply le_trans h.left h'.left,
--     apply xs_ih _ h.right h'.right, }

-- @[mono]
-- lemma list_le_mono_left {α : Type*} [preorder α] {xs ys zs : list α}
--     (h : xs ≤ ys) :
--     xs ++ zs ≤ ys ++ zs := by
--   revert ys
--   induction xs with x xs; intros ys h
--   · cases ys; apply list.le_refl; cases h
--   · cases ys with y ys; cases h; simp [has_le.le,list.le] at *
--     revert h; apply and.imp_right
--     apply xs_ih

-- @[mono]
-- lemma list_le_mono_right {α : Type*} [preorder α] {xs ys zs : list α}
--     (h : xs ≤ ys) :
--     zs ++ xs ≤ zs ++ ys := by
--   revert ys zs
--   induction xs with x xs; intros ys zs h
--   · cases ys
--     · simp; apply list.le_refl
--     · cases h
--   · cases ys with y ys; cases h; simp [has_le.le,list.le] at *
--     suffices : list.le' ((zs ++ [x]) ++ xs) ((zs ++ [y]) ++ ys)
--     · refine cast _ this; simp
--     apply list.le_trans (zs ++ [y] ++ xs)
--     · apply list_le_mono_left
--       induction zs with z zs
--       · simp [has_le.le,list.le]; apply h.left
--       · simp [has_le.le,list.le]; split; exact le_rfl
--         apply zs_ih
--     · apply xs_ih h.right

-- lemma bar_bar'
--   (h : [] ++ [3] ++ [2] ≤ [1] ++ [5] ++ [4])
-- : [] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
-- begin
--   ac_mono,
-- end

-- lemma bar_bar''
--   (h : [3] ++ [2] ++ [2] ≤ [5] ++ [4] ++ [])
-- : [1] ++ ([3] ++ [2]) ++ [2] ≤ [1] ++ [5] ++ ([4] ++ []) :=
-- begin
--   ac_mono,
-- end

-- lemma bar_bar
--   (h : [3] ++ [2] ≤ [5] ++ [4])
-- : [1] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
-- begin
--   ac_mono,
-- end

def P (x : ℕ) := 7 ≤ x
def Q (x : ℕ) := x ≤ 7

lemma P_mono {x y : ℕ}
    (h : x ≤ y) :
    P x → P y := by auto d[P]

lemma Q_mono {x y : ℕ}
    (h : y ≤ x) :
    Q x → Q y := by auto d[Q]

example (x y z : ℕ)
  (h : x ≤ y)
  : P (x + z) → P (z + y) := by auto [h, P_mono]

example (x y z : ℕ)
  (h : y ≤ x)
  : Q (x + z) → Q (z + y) := by auto [h, Q_mono]

example (x y z k m n : ℤ)
  (h₀ : z ≤ 0)
  (h₁ : y ≤ x)
  : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
  : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
  : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
  : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m)
  : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : n + x + m ≤ y + n + m)
  : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto

example (x y z k m n : ℤ)
  (h₁ : x ≤ y)
  : true := by auto

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
  : true := by auto

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: true := by
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k := by auto
  auto

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
  : (m + x + n + i) * z + k = z * (j + n + m + y) + k := by auto

example (x y z k m n i j : ℕ)
    (h₁ : x + i = y + j) :
    z * (x + i + n + m) + k = z * (y + j + n + m) + k := by auto

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k := by auto
