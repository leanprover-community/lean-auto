import Auto.Tactic

set_option profiler true
set_option auto.optimizeCheckerProof false
set_option compiler.enableNew false
set_option auto.checker.buildMode "indirectReduce_reflection"

set_option trace.auto.lamReif.printProofs true
theorem test
  (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ f₁₄ : Nat → Nat → Nat)
  (g₁ g₂ g₃ g₄ g₅ g₆ : Nat → Nat → Nat)
  (f₁₅ f₁₆ f₁₇ f₁₈ f₁₉ f₂₀ f₂₁ f₂₂ f₂₃ f₂₄ f₂₅ f₂₆ f₂₇ f₂₈ : Nat → Nat → Nat)
  (H₁₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
       ∀ x₁₇, ∃ x₁₈, ∀ x₁₉, ∃ x₂₀, ∀ x₂₁, ∃ x₂₂, ∀ x₂₃, ∃ x₂₄,
       ∀ x₂₅, ∃ x₂₆, ∀ x₂₇, ∃ x₂₈, ∀ x₂₉, ∃ x₃₀, ∀ x₃₁, ∃ x₃₂,
       ∀ x₃₃, ∃ x₃₄, ∀ x₃₅, ∃ x₃₆, ∀ x₃₇, ∃ x₃₈, ∀ x₃₉, ∃ x₄₀,
       ∀ x₄₁, ∃ x₄₂, ∀ x₄₃, ∃ x₄₄, ∀ x₄₅, ∃ x₄₆, ∀ x₄₇, ∃ x₄₈,
       ∀ x₄₉, ∃ x₅₀, ∀ x₅₁, ∃ x₅₂, ∀ x₅₃, ∃ x₅₄, ∀ x₅₅, ∃ x₅₆,
       ∀ x₅₇, ∃ x₅₈, ∀ x₅₉, ∃ x₆₀, ∀ x₆₁, ∃ x₆₂, ∀ x₆₃, ∃ x₆₄,
    (g₁ (g₁ (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)))
      (f₈ (f₉ (f₁₀ x₉ x₁₀) (f₁₁ x₁₁ x₁₂)) (f₁₂ (f₁₃ x₁₃ x₁₄) (f₁₄ x₁₅ x₁₆))))
      (g₁ (f₁₅ (f₁₆ (f₁₇ x₁₇ x₁₈) (f₁₈ x₁₉ x₂₀)) (f₁₉ (f₂₀ x₂₁ x₂₂) (f₂₁ x₂₃ x₂₄)))
        (f₂₂ (f₂₃ (f₂₄ x₂₅ x₂₆) (f₂₅ x₂₇ x₂₈)) (f₂₆ (f₂₇ x₂₉ x₃₀) (f₂₈ x₃₁ x₃₂))))) =
    (g₂ (g₂ (f₁ (f₂ (f₃ x₃₃ x₃₄) (f₄ x₃₅ x₃₆)) (f₅ (f₆ x₃₇ x₃₈) (f₇ x₃₉ x₄₀)))
      (f₈ (f₉ (f₁₀ x₄₁ x₄₂) (f₁₁ x₄₃ x₄₄)) (f₁₂ (f₁₃ x₄₅ x₄₆) (f₁₄ x₄₇ x₄₈))))
      (g₂ (f₁₅ (f₁₆ (f₁₇ x₄₉ x₅₀) (f₁₈ x₅₁ x₅₂)) (f₁₉ (f₂₀ x₅₃ x₅₄) (f₂₁ x₅₅ x₅₆)))
        (f₂₂ (f₂₃ (f₂₄ x₅₇ x₅₈) (f₂₅ x₅₉ x₆₀)) (f₂₆ (f₂₇ x₆₁ x₆₂) (f₂₈ x₆₃ x₆₄))))))
  (H₂₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
       ∀ x₁₇, ∃ x₁₈, ∀ x₁₉, ∃ x₂₀, ∀ x₂₁, ∃ x₂₂, ∀ x₂₃, ∃ x₂₄,
       ∀ x₂₅, ∃ x₂₆, ∀ x₂₇, ∃ x₂₈, ∀ x₂₉, ∃ x₃₀, ∀ x₃₁, ∃ x₃₂,
       ∀ x₃₃, ∃ x₃₄, ∀ x₃₅, ∃ x₃₆, ∀ x₃₇, ∃ x₃₈, ∀ x₃₉, ∃ x₄₀,
       ∀ x₄₁, ∃ x₄₂, ∀ x₄₃, ∃ x₄₄, ∀ x₄₅, ∃ x₄₆, ∀ x₄₇, ∃ x₄₈,
       ∀ x₄₉, ∃ x₅₀, ∀ x₅₁, ∃ x₅₂, ∀ x₅₃, ∃ x₅₄, ∀ x₅₅, ∃ x₅₆,
       ∀ x₅₇, ∃ x₅₈, ∀ x₅₉, ∃ x₆₀, ∀ x₆₁, ∃ x₆₂, ∀ x₆₃, ∃ x₆₄,
    (g₂ (g₂ (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)))
      (f₈ (f₉ (f₁₀ x₉ x₁₀) (f₁₁ x₁₁ x₁₂)) (f₁₂ (f₁₃ x₁₃ x₁₄) (f₁₄ x₁₅ x₁₆))))
      (g₂ (f₁₅ (f₁₆ (f₁₇ x₁₇ x₁₈) (f₁₈ x₁₉ x₂₀)) (f₁₉ (f₂₀ x₂₁ x₂₂) (f₂₁ x₂₃ x₂₄)))
        (f₂₂ (f₂₃ (f₂₄ x₂₅ x₂₆) (f₂₅ x₂₇ x₂₈)) (f₂₆ (f₂₇ x₂₉ x₃₀) (f₂₈ x₃₁ x₃₂))))) =
    (g₃ (g₃ (f₁ (f₂ (f₃ x₃₃ x₃₄) (f₄ x₃₅ x₃₆)) (f₅ (f₆ x₃₇ x₃₈) (f₇ x₃₉ x₄₀)))
      (f₈ (f₉ (f₁₀ x₄₁ x₄₂) (f₁₁ x₄₃ x₄₄)) (f₁₂ (f₁₃ x₄₅ x₄₆) (f₁₄ x₄₇ x₄₈))))
      (g₃ (f₁₅ (f₁₆ (f₁₇ x₄₉ x₅₀) (f₁₈ x₅₁ x₅₂)) (f₁₉ (f₂₀ x₅₃ x₅₄) (f₂₁ x₅₅ x₅₆)))
        (f₂₂ (f₂₃ (f₂₄ x₅₇ x₅₈) (f₂₅ x₅₉ x₆₀)) (f₂₆ (f₂₇ x₆₁ x₆₂) (f₂₈ x₆₃ x₆₄))))))
  (H₃₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
       ∀ x₁₇, ∃ x₁₈, ∀ x₁₉, ∃ x₂₀, ∀ x₂₁, ∃ x₂₂, ∀ x₂₃, ∃ x₂₄,
       ∀ x₂₅, ∃ x₂₆, ∀ x₂₇, ∃ x₂₈, ∀ x₂₉, ∃ x₃₀, ∀ x₃₁, ∃ x₃₂,
       ∀ x₃₃, ∃ x₃₄, ∀ x₃₅, ∃ x₃₆, ∀ x₃₇, ∃ x₃₈, ∀ x₃₉, ∃ x₄₀,
       ∀ x₄₁, ∃ x₄₂, ∀ x₄₃, ∃ x₄₄, ∀ x₄₅, ∃ x₄₆, ∀ x₄₇, ∃ x₄₈,
       ∀ x₄₉, ∃ x₅₀, ∀ x₅₁, ∃ x₅₂, ∀ x₅₃, ∃ x₅₄, ∀ x₅₅, ∃ x₅₆,
       ∀ x₅₇, ∃ x₅₈, ∀ x₅₉, ∃ x₆₀, ∀ x₆₁, ∃ x₆₂, ∀ x₆₃, ∃ x₆₄,
    (g₃ (g₃ (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)))
      (f₈ (f₉ (f₁₀ x₉ x₁₀) (f₁₁ x₁₁ x₁₂)) (f₁₂ (f₁₃ x₁₃ x₁₄) (f₁₄ x₁₅ x₁₆))))
      (g₃ (f₁₅ (f₁₆ (f₁₇ x₁₇ x₁₈) (f₁₈ x₁₉ x₂₀)) (f₁₉ (f₂₀ x₂₁ x₂₂) (f₂₁ x₂₃ x₂₄)))
        (f₂₂ (f₂₃ (f₂₄ x₂₅ x₂₆) (f₂₅ x₂₇ x₂₈)) (f₂₆ (f₂₇ x₂₉ x₃₀) (f₂₈ x₃₁ x₃₂))))) =
    (g₄ (g₄ (f₁ (f₂ (f₃ x₃₃ x₃₄) (f₄ x₃₅ x₃₆)) (f₅ (f₆ x₃₇ x₃₈) (f₇ x₃₉ x₄₀)))
      (f₈ (f₉ (f₁₀ x₄₁ x₄₂) (f₁₁ x₄₃ x₄₄)) (f₁₂ (f₁₃ x₄₅ x₄₆) (f₁₄ x₄₇ x₄₈))))
      (g₄ (f₁₅ (f₁₆ (f₁₇ x₄₉ x₅₀) (f₁₈ x₅₁ x₅₂)) (f₁₉ (f₂₀ x₅₃ x₅₄) (f₂₁ x₅₅ x₅₆)))
        (f₂₂ (f₂₃ (f₂₄ x₅₇ x₅₈) (f₂₅ x₅₉ x₆₀)) (f₂₆ (f₂₇ x₆₁ x₆₂) (f₂₈ x₆₃ x₆₄))))))
  (G₁ : ∀ x y, g₁ x y = a₁)
  (G₂ : ∀ x y, g₂ x y = a₂)
  (G₃ : ∀ x y, g₃ x y = a₃)
  (G₄ : ∀ x y, g₃ x y = a₄) : a₁ = a₄ := by auto

theorem test₁ (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ : Nat → Nat → Nat)
  (H₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₅) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₅) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₆) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₆) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₈) (f₇ x₅ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₈) (f₇ x₆ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₅) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₅) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₆) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₆) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₇) (f₇ x₅ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
       ∀ x₉, ∃ x₁₀, ∀ x₁₁, ∃ x₁₂, ∀ x₁₃, ∃ x₁₄, ∀ x₁₅, ∃ x₁₆,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₇) (f₇ x₆ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉)))) :
  True := by auto

#check 2

set_option trace.auto.buildChecker true in
theorem test₂ (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ : Nat → Nat → Nat)
  (x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ : Nat)
  (H₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₅) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₅) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₆) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₆) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₈) (f₇ x₅ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₇ x₈) (f₇ x₆ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₅) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₅) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₆) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₆) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₇) (f₇ x₅ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₈ x₇) (f₇ x₆ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉)))) :
  True := by auto

#check 2

set_option trace.auto.buildChecker true in
theorem test₃ (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ : Nat → Nat → Nat)
  (x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ : Nat)
  (H₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₃ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₆ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₄ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₇) (f₇ x₈ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₅ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₆ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₆ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₈) (f₇ x₇ x₆)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₇ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₇ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₈ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₅) (f₇ x₈ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₉ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₅ x₈)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₀ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₇) (f₇ x₈ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₁ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₅ x₇)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉))))
  (H₁₂ : ∀ x₁, ∃ x₂, ∀ x₃, ∃ x₄, ∀ x₅, ∃ x₆, ∀ x₇, ∃ x₈,
    (f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₆ x₈) (f₇ x₇ x₅)) =
      f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁ (f₂ x₄ x₃) (f₃ x₂ x₁))) =
    (f₄ (f₅ (f₆ x₉ x₁₀) (f₇ x₁₁ x₁₂)) (f₈ (f₉ x₁₃ x₁₄) (f₁₀ x₁₅ x₁₆)) =
      f₁₁ (f₁ (f₂ x₁₆ x₁₅) (f₃ x₁₄ x₁₃)) (f₄ (f₅ x₁₂ x₁₁) (f₆ x₁₀ x₉)))) :
  True := by auto

#check 2
