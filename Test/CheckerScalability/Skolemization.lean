import Auto.Tactic

set_option profiler true
set_option auto.optimizeCheckerProof false
set_option compiler.enableNew false
set_option auto.checker.buildMode "smallstep_reflection"

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
