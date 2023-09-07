namespace Auto

theorem heq_of_cast_eq : ∀ (e : α = β) (_ : cast e a = a'), HEq a a'
  | rfl, h => Eq.recOn h (HEq.refl _)

def HEq.tyEq {α β : Sort u} (x : α) (y : β) (H : HEq x y) : α = β :=
  match β, y, H with
  | .(α), .(x), HEq.refl _ => Eq.refl _

def HEq.funext {γ : Sort u} {α β : γ → Sort v}
  (x : ∀ (u : γ), α u) (y : ∀ (u : γ), β u) (H : ∀ u, HEq (x u) (y u)) : HEq x y :=
  (fun αβEq : α = β =>
    match β, αβEq with
    | .(α), Eq.refl _ =>
      let xyEq : x = y := _root_.funext (fun u => eq_of_heq (H u))
      match xyEq with
      | Eq.refl _ => HEq.refl _) (_root_.funext (fun u => HEq.tyEq _ _ (H u)))

theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
  (h₁ : HEq f g) (h₂ : HEq x y) : f x = g y := by
  cases h₂; cases h₁; rfl

theorem congr_h_heq {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {x₁ : α₁} {x₂ : α₂}
  (Hβ : β₁ = β₂) (h₁ : HEq f₁ f₂) (h₂ : HEq x₁ x₂) : HEq (f₁ x₁) (f₂ x₂) := by
  cases h₂; cases Hβ; cases h₁; apply HEq.rfl

theorem congr₂_h_heq
  {f₁ : α₁ → β₁ → γ₁} {f₂ : α₂ → β₂ → γ₂}
  {x₁ : α₁} {x₂ : α₂} {y₁ : β₁} {y₂ : β₂}
  (Hγ : γ₁ = γ₂) (h₁ : HEq f₁ f₂) (h₂ : HEq x₁ x₂) (h₃ : HEq y₁ y₂) :
  HEq (f₁ x₁ y₁) (f₂ x₂ y₂) := by
  cases h₂; cases h₃; cases Hγ; cases h₁; apply HEq.rfl

theorem congr_hd_heq
  {β₁ : α₁ → Sort u} {β₂ : α₂ → Sort u}
  {f₁ : ∀ (x : α₁), β₁ x} {f₂ : ∀ (x : α₂), β₂ x} {x₁ : α₁} {x₂ : α₂}
  (Hβ : HEq β₁ β₂) (h₁ : HEq f₁ f₂) (h₂ : HEq x₁ x₂) : HEq (f₁ x₁) (f₂ x₂) := by
  cases h₂; cases Hβ; cases h₁; apply HEq.rfl

theorem congr_arg_heq {α} {β : α → Sort _} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → HEq (f a₁) (f a₂)
  | _, _, rfl => HEq.rfl

theorem congr_fun_heq {α} {β₁ β₂ : α → Sort _} {f₁ : ∀ a, β₁ a} {f₂ : ∀ a, β₂ a}
  {x₁ x₂ : α} (hβ : β₁ = β₂) (h₁ : HEq f₁ f₂) (h₂ : x₁ = x₂) : HEq (f₁ x₁) (f₂ x₂) := by
  cases hβ; cases h₁; cases h₂; apply HEq.rfl

theorem heq_of_eqRec_eq' {motive : γ → Sort u} {α β : γ} (h₁ : α = β)
  (a : motive α) : HEq a (@Eq.rec γ α (fun α _ => motive α) a β h₁) := by
  subst h₁
  apply HEq.refl

theorem eq_sigma_of_heq {p : α → Type v} {ty₁ ty₂ : α} {val₁ : p ty₁} {val₂ : p ty₂}
  (h₁ : ty₁ = ty₂) (h₂ : HEq val₁ val₂) : @Eq ((x : α) × (p x)) ⟨ty₁, val₁⟩ ⟨ty₂, val₂⟩ := by
  cases h₁; cases h₂; rfl

theorem heq_of_eq_sigma {p : α → Type v} {ty₁ ty₂ : α} {val₁ : p ty₁} {val₂ : p ty₂}
  (h : @Eq ((x : α) × (p x)) ⟨ty₁, val₁⟩ ⟨ty₂, val₂⟩) : ty₁ = ty₂ ∧ HEq val₁ val₂ := by
  cases h; apply And.intro; rfl; apply HEq.refl

theorem eqRec_heq' {α : Sort u_1} {a' : α} {motive : (a : α) → a' = a → Sort u}
    (p : motive a' (rfl : a' = a')) {a : α} (t : a' = a) :
    HEq (@Eq.rec α a' motive p a t) p :=
  by subst t; apply HEq.refl

theorem congr_arg₂_heq {β : α → Sort _} (γ : ∀ (a : α), β a → Sort _)
  (f : ∀ (a : α) (b : β a), γ a b) {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
  (H₁ : a₁ = a₂) (H₂ : HEq b₁ b₂) : HEq (f a₁ b₁) (f a₂ b₂) := by
  subst H₁
  cases H₂
  apply HEq.refl

end Auto