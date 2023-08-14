namespace Auto

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

theorem congr_arg_heq {α} {β : α → Sort _} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → HEq (f a₁) (f a₂)
  | _, _, rfl => HEq.rfl

theorem heq_of_eqRec_eq' {motive : γ → Sort u} {α β : γ} (h₁ : α = β)
  (a : motive α) : HEq a (@Eq.rec γ α (fun α _ => motive α) a β h₁) := by
  subst h₁
  apply HEq.refl

theorem congr_arg₂_heq {β : α → Sort _} (γ : ∀ (a : α), β a → Sort _)
  (f : ∀ (a : α) (b : β a), γ a b) {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
  (H₁ : a₁ = a₂) (H₂ : HEq b₁ b₂) : HEq (f a₁ b₁) (f a₂ b₂) := by
  subst H₁
  cases H₂
  apply HEq.refl

end Auto