namespace Auto

structure IsomType (α : Sort u) (β : Sort v) where
  f : α → β
  g : β → α
  eq₁ : ∀ (x : α), g (f x) = x
  eq₂ : ∀ (x : β), f (g x) = x

theorem IsomType.substForall {p : α → Sort u} (I : IsomType α β)
  (H : ∀ (x : α), p x) : ∀ (x : β), p (I.g x) := fun _ => H _

theorem IsomType.eqForall {p : α → Prop} (I : IsomType α β) :
  (∀ (x : α), p x) ↔ (∀ (x : β), p (I.g x)) :=
  Iff.intro (substForall I) (fun h x => Eq.mp (by rw [I.eq₁]) (h (I.f x)))

theorem IsomType.substForall' {p : β → Sort u} (I : IsomType α β)
  (H : ∀ (x : β), p x) : ∀ (x : α), p (I.f x) := fun _ => H _

theorem IsomType.eqForall' {p : β → Prop} (I : IsomType α β) :
  (∀ (x : β), p x) ↔ (∀ (x : α), p (I.f x)) :=
  Iff.intro (substForall' I) (fun h x => Eq.mp (by rw [I.eq₂]) (h (I.g x)))

theorem IsomType.eqExists {p : α → Prop} (I : IsomType α β) :
  (∃ (x : α), p x) ↔ (∃ (x : β), p (I.g x)) :=
  Iff.intro (fun ⟨x, h⟩ => ⟨I.f x, I.eq₁ _ ▸ h⟩) (fun ⟨x, h⟩ => ⟨I.g x, h⟩)

theorem IsomType.eqExists' {p : β → Prop} (I : IsomType α β) :
  (∃ (x : β), p x) ↔ (∃ (x : α), p (I.f x)) :=
  Iff.intro (fun ⟨x, h⟩ => ⟨I.g x, I.eq₂ _ ▸ h⟩) (fun ⟨x, h⟩ => ⟨I.f x, h⟩)

theorem Prod.eqForall {p : α × β → Prop} :
  (∀ (x : α × β), p x) ↔ (∀ (x : α) (y : β), p (x, y)) :=
  Iff.intro (fun h x y => h (x, y)) (fun h (x, y) => h x y)

theorem Prod.eqExist {p : α × β → Prop} :
  (∃ (x : α × β), p x) ↔ (∃ (x : α) (y : β), p (x, y)) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨x, ⟨y, h⟩⟩) (fun ⟨x, ⟨y, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

theorem Prod.eqForall' {p : α × β → Prop} :
  (∀ (x : α × β), p x) ↔ (∀ (y : β) (x : α), p (x, y)) :=
  Iff.intro (fun h y x => h (x, y)) (fun h (y, x) => h x y)

theorem Prod.eqExist' {p : α × β → Prop} :
  (∃ (x : α × β), p x) ↔ (∃ (y : β) (x : α), p (x, y)) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨y, ⟨x, h⟩⟩) (fun ⟨y, ⟨x, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

theorem PProd.eqForall {p : PProd α β → Prop} :
  (∀ (x : PProd α β), p x) ↔ (∀ (x : α) (y : β), p ⟨x, y⟩) :=
  Iff.intro (fun h x y => h ⟨x, y⟩) (fun h ⟨x, y⟩ => h x y)

theorem PProd.eqExist {p : PProd α β → Prop} :
  (∃ (x : PProd α β), p x) ↔ (∃ (x : α) (y : β), p ⟨x, y⟩) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨x, ⟨y, h⟩⟩) (fun ⟨x, ⟨y, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

theorem PProd.eqForall' {p : PProd α β → Prop} :
  (∀ (x : PProd α β), p x) ↔ (∀ (y : β) (x : α), p ⟨x, y⟩) :=
  Iff.intro (fun h y x => h ⟨x, y⟩) (fun h ⟨y, x⟩ => h x y)

theorem PProd.eqExist' {p : PProd α β → Prop} :
  (∃ (x : PProd α β), p x) ↔ (∃ (y : β) (x : α), p ⟨x, y⟩) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨y, ⟨x, h⟩⟩) (fun ⟨y, ⟨x, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

theorem PUnit.eqForall {p : PUnit → Prop} : (∀ (x : PUnit), p x) ↔ p .unit :=
  Iff.intro (fun h => h .unit) (fun h x => match x with | .unit => h)

theorem PUnit.eqExist {p : PUnit → Prop} : (∃ (x : PUnit), p x) ↔ p .unit :=
  Iff.intro (fun ⟨_, h⟩ => h) (fun h => ⟨.unit, h⟩)

end Auto