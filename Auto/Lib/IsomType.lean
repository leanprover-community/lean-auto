namespace Auto

structure IsomType (α : Sort u) (β : Sort v) where
  f : α → β
  g : β → α
  eq₁ : ∀ (x : α), g (f x) = x
  eq₂ : ∀ (x : β), f (g x) = x

def IsomType.substForall {p : α → Sort u} (I : IsomType α β)
  (H : ∀ (x : α), p x) : ∀ (x : β), p (I.g x) := fun _ => H _

def IsomType.substForallRev {p : α → Sort u} (I : IsomType α β)
  (H : ∀ (x : β), p (I.g x)) : ∀ (x : α), p x := fun x => Eq.mp (by rw [I.eq₁]) (H (I.f x))

def IsomType.eqForall {p : α → Prop} (I : IsomType α β) :
  (∀ (x : α), p x) ↔ (∀ (x : β), p (I.g x)) :=
  Iff.intro (substForall I) (fun h x => Eq.mp (by rw [I.eq₁]) (h (I.f x)))

def IsomType.substForall' {p : β → Sort u} (I : IsomType α β)
  (H : ∀ (x : β), p x) : ∀ (x : α), p (I.f x) := fun _ => H _

def IsomType.substForallRev' {p : β → Sort u} (I : IsomType α β)
  (H : ∀ (x : α), p (I.f x)) : ∀ (x : β), p x := fun x => Eq.mp (by rw [I.eq₂]) (H (I.g x))

def IsomType.eqForall' {p : β → Prop} (I : IsomType α β) :
  (∀ (x : β), p x) ↔ (∀ (x : α), p (I.f x)) :=
  Iff.intro (substForall' I) (fun h x => Eq.mp (by rw [I.eq₂]) (h (I.g x)))

def IsomType.eqExists {p : α → Prop} (I : IsomType α β) :
  (∃ (x : α), p x) ↔ (∃ (x : β), p (I.g x)) :=
  Iff.intro (fun ⟨x, h⟩ => ⟨I.f x, I.eq₁ _ ▸ h⟩) (fun ⟨x, h⟩ => ⟨I.g x, h⟩)

def IsomType.eqExists' {p : β → Prop} (I : IsomType α β) :
  (∃ (x : β), p x) ↔ (∃ (x : α), p (I.f x)) :=
  Iff.intro (fun ⟨x, h⟩ => ⟨I.g x, I.eq₂ _ ▸ h⟩) (fun ⟨x, h⟩ => ⟨I.f x, h⟩)

def Prod.eqForall {p : α × β → Prop} :
  (∀ (x : α × β), p x) ↔ (∀ (x : α) (y : β), p (x, y)) :=
  Iff.intro (fun h x y => h (x, y)) (fun h (x, y) => h x y)

def Prod.eqExist {p : α × β → Prop} :
  (∃ (x : α × β), p x) ↔ (∃ (x : α) (y : β), p (x, y)) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨x, ⟨y, h⟩⟩) (fun ⟨x, ⟨y, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

def Prod.eqForall' {p : α × β → Prop} :
  (∀ (x : α × β), p x) ↔ (∀ (y : β) (x : α), p (x, y)) :=
  Iff.intro (fun h y x => h (x, y)) (fun h (y, x) => h x y)

def Prod.eqExist' {p : α × β → Prop} :
  (∃ (x : α × β), p x) ↔ (∃ (y : β) (x : α), p (x, y)) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨y, ⟨x, h⟩⟩) (fun ⟨y, ⟨x, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

def PProd.eqForall {p : PProd α β → Prop} :
  (∀ (x : PProd α β), p x) ↔ (∀ (x : α) (y : β), p ⟨x, y⟩) :=
  Iff.intro (fun h x y => h ⟨x, y⟩) (fun h ⟨x, y⟩ => h x y)

def PProd.eqExist {p : PProd α β → Prop} :
  (∃ (x : PProd α β), p x) ↔ (∃ (x : α) (y : β), p ⟨x, y⟩) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨x, ⟨y, h⟩⟩) (fun ⟨x, ⟨y, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

def PProd.eqForall' {p : PProd α β → Prop} :
  (∀ (x : PProd α β), p x) ↔ (∀ (y : β) (x : α), p ⟨x, y⟩) :=
  Iff.intro (fun h y x => h ⟨x, y⟩) (fun h ⟨y, x⟩ => h x y)

def PProd.eqExist' {p : PProd α β → Prop} :
  (∃ (x : PProd α β), p x) ↔ (∃ (y : β) (x : α), p ⟨x, y⟩) :=
  Iff.intro (fun ⟨⟨x, y⟩, h⟩ => ⟨y, ⟨x, h⟩⟩) (fun ⟨y, ⟨x, h⟩⟩ => ⟨⟨x, y⟩, h⟩)

def PUnit.eqForall {p : PUnit → Prop} : (∀ (x : PUnit), p x) ↔ p .unit :=
  Iff.intro (fun h => h .unit) (fun h x => match x with | .unit => h)

def PUnit.eqExist {p : PUnit → Prop} : (∃ (x : PUnit), p x) ↔ p .unit :=
  Iff.intro (fun ⟨_, h⟩ => h) (fun h => ⟨.unit, h⟩)

end Auto