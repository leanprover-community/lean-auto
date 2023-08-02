namespace Auto.Embedding

structure GLift.{u, v} (α : Sort u) : Sort (max u (v + 1)) where
  /-- Lift a value into `GLift α` -/    up ::
  /-- Extract a value from `GLift α` -/ down : α

def notLift.{u} (p : GLift.{1, u} Prop) :=
  GLift.up (Not p.down)

def andLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (And p.down q.down)

def orLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Or p.down q.down)

def iffLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Iff p.down q.down)

def ImpF.{u, v} (p : Sort u) (q : Sort v) := p → q

def impLift.{u}
  (p : GLift.{t + 1, v} (Sort t))
  (q : GLift.{u + 1, v} (Sort u)) :=
  GLift.up (p.down → q.down)

def LiftTyConv.{u, v} (tyUp : GLift.{u + 1, v} (Sort u)) :=
  GLift.{u, v} (GLift.down.{u + 1, v} tyUp)

structure IsomType (α : Sort u) (β : Sort v) where
  f : α → β
  g : β → α
  eq₁ : ∀ (x : α), g (f x) = x
  eq₂ : ∀ (x : β), f (g x) = x

-- Isomorphic domain, β is the lifted one
def eqLift {α : Sort u} {β : Sort v} (I : IsomType α β) (x y : β) :=
  GLift.up.{_, v} (I.g x = I.g y)

def eqLift_refl {α : Sort u} {β : Sort v} (I : IsomType α β) (x : β) :
  GLift.down (eqLift I x x) := rfl

def eqLift.down {α : Sort u} {β : Sort v} (I : IsomType α β)
  (x y : β) (H : GLift.down (eqLift I x y)) : x = y := 
  let H₁ : I.f (I.g x) = I.f (I.g y) := H ▸ rfl
  let H₂ : x = I.f (I.g y) := I.eq₂ x ▸ H₁
  I.eq₂ y ▸ H₂

def eqLift.up {α : Sort u} {β : Sort v} (I : IsomType α β)
  (x y : β) (H : x = y) : GLift.down (eqLift I x y) :=
  H ▸ eqLift_refl I x

structure EqLift (β : Sort u) where
  eqF  : β → β → GLift.{1, v} Prop
  down : ∀ (x y : β), (eqF x y).down → x = y
  up   : ∀ (x y : β), x = y → (eqF x y).down

def EqLift.ofEqLift {α : Sort u} {β : Sort v} (I : IsomType α β) : EqLift β :=
  ⟨eqLift I, eqLift.down I, eqLift.up I⟩

def forallF {α : Sort u} (p : α → Sort v) := ∀ (x : α), p x

-- Isomorphic domain, β is the lifted one
def forallLift {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, v} (Sort w)) :=
  GLift.up.{(imax u w) + 1, v} (∀ (x : α), GLift.down (p (I.f x)))

def forallLift.down
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, v} (Sort w)) (H : GLift.down (forallLift I p))
  (x : β) : GLift.down (p x) :=
  I.eq₂ x ▸ H (I.g x)

def forallLift.up
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, v} (Sort w))
  (H : ∀ (x : β), GLift.down (p x)) : GLift.down (forallLift I p) :=
  fun x => I.eq₁ x ▸ H (I.f x)

structure ForallLift (β : Sort v') where
  forallF : (β → GLift.{w + 1, v} (Sort w)) → GLift.{_, v} (Sort w')
  down    : ∀ (p : β → GLift.{w + 1, v} (Sort w)), (forallF p).down → (∀ x : β, (p x).down)
  up      : ∀ (p : β → GLift.{w + 1, v} (Sort w)), (∀ x : β, (p x).down) → (forallF p).down

def ForallLift.ofForallLift.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β) : ForallLift β :=
  ⟨forallLift.{u, v, w} I, forallLift.down I, forallLift.up I⟩

-- Isomorphic domain, β is the lifted one
def existLift {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, v} Prop) :=
  GLift.up.{_, v} (∃ (x : α), GLift.down (p (I.f x)))

def existLift.down
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, v} Prop)
  (H : GLift.down (existLift I p)) : ∃ x, GLift.down (p x) := by
  cases H; case intro x proof => exists I.f x;

def existLift.up
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, v} Prop)
  (H : ∃ x, GLift.down (p x)) : GLift.down (existLift I p) := by
  cases H; case intro x proof => exists I.g x; rw [I.eq₂]; exact proof

structure ExistLift (β : Sort v') where
  existF  : (β → GLift.{1, v} Prop) → GLift.{1, v} Prop
  down    : ∀ (p : β → GLift.{1, v} Prop), (existF p).down → (∃ x : β, (p x).down)
  up      : ∀ (p : β → GLift.{1, v} Prop), (∃ x : β, (p x).down) → (existF p).down

def ExistLift.ofExistLift.{u, v} {α : Sort u} {β : Sort v} (I : IsomType α β) : ExistLift β :=
  ⟨existLift.{u, v} I, existLift.down I, existLift.up I⟩

end Auto.Embedding