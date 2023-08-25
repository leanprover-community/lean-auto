namespace Auto.Embedding

structure GLift.{u, v} (α : Sort u) : Sort (max u (v + 1)) where
  /-- Lift a value into `GLift α` -/    up ::
  /-- Extract a value from `GLift α` -/ down : α

def GLift.down.inj (x y : GLift α) (H : GLift.down x = GLift.down y) : x = y :=
  show GLift.up (GLift.down x) = GLift.up (GLift.down y) by rw [H]

def notLift.{u} (p : GLift.{1, u} Prop) :=
  GLift.up (Not p.down)

def andLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (And p.down q.down)

def orLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Or p.down q.down)

def iffLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Iff p.down q.down)

@[reducible] def ImpF.{u, v} (p : Sort u) (q : Sort v) := p → q

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
def eqLift.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β) (x y : β) :=
  GLift.up.{_, w} (I.g x = I.g y)

def eqLift_refl.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β) (x : β) :
  GLift.down (eqLift.{u, v, w} I x x) := rfl

def eqLift.down.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β)
  (x y : β) (H : GLift.down (eqLift.{u, v, w} I x y)) : x = y := 
  let H₁ : I.f (I.g x) = I.f (I.g y) := H ▸ rfl
  let H₂ : x = I.f (I.g y) := I.eq₂ x ▸ H₁
  I.eq₂ y ▸ H₂

def eqLift.up.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β)
  (x y : β) (H : x = y) : GLift.down (eqLift.{u, v, w} I x y) :=
  H ▸ eqLift_refl.{u, v, w} I x

structure EqLift (β : Sort u) where
  eqF  : β → β → GLift.{1, v} Prop
  down : ∀ (x y : β), (eqF x y).down → x = y
  up   : ∀ (x y : β), x = y → (eqF x y).down

def EqLift.ofIsomTy {α : Sort u} {β : Sort v} (I : IsomType α β) : EqLift.{v, w} β :=
  ⟨eqLift.{u, v, w} I, eqLift.down.{u, v, w} I, eqLift.up.{u, v, w} I⟩

def eqLiftFn.{u} {β : Type u} (x y : β) := GLift.up.{1, u} (@Eq β x y)

def EqLift.default (β : Sort u) : EqLift β :=
  ⟨fun x y => GLift.up (@Eq β x y), fun _ _ => id, fun _ _ => id⟩

@[reducible] def forallF {α : Sort u} (p : α → Sort v) := ∀ (x : α), p x

-- Isomorphic domain, β is the lifted one
def forallLift.{u, v, w, x} {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, x} (Sort w)) :=
  GLift.up.{(imax u w) + 1, x} (∀ (x : α), GLift.down (p (I.f x)))

def forallLift.down.{u, v, w, x}
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, x} (Sort w)) (H : GLift.down (forallLift I p))
  (x : β) : GLift.down (p x) :=
  I.eq₂ x ▸ H (I.g x)

def forallLift.up
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, x} (Sort w))
  (H : ∀ (x : β), GLift.down (p x)) : GLift.down (forallLift I p) :=
  fun x => I.eq₁ x ▸ H (I.f x)

structure ForallLift (β : Sort v') where
  forallF : (β → GLift.{w + 1, v} (Sort w)) → GLift.{w' + 1, v} (Sort w')
  down    : ∀ (p : β → GLift.{w + 1, v} (Sort w)), (forallF p).down → (∀ x : β, (p x).down)
  up      : ∀ (p : β → GLift.{w + 1, v} (Sort w)), (∀ x : β, (p x).down) → (forallF p).down
 
def ForallLift.ofIsomTy.{u, v, w, x} {α : Sort u} {β : Sort v} (I : IsomType α β) : ForallLift β :=
  ⟨forallLift.{u, v, w, x} I, forallLift.down I, forallLift.up I⟩

def forallLiftFn.{u} (β : Type u) (p : β → GLift.{1, u} Prop) := GLift.up.{1, u} (∀ x, GLift.down (p x))

def ForallLift.default (β : Sort v') : ForallLift.{v', v, w, imax v' w} β :=
  ⟨fun (p : β → GLift.{w + 1, v} (Sort w)) => GLift.up (∀ (x : β), GLift.down (p x)), fun _ => id, fun _ => id⟩

-- Isomorphic domain, β is the lifted one
def existLift {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, x} Prop) :=
  GLift.up.{_, x} (∃ (x : α), GLift.down (p (I.f x)))

def existLift.down
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, x} Prop)
  (H : GLift.down (existLift I p)) : ∃ x, GLift.down (p x) := by
  cases H; case intro x proof => exists I.f x;

def existLift.up
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, x} Prop)
  (H : ∃ x, GLift.down (p x)) : GLift.down (existLift I p) := by
  cases H; case intro x proof => exists I.g x; rw [I.eq₂]; exact proof

structure ExistLift (β : Sort v') where
  existF  : (β → GLift.{1, v} Prop) → GLift.{1, v} Prop
  down    : ∀ (p : β → GLift.{1, v} Prop), (existF p).down → (∃ x : β, (p x).down)
  up      : ∀ (p : β → GLift.{1, v} Prop), (∃ x : β, (p x).down) → (existF p).down

def ExistLift.ofIsomTy.{u, v, x} {α : Sort u} {β : Sort v} (I : IsomType α β) : ExistLift β :=
  ⟨existLift.{u, v, x} I, existLift.down I, existLift.up I⟩

def existLiftFn.{u} (β : Type u) (p : β → GLift.{1, u} Prop) := GLift.up.{1, u} (∃ x, GLift.down (p x))

def ExistLift.default (β : Sort v') : ExistLift.{v', w} β :=
  ⟨fun (p : β → GLift.{1, w} Prop) => GLift.up (∃ (x : β), GLift.down (p x)), fun _ => id, fun _ => id⟩

-- !! First generalization (of `EqLift`)
--
-- structure FLift (β : Sort u) (f : ∀ (α : Sort u), α → α → Prop) where
--   fF   : β → β → Prop
--   down : ∀ (x y : β), fF x y → f β x y
--   up   : ∀ (x y : β), f β x y → fF x y
--
-- !! Rewrite of the above `FLift`
--
-- structure FLift (β : Sort u) (f : ∀ (α : Sort u), PProd α α → Prop) where
--   fF   : PProd β β → Prop
--   down : ∀ (x y : β), fF ⟨x, y⟩ → f β ⟨x, y⟩
--   up   : ∀ (x y : β), f β ⟨x, y⟩ → fF ⟨x, y⟩
--
-- !!Second Generalization (of the above `FLift`)
--
-- structure FLift (β : Sort u) (γ : Sort u → Sort u) (f : ∀ (α : Sort u), γ α → Prop) where
--   fF   : γ β → Prop
--   down : ∀ (x : γ β), fF x → f β x
--   up   : ∀ (x : γ β), f β x → fF x

end Auto.Embedding