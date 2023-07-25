inductive DepEq {α : Sort u} (f : α → Sort v) : {x : α} → (a : f x) → {y : α} → (b : f y) → Prop where
  /-- Reflexivity of heterogeneous equality. -/
  | refl (x : α) (a : f x) : DepEq f a a

@[match_pattern] protected def DepEq.rfl {α : Sort u} (f : α → Sort v) {x : α} {a : f x} :=
  DepEq.refl x a

theorem DepEq.ndrec {α : Sort u} (f : α → Sort v) (x : α) (a : f x)
  {motive : {x : α} → f x → Sort w} (m : motive a)
  {y : α} (b : f y) (h : DepEq f a b) : motive b := by
  cases h; case refl => exact m

def DepEq.subst {α : Sort u} (f : α → Sort v) (x y : α) (a : f x) (b : f y)
  {p : (x : α) → f x → Prop} (h₁ : DepEq f a b) (h₂ : p x a) : p y b :=
  @DepEq.ndrec α f x a (fun {x : α} a => p x a) h₂ y b h₁

def heq_of_depeq {α : Sort u} (f : α → Sort v)
  {x : α} {a : f x} {x' : α} {a' : f x'} (h : DepEq f a a') : HEq a a' :=
  @DepEq.ndrec α f x a (fun {y : α} (b : f y) => HEq a b) HEq.rfl x' a' h

def depeq_of_eq {α : Sort u} (f : α → Sort v)
  {x : α} {a a' : f x} (h : Eq a a') : DepEq f a a' :=
  Eq.mpr (h ▸ Eq.refl (DepEq f a a')) (DepEq.refl x a')

def eq_of_depeq {α : Sort u} (f : α → Sort v)
  {x : α} {a b : f x} (h : DepEq f a b) : a = b :=
  eq_of_heq (heq_of_depeq f h)

def DepEq.transferF {α : Sort u} {β : Sort v}
  (g : α → β) (h : β → Sort w) {x : α} (a : h (g x)) {y : α} (b : h (g y))
  (H : DepEq (fun x => h (g x)) a b) : DepEq h a b :=
  @DepEq.ndrec α (fun x => h (g x)) x a (fun {_} b => DepEq h a b) (DepEq.rfl _) y b H

def depeq_of_heq {α : Sort u} (f : α → Sort v)
  {x : α} {a : f x} {x' : α} {a' : f x'} (h : HEq a a') (h' : x = x') : DepEq f a a' :=
  by cases h'; cases h; apply DepEq.rfl

def depeq_of_heq' (f : Sort v → Sort v)
  {x : Sort v} {a : f x} {x' : Sort v} {a' : f x'} (h : HEq a a') (H : f = id) : DepEq f a a' :=
  by cases H; simp at h; cases h; apply DepEq.rfl

-- Rename so that it does not clash with `funext` during the proof
private def DepEq.funext_Aux {α : Sort u} {β : Sort v} (γ : α → β → Sort w) :
  let F := fun (x : α) => (∀ (u : β), γ x u)
  (x : α) → (f : F x) → (y : α) → (g : F y) →
  (h₁ : x = y) → (h₂ : ∀ (u : β), DepEq (fun k => γ k u) (f u) (g u))
  → DepEq F f g := by
  simp; intro x f y g HEq HDepEq
  cases HEq;
  case refl =>
    have allEq : ∀ (u : β), f u = g u := fun u =>
      let F := fun (k : α) => γ k u;
      (@eq_of_depeq (α:=α) (f:=F) (x:=x) (a:=f u) (b:=g u) (HDepEq u))
    have funEq : f = g := funext allEq
    cases funEq; case refl => apply DepEq.rfl

def DepEq.funext {α : Sort u} {β : Sort v} (γ : α → β → Sort w) :=
  @DepEq.funext_Aux α β γ