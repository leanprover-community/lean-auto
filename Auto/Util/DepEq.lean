inductive DepEq {α : Sort u} (f : α → Sort v) : {x : α} → (a : f x) → {y : α} → (b : f y) → Prop where
  /-- Reflexivity of heterogeneous equality. -/
  | refl (x : α) (a : f x) : DepEq f a a

@[match_pattern] protected def DepEq.rfl {α : Sort u} (f : α → Sort v) {x : α} {a : f x} :=
  DepEq.refl x a

def DepEq.ofSigmaEq {α : Type u} (f : α → Type v) (x : α) (a : f x)
  (y : α) (b : f y) (H : Sigma.mk (β:=f) x a = Sigma.mk (β:=f) y b) : DepEq f a b :=
  by cases H; apply DepEq.refl

def DepEq.toSigmaEq {α : Type u} (f : α → Type v) (x : α) (a : f x)
  (y : α) (b : f y) (H : DepEq f a b) : Sigma.mk (β:=f) x a = Sigma.mk (β:=f) y b :=
  by cases H; rfl

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

set_option genInjectivity false in
inductive SigmaFn : Nat → Type 1
  | mk (α : Type) (fn : α → Nat) (arg : α) : SigmaFn (fn arg)

def HEq.ofSigmaEq {α β : Type u} (x : α) (y : β) (H : @Sigma.mk _ id _ x = @Sigma.mk _ id _ y) : HEq x y :=
  by cases H; apply HEq.rfl

def HEq.toSigmaEq {α β : Type u} (x : α) (y : β) (H : HEq x y) : @Sigma.mk _ id _ x = @Sigma.mk _ id _ y :=
  by cases H; rfl

theorem SigmaFn.inj {α : Type} {fn : α → Nat} {arg : α} {fn_1 : α_1 → Nat} {arg_1 : α_1}
  (H : DepEq SigmaFn (SigmaFn.mk α fn arg) (SigmaFn.mk α_1 fn_1 arg_1)) : α = α_1 ∧ HEq arg arg_1 ∧ HEq fn fn_1 :=
  let lh : Sigma SigmaFn := { fst := fn arg, snd := mk α fn arg }
  let rh : Sigma SigmaFn := { fst := fn_1 arg_1, snd := mk α_1 fn_1 arg_1 }
  let lreq : lh = rh := DepEq.toSigmaEq _ _ _ _ _ H
  let rwFn₁ (x : Sigma SigmaFn) : Sigma id :=
    match x with
    | Sigma.mk fst snd =>
      match snd with
      | SigmaFn.mk α fn arg => ⟨α, arg⟩
  let rwRes₁ : rwFn₁ lh = rwFn₁ rh := by rw [lreq]
  let argHeq := HEq.ofSigmaEq _ _ rwRes₁;
  let rwFn₂ (x : Sigma SigmaFn) : Sigma id :=
    match x with
    | Sigma.mk fst snd =>
      match snd with
      | SigmaFn.mk α fn arg => ⟨α → Nat, fn⟩
  let rwRes₂ : rwFn₂ lh = rwFn₂ rh := by rw [lreq]
  let fnHeq := HEq.ofSigmaEq _ _ rwRes₂;
  And.intro (by cases argHeq; rfl) (And.intro argHeq fnHeq)
