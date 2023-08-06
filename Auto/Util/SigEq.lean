def HEq.ofSigmaEq {α β : Type u} (x : α) (y : β) (H : @Sigma.mk _ id _ x = @Sigma.mk _ id _ y) : HEq x y :=
  match β, y, H with
  | .(α), .(x), Eq.refl _ => HEq.refl _

def HEq.ofPSigmaEq {α β : Sort u} (x : α) (y : β) (H : @PSigma.mk _ id _ x = @PSigma.mk _ id _ y) : HEq x y :=
  match β, y, H with
  | .(α), .(x), Eq.refl _ => HEq.refl _

def HEq.ofSigmaEq' {α : Type u} (β : α → Type v) {xty yty : α} (x : β xty) (y : β yty)
  (H : @Sigma.mk _ β _ x = @Sigma.mk _ β _ y) : HEq x y :=
  match yty, y, H with
  | .(xty), .(x), Eq.refl _ => HEq.refl _

def HEq.ofPSigmaEq' {α : Sort u} (β : α → Sort v) {xty yty : α} (x : β xty) (y : β yty)
  (H : @PSigma.mk _ β _ x = @PSigma.mk _ β _ y) : HEq x y :=
  match yty, y, H with
  | .(xty), .(x), Eq.refl _ => HEq.refl _

def HEq.toSigmaEq {α β : Type u} (x : α) (y : β) (H : HEq x y) : @Sigma.mk _ id _ x = @Sigma.mk _ id _ y :=
  match β, y, H with
  | .(α), .(x), HEq.refl _ => Eq.refl _

def HEq.toPSigmaEq {α β : Sort u} (x : α) (y : β) (H : HEq x y) : @PSigma.mk _ id _ x = @PSigma.mk _ id _ y :=
  match β, y, H with
  | .(α), .(x), HEq.refl _ => Eq.refl _

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

def SigmaEq.rfl {α : Type u} (f : α → Type v) {x : α} {a : f x} : Sigma.mk x a = Sigma.mk x a :=
  Eq.refl _

def PSigmaEq.rfl {α : Sort u} (f : α → Sort v) {x : α} {a : f x} : PSigma.mk x a = PSigma.mk x a :=
  Eq.refl _

def SigmaEq.rec {α : Type u} {f : α → Type v} {x : α} {a : f x}
  (motive : {y : α} → (b : f y) → Sigma.mk x a = Sigma.mk y b → Sort u_1)
  (m : motive a (Eq.refl _)) {y : α} {b : f y} (h : Sigma.mk x a = Sigma.mk y b) : motive b h :=
  match y, b, h with
  | .(x), .(a), Eq.refl _ => m

def PSigmaEq.rec {α : Sort u} {f : α → Sort v} {x : α} {a : f x}
  (motive : {y : α} → (b : f y) → PSigma.mk x a = PSigma.mk y b → Sort u_1)
  (m : motive a (Eq.refl _)) {y : α} {b : f y} (h : PSigma.mk x a = PSigma.mk y b) : motive b h :=
  match y, b, h with
  | .(x), .(a), Eq.refl _ => m

def SigmaEq.ndrec {α : Type u} (f : α → Type v) (x : α) (a : f x)
  {motive : {x : α} → f x → Sort w} (m : motive a)
  {y : α} (b : f y) (h : Sigma.mk x a = Sigma.mk y b) : motive b :=
  match y, b, h with
  | .(x), .(a), Eq.refl _ => m

def PSigmaEq.ndrec {α : Sort u} (f : α → Sort v) (x : α) (a : f x)
  {motive : {x : α} → f x → Sort w} (m : motive a)
  {y : α} (b : f y) (h : PSigma.mk x a = PSigma.mk y b) : motive b :=
  match y, b, h with
  | .(x), .(a), Eq.refl _ => m

def SigmaEq.subst {α : Type u} (f : α → Type v) (x y : α) (a : f x) (b : f y)
  {p : (x : α) → f x → Prop} (h₁ : Sigma.mk x a = Sigma.mk y b) (h₂ : p x a) : p y b :=
  @SigmaEq.ndrec α f x a (fun {x : α} a => p x a) h₂ y b h₁

def PSigmaEq.subst {α : Sort u} (f : α → Sort v) (x y : α) (a : f x) (b : f y)
  {p : (x : α) → f x → Prop} (h₁ : PSigma.mk x a = PSigma.mk y b) (h₂ : p x a) : p y b :=
  @PSigmaEq.ndrec α f x a (fun {x : α} a => p x a) h₂ y b h₁

def SigmaEq.of_eq {α : Type u} (f : α → Type v)
  {x : α} {a a' : f x} (h : Eq a a') : Sigma.mk x a = Sigma.mk x a' :=
  Eq.mpr (h ▸ Eq.refl _) (@SigmaEq.rfl _ f x a')

def PSigmaEq.of_eq {α : Sort u} (f : α → Sort v)
  {x : α} {a a' : f x} (h : Eq a a') : PSigma.mk x a = PSigma.mk x a' :=
  Eq.mpr (h ▸ Eq.refl _) (@PSigmaEq.rfl _ f x a')

def SigmaEq.to_Eq {α : Type u} (f : α → Type v)
  {x : α} {a b : f x} (h : Sigma.mk x a = Sigma.mk x b) : a = b :=
  match b, h with
  | .(a), Eq.refl _ => Eq.refl _

def PSigmaEq.to_eq {α : Sort u} (f : α → Sort v)
  {x : α} {a b : f x} (h : PSigma.mk x a = PSigma.mk x b) : a = b :=
  match b, h with
  | .(a), Eq.refl _ => Eq.refl _

def SigmaEq.of_PSigmaEq {α : Type u} (f : α → Type v) {x : α} {a : f x} {y : α} {b : f y}
  (H : PSigma.mk x a = PSigma.mk y b) : Sigma.mk x a = Sigma.mk y b :=
  match y, b, H with
  | .(x), .(a), Eq.refl _ => Eq.refl _

def PSigmaEq.of_SigmaEq {α : Type u} (f : α → Type v) {x : α} {a : f x} {y : α} {b : f y}
  (H : Sigma.mk x a = Sigma.mk y b) : PSigma.mk x a = PSigma.mk y b :=
  match y, b, H with
  | .(x), .(a), Eq.refl _ => Eq.refl _

def SigmaEq.of_heq {α : Type u} (f : α → Type v)
  {x : α} {a : f x} {x' : α} {a' : f x'} (h : HEq a a') (h' : x = x') : Sigma.mk x a = Sigma.mk x' a' :=
  match x', h' with
  | .(x), Eq.refl _ =>
    match h with
    | HEq.refl _ => Eq.refl _

def PSigmaEq.of_heq {α : Sort u} (f : α → Sort v)
  {x : α} {a : f x} {x' : α} {a' : f x'} (h : HEq a a') (h' : x = x') : PSigma.mk x a = PSigma.mk x' a' :=
  match x', h' with
  | .(x), Eq.refl _ =>
    match h with
    | HEq.refl _ => Eq.refl _

abbrev PSigmaEq {α : Sort u} (f : α → Sort v) {x : α} (a : f x) {y : α} (b : f y) :=
  PSigma.mk x a = PSigma.mk y b

abbrev SigmaEq {α : Type u} (f : α → Type v) {x : α} (a : f x) {y : α} (b : f y) :=
  Sigma.mk x a = Sigma.mk y b

inductive DepEq {α : Sort u} (f : α → Sort v) : {x : α} → (a : f x) → {y : α} → (b : f y) → Prop where
  /-- Reflexivity of heterogeneous equality. -/
  | refl (x : α) (a : f x) : DepEq f a a

@[match_pattern] protected def DepEq.rfl {α : Sort u} (f : α → Sort v) {x : α} {a : f x} :=
  DepEq.refl x a

def DepEq.ofSigmaEq {α : Type u} (f : α → Type v) (x : α) (a : f x)
  (y : α) (b : f y) (H : Sigma.mk (β:=f) x a = Sigma.mk (β:=f) y b) : DepEq f a b :=
  by cases H; apply DepEq.refl

def DepEq.ofPSigmaEq {α : Sort u} (f : α → Sort v) (x : α) (a : f x)
  (y : α) (b : f y) (H : PSigma.mk (β:=f) x a = PSigma.mk (β:=f) y b) : DepEq f a b :=
  by cases H; apply DepEq.refl

def DepEq.toSigmaEq {α : Type u} (f : α → Type v) (x : α) (a : f x)
  (y : α) (b : f y) (H : DepEq f a b) : Sigma.mk (β:=f) x a = Sigma.mk (β:=f) y b :=
  by cases H; rfl

def DepEq.toPSigmaEq {α : Sort u} (f : α → Sort v) (x : α) (a : f x)
  (y : α) (b : f y) (H : DepEq f a b) : PSigma.mk (β:=f) x a = PSigma.mk (β:=f) y b :=
  by cases H; rfl

-- Example Usage of `SigmaEq`

set_option genInjectivity false in
inductive SigmaFn : Nat → Type 1
  | mk (α : Type) (fn : α → Nat) (arg : α) : SigmaFn (fn arg)

def SigmaFn.inj {α : Type} {fn : α → Nat} {arg : α} {fn_1 : α_1 → Nat} {arg_1 : α_1}
  (H : (⟨fn arg, SigmaFn.mk α fn arg⟩ : Sigma SigmaFn) = ⟨fn_1 arg_1, SigmaFn.mk α_1 fn_1 arg_1⟩) :
  α = α_1 ∧ (⟨α, arg⟩ : Sigma id) = ⟨α_1, arg_1⟩ ∧ (⟨α, fn⟩ : Sigma (fun α => α → Nat)) = ⟨α_1, fn_1⟩ :=
  let lh : Sigma SigmaFn := ⟨fn arg, SigmaFn.mk α fn arg⟩
  let rh : Sigma SigmaFn := ⟨fn_1 arg_1, SigmaFn.mk α_1 fn_1 arg_1⟩
  let lreq : lh = rh := H
  let rwFn₁ (x : Sigma SigmaFn) : Sigma id :=
    match x with
    | Sigma.mk fst snd =>
      match snd with
      | SigmaFn.mk α fn arg => ⟨α, arg⟩
  let rwRes₁ : rwFn₁ lh = rwFn₁ rh := by rw [lreq]
  let rwFn₂ (x : Sigma SigmaFn) : Sigma (fun (α : Type) => α → Nat) :=
    match x with
    | Sigma.mk fst snd =>
      match snd with
      | SigmaFn.mk α fn arg => ⟨α, fn⟩
  let rwRes₂ : rwFn₂ lh = rwFn₂ rh := by rw [lreq]
  And.intro (by cases rwRes₁; rfl) (And.intro rwRes₁ rwRes₂)