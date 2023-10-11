import Lean
import Auto.DUnif.DRefl

opaque wwww : Nat → Nat → Nat → Nat := fun _ _ _ => 1
opaque www : Nat → Nat → Nat := fun _ _ => 1
opaque ww : Nat → Nat := id
opaque w : Nat

set_option auto.dunif.dbgOn true

-- Trivial
set_option trace.auto.dunif.debug true in
def tri₁ : 1 = 1 := by drefl attempt 3 unifier 0 contains 0

def tri₂ (done : Prop)
         (gene : ∀ r (b : Nat → Nat), r = b r → done) : done := by
  apply gene;
  case a => drefl attempt 500 unifier 0 contains 0 iteron; exact 1
#print tri₂.proof_1

@[reducible] def fooNat := Nat

set_option trace.auto.dunif.debug true in
def tri₃ : (Nat → Nat → Nat → Nat → Nat) = (Nat → Nat → Nat → fooNat → Nat) := by
  drefl attempt 11 unifier 0 contains 0

-- Iteration
set_option trace.auto.dunif.debug true in
set_option auto.dunif.oracleInstOn false in
def iter₁ (done : Prop)
          (gene : ∀ (H : (Nat → Nat) → Nat → Nat) F X, H F X = F X → done) :
          done := by
  apply gene
  case a => drefl attempt 1500 unifier 0 contains 0 iteron
            case X => exact w

set_option trace.auto.dunif.debug true in
def iter₂ (done : Prop) (a : Nat)
          (gene : ∀ (F G : Nat → Nat), F a = G a → done) :
          done := by
  apply gene
  case a => drefl attempt 50 unifier 3 contains 0 iteron;

#print iter₂.proof_1


set_option auto.dunif.dbgOn true

-- ChurchNumeral
namespace ChNum

@[reducible] def ChNat := Nat → (Nat → Nat) → Nat
@[reducible] def chadd (n m : ChNat) x f := n (m x f) f
@[reducible] def chmul (n m : ChNat) x f := n x (fun z => m z f)
@[reducible] def idtest (n : ChNat) := fun z => n z (fun y => y)

@[reducible] def c0 : ChNat := fun x _ => x
@[reducible] def c1 : ChNat := fun x f => f x
@[reducible] def c2 : ChNat := fun x f => f (f x)
@[reducible] def c3 : ChNat := fun x f => f (f (f x))
@[reducible] def c7 : ChNat := fun x f => f (f (f (f (f (f (f x))))))

def pellEquation₁ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → Nat)
                  -- ?m = 2, ?n = 1
                  (h : ∀ (m n : ChNat), 
                  q (chmul (chadd n c2) (chadd n c2)) (idtest m)   (idtest n) = 
                  q (chadd (chmul (chmul c2 m) m) c1) (fun z => z) (fun z => z)  → done)
                  : done := by
  apply h;
  case a => drefl attempt 160 unifier 0 contains 0

#print pellEquation₁.proof_1

def pellEquation₂ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → Nat)
                  -- ?m = 3, ?n = 6
                  (h : ∀ (m n : ChNat), 
                  q (chmul (chadd n c2) (chadd n c2)) (idtest m)   (idtest n) = 
                  q (chadd (chmul (chmul c7 m) m) c1) (fun z => z) (fun z => z)→ done)
                  : done := by
  apply h;
  case a => drefl attempt 18000 unifier 0 contains 0

#print pellEquation₂.proof_1

def pythagoreanTriple₁ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Nat)
                       (h : ∀ (x y z : ChNat),
                       -- 3² + 4² = 5²
                       q (chadd (chmul (chadd x c1) (chadd x c1))  (chmul (chadd y c1) (chadd y c1)))  (idtest x)   (idtest y)   (idtest z) = 
                       q (chmul (chadd z c2) (chadd z c2)) (fun z => z) (fun z => z) (fun z => z) → done):
                       done := by
  apply h;
  case a => drefl attempt 6000 unifier 0 contains 0

#print pythagoreanTriple₁.proof_1

end ChNum


-- Dependent Type
namespace Dependent

def dep₁ (done : Prop)
         (h : ∀ x, x = (1, 2).1 → done) : done := by
  apply h
  case a => drefl attempt 54 unifier 0 contains 0

@[reducible] noncomputable def Nat.add1 := fun (x x_1 : Nat) =>
  @Nat.brecOn.{1} (fun (x : Nat) => Nat → Nat) x_1
    (fun (x : Nat) (f : @Nat.below.{1} (fun (x : Nat) => Nat → Nat) x) (x_2 : Nat) =>
      (fun (motive : Nat → Nat → Type) (a x : Nat) (h_1 : (a : Nat) → motive a Nat.zero)
    (h_2 : (a b : Nat) → motive a (Nat.succ b)) =>
  @Nat.casesOn.{1} (fun (x : Nat) => motive a x) x (h_1 a) fun (n : Nat) => h_2 a n) (fun (a x : Nat) => @Nat.below.{1} (fun (x : Nat) => Nat → Nat) x → Nat) x_2
        x (fun (a : Nat) (x : @Nat.below.{1} (fun (x : Nat) => Nat → Nat) Nat.zero) => a)
        (fun (a b : Nat) (x : @Nat.below.{1} (fun (x : Nat) => Nat → Nat) (Nat.succ b)) =>
          Nat.succ
            (@PProd.fst.{1, 1} ((fun (x : Nat) => Nat → Nat) b)
              (@Nat.rec.{2} (fun (t : Nat) => Type) PUnit.{1}
                (fun (n : Nat) (n_ih : Type) =>
                  PProd.{1, 1} (PProd.{1, 1} ((fun (x : Nat) => Nat → Nat) n) n_ih) PUnit.{1})
                b)
              (@PProd.fst.{1, 1}
                (PProd.{1, 1} ((fun (x : Nat) => Nat → Nat) b)
                  (@Nat.rec.{2} (fun (t : Nat) => Type) PUnit.{1}
                    (fun (n : Nat) (n_ih : Type) =>
                      PProd.{1, 1} (PProd.{1, 1} ((fun (x : Nat) => Nat → Nat) n) n_ih) PUnit.{1})
                    b))
                PUnit.{1} x)
              a))
        f)
    x

set_option maxHeartbeats 400000 in
set_option auto.dunif.oracleInstOn false in
set_option auto.dunif.dbgOn false in
def dep₂ (done : Prop)
         (h : ∀ x, x = Nat.add1 → done) : done := by
  apply h
  case a => drefl attempt 130000 unifier 0 contains 0

#print dep₂.proof_1

-- This tests DUnif's ability to avoid assigning `e` to mvar `m` when
--   some mvars in `e` depends on `m`. This mostly concerns the binding
--   `oracleInst` and `identification`.
set_option trace.auto.dunif.debug true in
set_option trace.Meta.Tactic true in
def dep₃ (done : Prop) (inh : Sort u)
         (h : ∀ (r : Type u) (a_1 : r → Prop) (a_2 : r), a_1 a_2 = Nonempty r → done) : done := by
  apply h
  case a => drefl attempt 21 unifier 0 contains 0; exact (Sort u);
  case a_2 => exact inh

end Dependent


-- let binders

@[reducible] def letdef₁ := let x := 2; x + x

def letrefl₁  (done : Prop)
              (lr : ∀ u, u = letdef₁ → done)
              : done := by
  apply lr
  drefl attempt 60 unifier 0 contains 0


-- OracleInst

def ora₁ (done : Prop) (inh : α → β → Nat)
  (h : ∀ (a b : α → β → Nat), (fun x y => a y x) = (fun x y => b y x) → done) : done := by
  apply h
  drefl attempt 3 unifier 0 contains 0
  exact inh

def ora₂ (done : Prop) (inh : ∀ (α β : Type) (x : α) (y : β), α → β)
  (h : ∀ (a b : ∀ (α β : Type) (x : α) (y : β), α → β),
    (fun β y α x => a α β x y) = (fun β y α x => b α β x y) → done) : done := by
  apply h
  drefl attempt 3 unifier 0 contains 0
  exact inh

def ora₃ (done : Prop) (inh : ∀ (α β : Type) (x : α) (y : β), α → β)
  (h : ∀ (a b : ∀ (α β : Type) (x : α) (y : β), α → β),
    (fun β α y x => a α β x y) = (fun β α y x => b α β x y) → done) : done := by
  apply h
  drefl attempt 3 unifier 0 contains 0
  exact inh


-- Polymorphism

def poly₁ (done : Prop) (f : ∀ (α : Type), α)
  (h : ∀ β, @Sigma.mk _ id (Nat → Nat) (f (Nat → Nat)) = ⟨β, f β⟩ → done) : done := by
  apply h
  drefl attempt 20 unifier 0 contains 0

def poly₂ (done : Prop) (f : ∀ (α : Type), α)
  (h : ∀ (g : ∀ (α : Type), α), g (Nat → Nat) 2 = f (Nat → Nat) 2 → done) : done := by
  apply h
  drefl attempt 20 unifier 0 contains 0

def poly₃
  (done : Prop)
  (skS : ∀ {_ : Nat} {α : Type}, α)
  (α β : Type) (p : α → β → Prop) (f : α → β) (x : α)
  (h : ∀ a b c d, p a (@skS (nat_lit 1) (α → β → β) a b) = p (@skS (nat_lit 0) ((α → β) → α → α) c d) (c (@skS (nat_lit 0) ((α → β) → α → α) c d)) → done) :
  done := by
  apply h
  drefl attempt 30 unifier 0 contains 0
  exact f; exact x

def poly₄
  (done : Prop)
  (skS : ∀ {_ : Nat} {α : Type}, α)
  (α β : Type) (p : α → β → Prop) (f : α → β) (x : α)
  (h : ∀ a b c d e, p a (@skS (nat_lit 1) (α → β → β → β) a b e) = p (@skS (nat_lit 0) ((α → β) → α → α) c d) (c (@skS (nat_lit 0) ((α → β) → α → α) c d)) → done) :
  done := by
  apply h
  drefl attempt 37 unifier 0 contains 0
  exact f; exact f; exact x

-- Eta expansion test
def Set α := α → Prop

def eta₁ (done : Prop) (inh : Nat → Prop)
         (h : ∀ (f g : Set Nat), f = g → done) : done := by
  apply h
  drefl attempt 10 unifier 0 contains 0
  exact inh

def eta₂ (done : Prop) (inh : Nat → Prop)
         (h : ∀ (f g : Set Nat), (fun x => f x) = (fun x => g x) → done) : done := by
  apply h
  drefl attempt 10 unifier 0 contains 0
  exact inh

-- Negative tests
set_option trace.auto.dunif.debug true in
def neg₁ (done : Prop) (f : Nat → Nat)
         (h : ∀ x, x = f x → done) : done := by
  apply h
  case a => drefl attempt 10 unifier 0 contains 0

set_option trace.auto.dunif.debug true in
def neg₂ (done : Prop) (f : Nat → Nat) (g : Nat → Nat →  Nat)
         (h : ∀ x y, g x y = g y (f x) → done) : done := by
  apply h
  case a => drefl attempt 10 unifier 0 contains 0

set_option trace.auto.dunif.debug true in
def neg₃ : (Nat → Bool → Nat → Bool → Nat) = (Bool → Nat → Bool → Nat → Bool) := by
  drefl attempt 11 unifier 0 contains 0

set_option trace.auto.dunif.debug true in
def neg₄ : (Nat → Type 2 → Type 1) = (Nat → Bool → Type 2) := by
  drefl attempt 11 unifier 0 contains 0

-- Not very clear whether we need to succeed
def unclear₁ (done : Prop)
         (h : ∀ (f g : Set Nat), (fun x => f x) = g → done) : done := by
  apply h
  drefl attempt 10 unifier 0 contains 0