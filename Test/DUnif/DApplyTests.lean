import Lean
import Auto.DUnif.DApply

-- whnf test
def wh₁ : Nat := 3

set_option auto.dunif.dbgOn true

set_option trace.Meta.Tactic true in
def wh₀ (f : Nat → Prop) (h : ∀ x, f x) : f wh₁ :=
  by dapply h attempt 5 unifier 0 contains 0

-- Imitation
set_option trace.auto.dunif.debug true in
def imt₀ (f : Nat → Prop) (h : ∀ x, f x) : f 3 :=
  by dapply h attempt 30 unifier 0 contains 0

def imt₁ (f : Nat → Prop)
         (h : ∀ x y (z : Nat), f z → f (x + y))
         (k : f 0) : f (3 + b) := by
  dapply h attempt 30 unifier 0 contains 0
  case a => dapply h attempt 70 unifier 0 contains 0;
            case a => apply k;
            exact 0; exact 0

def imt₂ (f : Nat → Prop)
          (comm : ∀ x y, f (x + y) → f (y + x))
          (h : ∀ x y z, f (x + z) → f (x + y))
          (g : f (u + v))
          : f (a + b) := by
  dapply h attempt 30 unifier 0 contains 0
  case a =>
    dapply comm attempt 42 unifier 0 contains 0;
    case a => dapply h attempt 42 unifier 0 contains 0;
              case a => dapply g attempt 42 unifier 0 contains 0

-- Huet-Style Projection
def hsp₁ (ftr : ∀ (f g : Nat → Prop) (x : Nat), f x → g x)
          (S T : Nat → Prop) (u v : Nat)
          (h   : S u) : T v := by
  dapply ftr attempt 100 unifier 1 contains 0
  case a => dapply h attempt 10 unifier 0 contains 0

def hsp₂ (p : Nat → Prop) (x y : Nat)
        (hp : ∀ (f : Nat → Nat → Nat), p (f x y) ∧ p (f y x))
        : p x ∧ p y := by
  dapply hp attempt 11 unifier 0 contains 0

def hsp₃ (p : Nat → Prop) (x y : Nat)
        (hp : ∀ (f : Nat → Nat → Nat), p (f x y) ∧ p (f y x))
        : p (x + y) ∧ p (y + x) := by
  dapply hp attempt 300 unifier 0 contains 0

def hsp₄ (done : Prop)
         (gene : ∀ (H : (Nat → Nat) → Nat → Nat), (fun F X => H F X) = (fun F X => F X) → done) :
         done := by
  dapply gene attempt 10 unifier 0 contains 0
  case a => dapply Eq.refl attempt 70 unifier 0 contains 0;

opaque www : Nat → Nat → Nat := fun _ _ => 1
opaque ww : Nat → Nat := id
opaque w : Nat

-- Elimination
def elm₁ (p : Nat → Prop) 
         (a b : Nat) (h : ∀ (f : Nat → Nat → Nat), p (f a b))
         (g : ∀ (ay : Nat), p ay → False)
         : False := by
  dapply g attempt 10 unifier 0 contains 0
  case a => dapply h attempt 590 unifier 0 contains 0; exact www

#print elm₁.proof_1

-- Identification
def idt₁ (p : Nat → Prop) (x : Nat)
         (hp : ∀ (f g : Nat → Nat), p (f (g x)) ∧ p (g (f x)))
         (done : Prop)
         (hq : ∀ w, p w ∧ p w → done) : done := by
  dapply hq attempt 10 unifier 0 contains 0
  case a => dapply hp attempt 10000 unifier 66 contains 0
            exact id; exact (fun _ => (Nat → Nat)); exact (fun _ b _ => b id)

#print idt₁.proof_1

-- Negative tests
def neg₁ (h : True) : False :=
  by dapply h attempt 10 unifier 0 contains 0