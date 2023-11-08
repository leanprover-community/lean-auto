inductive Foo : Nat → Bool → Type
  | ctor (f : Nat → Nat) (n : Nat) : Foo (f n) false

def match_Foo (h : Foo 2 true) : False := by
  cases h -- Fails

inductive Bar : Bool → Nat → Type
  | ctor (f : Nat → Nat) (n : Nat) : Bar false (f n)

def match_Bar (h : Bar true 2) : False := by
  cases h

-- Context where this becomes a problem
inductive Ctx : Bool → Nat → Type
  | ctor1 (f : Nat → Nat) (n : Nat) : Ctx false (f n)
  | ctor2 (f : Bool → Bool) (n : Bool) : Ctx (f n) 0

def match_Ctx (h : Ctx true 2) : False := by
  cases h -- Fails

def match_Ctx_generalize (h : Ctx true 2) : False := by
  revert h; generalize h₁ : 2 = a; generalize h₂ : true = b
  intro h; cases h
  case ctor1 => cases h₂
  case ctor2 => cases h₁

-- Workaround (Jannis Limperg)
inductive Flat : Nat → Bool → Type
  | ctor (f : Nat → Nat) (n : Nat) (x : Nat) (h : x = f n) : Flat x false

def match_Flat (h : Flat 2 true) : False := by
  cases h

inductive Ctx' : Bool → Nat → Type
  | ctor1 (f : Nat → Nat) (n : Nat) (h : x = f n) : Ctx' false x
  | ctor2 (f : Bool → Bool) (n : Bool) (h : f n = x) : Ctx' x 0

def match_Ctx' (h : Ctx' true 2) : False := by
  cases h

-- Issue with Jannis Limperg's workaround
opaque sinterp : Nat → Bool → Type
instance : Inhabited (sinterp n b) := sorry
opaque tinterp (f : Nat → Nat) (n : Nat) (b : Bool) : sinterp (f n) b
opaque fn1 {n b} : sinterp n b → Nat

def funFoo : Foo x b → sinterp x b
| .ctor f n => tinterp f n false

def funFlat : Flat x b → sinterp x b
| .ctor f n x h => h ▸ tinterp f n false

-- Minimized example
theorem funFoo_fact1 (i : Foo x b) : ∃ f n, HEq (funFoo i) (tinterp f n b) := by
  cases i
  case ctor f n =>
    exists f, n; apply HEq.refl

theorem funFlat_fact1 (i : Flat x b) : ∃ f n, HEq (funFlat i) (tinterp f n b) := by
  cases i
  case ctor f n h =>
    exists f, n; dsimp [funFlat]; cases h; apply HEq.refl
