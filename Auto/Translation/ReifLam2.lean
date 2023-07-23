import Auto.Translation.Lift

namespace Auto.ReifLam₂

-- 0 = *
-- 1 = * -> *
-- 2 = * -> * -> *
-- ...
abbrev Lam₂Sort := Nat

def Lam₂Sort.interp.{u} : Lam₂Sort → Type u
| 0 => Sort u
| n + 1 => Sort u → Lam₂Sort.interp n

inductive Lam₂Type
| atom    : Nat → Lam₂Type
-- The n-th element in the type local context
| bvar    : (n : Nat) → Lam₂Type
-- α → β
| func    : (α β : Lam₂Type) → Lam₂Type
-- α β, e.g (List Nat)
-- α is a type constructor, or a partial application of a type constructor
| app     : (α β : Lam₂Type) → Lam₂Type
deriving Inhabited, Hashable
-- Example: `HashMap α (Nat → Nat)`
--   `Nat` will be an `atom`
--   `α` will be a `bvar`
--   `Nat → Nat` will be a `func`
--   `HashMap α` will be an `app`
-- Since we are in `λ₂`, only types of sort `0` can be type argument

def Lam₂Type.beq : Lam₂Type → Lam₂Type → Bool
| .atom m,        .atom n        => m == n
| .bvar m,        .bvar n        => m == n
| .func m₁ n₁,    .func m₂ n₂    => m₁.beq m₂ && n₁.beq n₂
| .app m₁ n₁,     .app m₂ n₂     => m₁.beq m₂ && n₁.beq n₂
| _,              _              => false

theorem Lam₂Type.beq_refl (a : Lam₂Type) : (a.beq a) = true := by
  induction a
  case atom n => simp [beq]
  case bvar n => simp [beq]
  case func t1 t2 => simp [beq]; simp [t1, t2]
  case app t1 t2 => simp [beq]; simp [t1, t2]

theorem Lam₂Type.beq_eq (a b : Lam₂Type) : (a.beq b = true) → a = b := by
  revert b; induction a
  case atom m =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
    case atom n => apply id
  case bvar n =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
    case bvar m => apply id
  case func m₁ n₁ ihm₁ ihn₁ =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
    intro h; cases h;
    case func.intro h₁ h₂ =>
      apply And.intro
      case left => apply ihm₁; simp [h₁]
      case right => apply ihn₁; simp [h₂]
  case app m₁ n₁ ihm₁ ihn₁ =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
    intro h; cases h;
    case app.intro h₁ h₂ =>
      apply And.intro
      case left => apply ihm₁; simp [h₁]
      case right => apply ihn₁; simp [h₂]

theorem Lam₂Type.beq_eq_true_eq (a b : Lam₂Type) : (a.beq b = true) = (a = b) :=
  propext <| Iff.intro (beq_eq a b) (fun h => by subst h; apply beq_refl)

-- `tcVal`: Valuation of type constructors
-- `lctx` : Number of type variables in the local context
-- Returns:
--   1. Number of type arguments the type takes, if the type is well-formed
--   2. None, otherwise
def Lam₂Type.check (tcVal : Nat → Lam₂Sort) (lctx : Nat) : Lam₂Type → Option Nat
| .atom n => .some (tcVal n)
| .bvar n => if n < lctx then .some 0 else .none
| .func dom cod =>
  match dom.check tcVal lctx, cod.check tcVal lctx with
  | .some 0, .some 0 => .some 0
  | _, _ => .none
| .app fn arg =>
  match fn.check tcVal lctx, arg.check tcVal lctx with
  | .some (n + 1), .some 0 => .some n
  | _, _ => .none

-- Sort Judgement
--   `val, typelctx ⊢ type : Sort`
@[reducible] def Lam₂Type.interp.{u}
  (val : Nat → ((n : Lam₂Sort) × Lam₂Sort.interp n)) (lctx : List (Sort u)) :
  Lam₂Type → Option ((n : Lam₂Sort) × Lam₂Sort.interp n)
| .atom n => .some (val n)
| .bvar n =>
  match lctx.get? n with
  | .some s => .some ⟨0, s⟩
  | .none   => .none
| .func dom cod =>
  match dom.interp val lctx, cod.interp val lctx with
  | .some ⟨0, domi⟩, .some ⟨0, codi⟩ => .some ⟨0, domi → codi⟩
  | _,            _                 => .none
| .app fn arg =>
  match fn.interp val lctx, arg.interp val lctx with
  | .some ⟨n + 1, fni⟩, .some ⟨0, argi⟩ => .some ⟨n, fni argi⟩
  | _,                 _               => none

end Auto.ReifLam₂