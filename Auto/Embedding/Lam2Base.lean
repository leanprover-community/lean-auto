import Auto.Embedding.Lift

namespace Auto.Embedding.Lam₂

/--
  0 = *
  1 = * -> *
  2 = * -> * -> *
  ...
-/
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
  case bvar n =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
  case func m₁ n₁ ihm₁ ihn₁ =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
    intro h₁ h₂;
    apply And.intro
    case left => apply ihm₁; simp [h₁]
    case right => apply ihn₁; simp [h₂]
  case app m₁ n₁ ihm₁ ihn₁ =>
    intro b;
    cases b <;> simp [Lam₂Type.beq]
    intro h₁ h₂
    apply And.intro
    case left => apply ihm₁; simp [h₁]
    case right => apply ihn₁; simp [h₂]

theorem Lam₂Type.beq_eq_true_eq (a b : Lam₂Type) : (a.beq b = true) = (a = b) :=
  propext <| Iff.intro (beq_eq a b) (fun h => by subst h; apply beq_refl)

/--
  `tcVal`: Valuation of type constructors
  `ltyLCtx` : Number of type variables in the local context
  Returns:
    1. Number of type arguments the type takes, if the type is well-formed
    2. None, otherwise
-/
def Lam₂Type.check (tcVal : Nat → Lam₂Sort) (ltyLCtx : Nat) : Lam₂Type → Option Nat
| .atom n => .some (tcVal n)
| .bvar n => if n < ltyLCtx then .some 0 else .none
| .func dom cod =>
  match dom.check tcVal ltyLCtx, cod.check tcVal ltyLCtx with
  | .some 0, .some 0 => .some 0
  | _, _ => .none
| .app fn arg =>
  match fn.check tcVal ltyLCtx, arg.check tcVal ltyLCtx with
  | .some (n + 1), .some 0 => .some n
  | _, _ => .none

/-- Sort Judgement `val, typelctx ⊢ type : Sort` -/
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

def Lam₂Type.check_iff_interp
  (val : Nat → ((n : Lam₂Sort) × Lam₂Sort.interp n)) (lctx : List (Sort u))
  (lty : Lam₂Type) :
  let tcVal := fun n => (val n).1
  let ltyLCtx := lctx.length
  lty.check tcVal ltyLCtx = (lty.interp val lctx).map (fun x => x.1) := by
  induction lty
  case atom n =>
    simp [check, interp, Option.map]
  case bvar n =>
    simp [check, interp]
    cases Nat.decLt n (List.length lctx)
    case isTrue h =>
      simp [h]; simp [List.get?_eq_get h]
    case isFalse h =>
      simp [h]; simp at h; simp [List.get?_len_le h]
  case func fn arg IHfn IHarg =>
    revert IHfn IHarg
    simp [check, interp]
    match
      cfn : check (fun n => (val n).fst) (List.length lctx) fn,
      carg : check (fun n => (val n).fst) (List.length lctx) arg with
    | .some 0, .some 0 =>
      simp;
      match cifn : interp val lctx fn, ciarg : interp val lctx arg with
      | .some ⟨0, _⟩, .some ⟨0, _⟩ => simp
      | .some ⟨0, _⟩, .some ⟨n + 1, _⟩ => simp; simp_arith
      | .some ⟨0, _⟩, .none => simp
      | .some ⟨n + 1, _⟩, _ => simp; simp_arith
      | .none , _ => simp
    | .some 0, .some (n + 1) =>
      simp;
      match cifn : interp val lctx fn, ciarg : interp val lctx arg with
      | .some ⟨0, _⟩, .some ⟨0, _⟩ => simp
      | .some ⟨0, _⟩, .some ⟨n + 1, _⟩ => simp
      | .some ⟨0, _⟩, .none => simp
      | .some ⟨n + 1, _⟩, _ => simp
      | .none , _ => simp
    | .some 0, .none =>
      simp; cases interp val lctx arg <;> simp
    | .some (n + 1), _ =>
      simp;
      match cifn : interp val lctx fn, ciarg : interp val lctx arg with
      | .some ⟨0, _⟩, .some ⟨0, _⟩ => simp
      | .some ⟨0, _⟩, .some ⟨n + 1, _⟩ => simp
      | .some ⟨0, _⟩, .none => simp
      | .some ⟨n + 1, _⟩, _ => simp
      | .none , _ => simp
    | .none, _ =>
      simp; cases interp val lctx fn <;> simp
  case app fn arg IHfn IHarg =>
    revert IHfn IHarg
    simp [check, interp]
    match
      cfn : check (fun n => (val n).fst) (List.length lctx) fn,
      carg : check (fun n => (val n).fst) (List.length lctx) arg with
    | .some (n + 1), .some 0 =>
      simp;
      match cifn : interp val lctx fn, ciarg : interp val lctx arg with
      | .some ⟨n + 1, _⟩, .some ⟨0, _⟩ => simp
      | .some ⟨n + 1, _⟩, .some ⟨m + 1, _⟩ => simp; simp_arith
      | .some ⟨n + 1, _⟩, .none => simp
      | .some ⟨0, _⟩, _ => simp
      | .none , _ => simp
    | .some (n + 1), .some (m + 1) =>
      simp;
      match cifn : interp val lctx fn, ciarg : interp val lctx arg with
      | .some ⟨n + 1, _⟩, .some ⟨0, _⟩ => simp
      | .some ⟨n + 1, _⟩, .some ⟨m + 1, _⟩ => simp
      | .some ⟨n + 1, _⟩, .none => simp
      | .some ⟨0, _⟩, _ => simp
      | .none , _ => simp
    | .some (n + 1), none =>
      simp; cases interp val lctx arg <;> simp
    | .some 0, _ =>
      simp;
      match cifn : interp val lctx fn with
      | .some ⟨n + 1, _⟩ => simp; simp_arith
      | .some ⟨0, _⟩ => simp
      | .none => simp
    | .none, _ =>
      simp; cases interp val lctx fn <;> simp

end Auto.Embedding.Lam₂
