import Auto.Translation.Lift
import Std.Data.List.Lemmas

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.ReifLam

inductive LamSort
| atom : Nat → LamSort
| func : LamSort → LamSort → LamSort
deriving Inhabited, Hashable

def LamSort.beq : LamSort → LamSort → Bool
| .atom m,     .atom n     => m == n
| .func m₁ n₁, .func m₂ n₂ => LamSort.beq m₁ m₂ && LamSort.beq n₁ n₂
| _,           _           => false

theorem LamSort.beq_refl (a : LamSort) : (a.beq a) = true := by
  induction a
  case atom n => simp [beq]
  case func s1 s2 => simp [beq]; simp [s1, s2]

theorem LamSort.beq_eq (a b : LamSort) : (a.beq b = true) → a = b := by
  revert b; induction a
  case atom m =>
    intro b; cases b
    case atom n =>
      intro HEq; simp [beq] at HEq; simp [HEq]
    case func => simp [beq]
  case func m₁ n₁ ihm₁ ihn₁ =>
    intro b; cases b
    case atom => simp [beq]
    case func m₂ n₂ =>
      simp [beq]; intro hm hn;
      apply And.intro
      case left => apply ihm₁; apply hm
      case right => apply ihn₁; apply hn

theorem LamSort.beq_eq_true_eq (a b : LamSort) : (a.beq b = true) = (a = b) :=
  propext <| Iff.intro (beq_eq a b) (fun h => by subst h; apply beq_refl)

@[reducible] def LamSort.interp.{u} (val : Nat → Sort u) : LamSort → Sort u
| .atom n => val n
| .func dom cod => interp val dom → interp val cod

inductive LamTerm
| atom    : Nat → LamTerm
| bvar    : Nat → LamTerm
| lam     : LamSort → LamTerm → LamTerm
| app     : LamTerm → LamTerm → LamTerm
deriving Inhabited, Hashable

-- Typecheck. `val, lctx ⊢ term : type?`
-- `val : Nat → LamSort` : Valuation
-- `List LamSort`        : Local Context
def LamTerm.check (val : Nat → LamSort) : List LamSort → LamTerm → Option LamSort
| _,    .atom n  => val n
| lctx, .bvar n  => lctx.get? n
| lctx, .lam s t =>
  match t.check val (s :: lctx) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app fn arg =>
  match fn.check val lctx, arg.check val lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    if ty₁.beq argTy then .some ty₂ else none
  | _, _ => .none

-- Judgement. `val, lctx ⊢ term : type?`
structure LamJudge where
  lctx   : List LamSort
  rterm  : LamTerm
  rTy    : LamSort
deriving Inhabited, Hashable

inductive LamWF (val : Nat → LamSort) : LamJudge → Prop
  | ofAtom
      {lctx : List LamSort} (n : Nat) :
    LamWF val ⟨lctx, .atom n, val n⟩
  | ofBVar
      {lctx : List LamSort} (n : Fin lctx.length) :
    LamWF val ⟨lctx, .bvar n, lctx[n]⟩
  | ofLam
      {lctx : List LamSort}
      {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
      (H : LamWF val ⟨argTy :: lctx, body, bodyTy⟩) :
    LamWF val ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
  | ofApp
      {lctx : List LamSort}
      (argTy : LamSort) {resTy : LamSort}
      {fn : LamTerm} {arg : LamTerm}
      (HFn : LamWF val ⟨lctx, fn, .func argTy resTy⟩)
      (HArg : LamWF val ⟨lctx, arg, argTy⟩) :
    LamWF val ⟨lctx, .app fn arg, resTy⟩

theorem LamTerm.check_if_wf
  (val : Nat → LamSort) (lctx : List LamSort) (t : LamTerm) (ty : LamSort) :
  LamWF val ⟨lctx, t, ty⟩ → t.check val lctx = .some ty := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rTy := ty : LamJudge} = Judge 
  intro HWf; revert lctx t ty JudgeEq; induction HWf
  case ofAtom lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq]; rfl
  case ofBVar lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]; apply List.get?_eq_get
  case ofLam lctx' argTy bodyTy body H H_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq];
    simp [check]; rw [H_ih]; rfl
  case ofApp lctx' argTy resTy fn arg HFn HArg HFn_ih HArg_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]
    simp [check];
    rw [HFn_ih lctx' fn (LamSort.func argTy resTy)] <;> try rfl;
    rw [HArg_ih lctx' arg argTy] <;> try rfl;
    simp [LamSort.beq_refl]

theorem LamTerm.wf_if_check
  (val : Nat → LamSort) (lctx : List LamSort) (t : LamTerm) (ty : LamSort) :
  t.check val lctx = .some ty → LamWF val ⟨lctx, t, ty⟩ := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rTy := ty : LamJudge} = Judge
  intros HWf; revert lctx ty Judge JudgeEq; induction t
  case atom a =>
    intros lctx ty Judge JudgeEq HCheck; rw [← JudgeEq]
    simp [check] at HCheck; rw [← HCheck]; apply LamWF.ofAtom
  case bvar n =>
    intros lctx ty Judge JudgeEq HCheck; rw [← JudgeEq]
    simp [check] at HCheck; rw [List.get?_eq_some] at HCheck
    cases HCheck;
    case intro hLt hEq =>
      rw [← hEq]; apply LamWF.ofBVar (n := ⟨n, hLt⟩)
  case lam argTy body IH =>
    intros lctx ty Judge JudgeEq; rw [← JudgeEq];
    simp [check];
    generalize CheckEq : check val (argTy :: lctx) body = cRes
    cases cRes;
    case none =>
      intro HWf; simp at HWf;
    case some bodyTy =>
      simp; intro tyEq; rw [← tyEq]
      apply LamWF.ofLam; apply IH _ _ _ _ CheckEq; rfl
  case app fn arg IHFn IHarg =>
    intros lctx ty Judge JudgeEq; rw [← JudgeEq];
    simp [check]
    generalize CheckFnEq : check val lctx fn = cFnRes
    generalize CheckArgEq : check val lctx arg = cArgRes
    cases cFnRes <;> try (intro HWf; simp at HWf)
    case some fnTy =>
      cases cArgRes
      case none => cases fnTy <;> simp at HWf
      case some argTy =>
      cases fnTy <;> simp at HWf
      case func argTy' resTy' =>
        cases tyEq : LamSort.beq argTy' argTy
        case false =>
          simp [tyEq] at HWf
        case true =>
          simp [tyEq] at HWf; rw [← HWf];
          rw [LamSort.beq_eq_true_eq] at tyEq; rw [tyEq] at CheckFnEq;
          apply LamWF.ofApp argTy
          case HFn => apply IHFn _ _ _ _ CheckFnEq; rfl
          case HArg => apply IHarg _ _ _ _ CheckArgEq; rfl
     
-- Valuation
structure Lam2DVal.{u} where
  tyVal    : Nat → Type (u + 1)
  constVal : Nat → (α : Type (u + 1)) × α

/-
  It seems that we cannot write an interpretation function
    `interp : Lam2DVal → List ((α : Type (u + 1)) × α) → LamTerm → (α : Type (u + 1)) × α`
  The main problem is that we cannot manipulate types like inductive types,
    so we will not be able to compare the types of the two arguments of
    `LamTerm.eq lhs rhs`, and will not be able to test that the
    argument type of `f` matches the type of `arg` in `LamTerm.app f arg`

  So, we instead inductively define a well-formedness predicate.
-/

-- Judgement, `lctx ⊢ rterm ≝ mterm : ty`
structure Lam2DJudge.{u} where
  -- Local context, list of CIC terms
  lctx    : List ((α : Type (u + 1)) × α)
  -- A term in simply typed lambda calculus
  rterm   : LamTerm
  -- Type of `mterm`
  ty      : Type (u + 1)
  -- The CIC term that `rterm` translates into
  mterm   : ty

inductive WF.{u} (val : Lam2DVal.{u}) : Lam2DJudge.{u} → Prop
  | ofAtom
      {lctx : List ((γ : Type (u + 1)) × γ)}
      (n : Nat) :
    WF val <|
      let ci := val.constVal n
      ⟨lctx, (.atom n), ci.fst, ci.snd⟩
  | ofBVar
      {lctx : List ((α : Type (u + 1)) × α)}
      (n : Fin lctx.length) :
    WF val <|
      ⟨lctx, .bvar n, lctx[n].fst, lctx[n].snd⟩
  | ofLam
      {lctx : List ((γ : Type (u + 1)) × γ)}
      {hs : LamSort} {ht : LamTerm}
      (α β : Type (u + 1)) (fn : α → β)
      (H : ∀ (t : α), WF val ⟨⟨α, t⟩ :: lctx, ht, β, fn t⟩)
      :
    WF val <|
      ⟨lctx, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctx : List ((γ : Type (u + 1)) × γ)}
      {hfn harg : LamTerm}
      (α β : Type (u + 1)) (fn : α → β) (arg : α)
      (Hfn : WF val ⟨lctx, hfn, α → β, fn⟩)
      (Harg : WF val ⟨lctx, harg, α, arg⟩)
      :
    WF val <|
      ⟨lctx, .app hfn harg, β, fn arg⟩

section Example
  
  def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  def interpEx₁.{u} : Lam2DJudge.{u} :=
    ⟨[], .lam (.atom 0) (.app (.atom 0) (.bvar 0)),
     GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  def valuation₁.{u} : Lam2DVal.{u} :=
    ⟨fun _ => GLift Nat,
     fun _ => ⟨GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat, Nat.succLift⟩⟩

  def wf₁.{u} : WF valuation₁.{u} interpEx₁.{u} := by
    apply WF.ofLam
    intro t
    apply WF.ofApp
    case Hfn =>
      apply WF.ofAtom
    case Harg =>
      apply (WF.ofBVar ⟨0, by simp⟩)

  -- Original: Nat.add 2 3
  -- Lifting to: GLift.up (Nat.add 2 3)
  def Nat.addLift.{u} (x y : GLift.{1, u} Nat) :=
    GLift.up (Nat.add (GLift.down x) (GLift.down y))

  def interpEx₂.{u} : Lam2DJudge.{u} :=
    ⟨[], .app (.app (.atom 0) (.atom 1)) (.atom 2),
      GLift.{1, u + 1} Nat, GLift.up (Nat.add 2 3)⟩

  def valuation₂.{u} : Lam2DVal.{u} :=
    ⟨fun _ => GLift Nat, fun n =>
      [⟨GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat, Nat.addLift⟩,
       ⟨GLift.{1, u + 1} Nat, GLift.up 2⟩, ⟨GLift.{1, u + 1} Nat, GLift.up 3⟩].getD n ⟨GLift.{1, u + 1} Nat, GLift.up 0⟩⟩
  
  def wf₂.{u} : WF valuation₂.{u} interpEx₂.{u} := by
    apply WF.ofApp (fn := Nat.addLift (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg =>
      apply WF.ofAtom

  -- Original: @Eq Nat 2 3
  -- Lifting to: GLift.up (@Eq Nat 2 3)
  def interpEx₃.{u} : Lam2DJudge.{u} :=
    ⟨[], .app (.app (.atom 0) (.atom 1)) (.atom 2), Type u, GLift (2 = 3)⟩
  
  def valuation₃.{u} : Lam2DVal.{u} :=
    ⟨fun _ => GLift Nat, fun n =>
      [⟨GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat → Type u, @EqLift.{1, u + 1, u} Nat⟩,
       ⟨GLift.{1, u + 1} Nat, GLift.up 2⟩, ⟨GLift.{1, u + 1} Nat, GLift.up 3⟩].getD n ⟨GLift.{1, u + 1} Nat, GLift.up 0⟩⟩

  def wf₃.{u} : WF valuation₃.{u} interpEx₃.{u} := by
    apply WF.ofApp (fn := @EqLift.{1, u + 1, u} Nat (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg => apply WF.ofAtom

end Example

end Auto.ReifLam