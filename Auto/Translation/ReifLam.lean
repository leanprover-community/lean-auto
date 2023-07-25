import Auto.Translation.Lift
import Auto.Util.ExprExtra
import Auto.Util.SigEq
import Std.Data.List.Lemmas

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.ReifLam

inductive LamSort
| atom : Nat → LamSort
| func : LamSort → LamSort → LamSort
deriving Inhabited, Hashable

def LamSort.reprPrec (s : LamSort) (n : Nat) :=
  let rec str :=
    match s with
    | .atom n     => f!".atom {n}"
    | .func s1 s2 => f!".func {LamSort.reprPrec s1 1} {LamSort.reprPrec s2 1}"
  if n == 0 then
    f!"Auto.ReifLam.LamSort" ++ str
  else
    f!"({str})"

instance : Repr LamSort where
  reprPrec s n := s.reprPrec n 

def LamSort.beq : LamSort → LamSort → Bool
| .atom m,     .atom n     => m == n
| .func m₁ n₁, .func m₂ n₂ => LamSort.beq m₁ m₂ && LamSort.beq n₁ n₂
| _,           _           => false

def LamSort.beq_refl : (a : LamSort) → (a.beq a) = true
| .atom m => by rw [beq]; apply Nat.beq_refl
| .func m₁ n₁ => by rw [beq]; rw [LamSort.beq_refl m₁]; rw [LamSort.beq_refl n₁]; rfl

def LamSort.beq_eq (a b : LamSort) : (a.beq b = true) → a = b := by
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

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive ErrSort : Sort u where
  | err : ErrSort

@[reducible] def LamSort.interp.{u} (val : Nat → Sort u) : LamSort → Sort u
| .atom n => val n
| .func dom cod => interp val dom → interp val cod

inductive LamTerm
| atom    : Nat → LamTerm
| bvar    : Nat → LamTerm
| lam     : LamSort → LamTerm → LamTerm
| app     : LamTerm → LamTerm → LamTerm
deriving Inhabited, Hashable

def LamTerm.reprPrec (t : LamTerm) (n : Nat) :=
  let s :=
    match t with
    | .atom m => f!".atom {m}"
    | .bvar m => f!".bvar {m}"
    | .lam s t => f!".lam {LamSort.reprPrec s 1} {LamTerm.reprPrec t 1}"
    | .app t₁ t₂ => f!".app {LamTerm.reprPrec t₁ 1} {LamTerm.reprPrec t₂ 1}"
  if n == 0 then
    f!"Auto.ReifLam.LamTerm" ++ s
  else
    f!"({s})"

instance : Repr LamTerm where
  reprPrec f n := LamTerm.reprPrec f n

@[reducible] def pushLCtx (lctx : Nat → α) (x : α) : Nat → α
| 0     => x
| n + 1 => lctx n

theorem pushLCtx.comm (f : α → β) (lctx : Nat → α) (x : α) :
  (fun n => f (pushLCtx lctx x n)) = pushLCtx (fun n => f (lctx n)) (f x) := by
  apply funext; intro n; cases n <;> simp

-- Typecheck. `lamVarTy, lctx ⊢ term : type?`
-- `lamVarTy : Nat → LamSort` : Valuation
-- `Nat → LamSort`        : Local Context
def LamTerm.check (lamVarTy : Nat → LamSort) : (Nat → LamSort) → LamTerm → Option LamSort
| _,    .atom n  => lamVarTy n
| lctx, .bvar n  => lctx n
| lctx, .lam s t =>
  match t.check lamVarTy (pushLCtx lctx s) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app fn arg =>
  match fn.check lamVarTy lctx, arg.check lamVarTy lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    if ty₁.beq argTy then .some ty₂ else none
  | _, _ => .none

-- Judgement. `lamVarTy, lctx ⊢ term : type?`
structure LamJudge where
  lctx   : Nat → LamSort
  rterm  : LamTerm
  rty    : LamSort
deriving Inhabited

inductive LamWF (lamVarTy : Nat → LamSort) : LamJudge → Type
  | ofAtom
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF lamVarTy ⟨lctx, .atom n, lamVarTy n⟩
  | ofBVar
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF lamVarTy ⟨lctx, .bvar n, lctx n⟩
  | ofLam
      {lctx : Nat → LamSort}
      {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
      (H : LamWF lamVarTy ⟨pushLCtx lctx argTy, body, bodyTy⟩) :
    LamWF lamVarTy ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
  | ofApp
      {lctx : Nat → LamSort}
      (argTy : LamSort) {resTy : LamSort}
      {fn : LamTerm} {arg : LamTerm}
      (HFn : LamWF lamVarTy ⟨lctx, fn, .func argTy resTy⟩)
      (HArg : LamWF lamVarTy ⟨lctx, arg, argTy⟩) :
    LamWF lamVarTy ⟨lctx, .app fn arg, resTy⟩

def LamWF.reprPrec (wf : LamWF f judge) (n : Nat) (lctxDep : Nat) :=
  let rec formatLCtxAux prec : (lctx : List LamSort) → Lean.Format
    | .nil => f!""
    | .cons a as => ", " ++ a.reprPrec prec ++ formatLCtxAux prec as
  let formatLCtx prec (lctx : Nat → LamSort) : (lctxDep : Nat) → Lean.Format
    | 0 => f!"[]"
    | n + 1 => f!"[" ++ (lctx 0).reprPrec prec ++
               formatLCtxAux prec ((List.range n).map (fun i => lctx (i + 1))) ++ f!"]"
  match wf with
  | @LamWF.ofAtom _ lctx m =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofAtom (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofAtom {m})"
  | @LamWF.ofBVar _ lctx m =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofBVar (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofBVar {m})"
  | @LamWF.ofLam _ lctx argTy bodyTy body H =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofLam (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"(body := {body.reprPrec 1}) {LamWF.reprPrec H 1 (lctxDep + 1)}"
    else
      f!"(.ofLam (argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec H 1 (lctxDep + 1)})"
  | @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofApp (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"(fn := {fn.reprPrec 1}) (arg := {arg.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1 lctxDep} {LamWF.reprPrec HArg 1 lctxDep}"
    else
      f!"(.ofApp (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1 lctxDep} {LamWF.reprPrec HArg 1 lctxDep})"

instance : Repr (LamWF lamVarTy judge) where
  reprPrec wf _ := LamWF.reprPrec wf 0 0

def LamWF.ofLamTerm {lamVarTy : Nat → LamSort} :
  {lctx : Nat → LamSort} → (t : LamTerm) → Option ((rty : LamSort) × LamWF lamVarTy ⟨lctx, t, rty⟩)
| lctx, .atom n => .some ⟨lamVarTy n, .ofAtom n⟩
| lctx, .bvar n => .some ⟨lctx n, .ofBVar n⟩
| lctx, .lam argTy body =>
  let bodyWf := @LamWF.ofLamTerm lamVarTy (pushLCtx lctx argTy) body
  match bodyWf with
  | .some ⟨bodyTy, wf⟩ => .some ⟨.func argTy bodyTy, .ofLam bodyTy wf⟩
  | .none => .none
| lctx, .app fn arg =>
  let fnWf := @LamWF.ofLamTerm lamVarTy lctx fn
  let argWf := @LamWF.ofLamTerm lamVarTy lctx arg
  match fnWf, argWf with
  | .some (⟨.func ty₁ ty₂, fnWf⟩), .some ⟨argTy, argWf⟩ =>
    match heq : ty₁.beq argTy with
    | true =>
      have tyEq := LamSort.beq_eq _ _ heq
      have fnWf' := tyEq ▸ fnWf
      .some ⟨ty₂, .ofApp argTy fnWf' argWf⟩
    | false => .none
  | _, _ => .none

-- #eval (@LamWF.ofLamTerm
--   (lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1))
--   (lctx := [])
--   (t := .lam (.atom 0) (.app (.atom 1) (.atom 0))))
-- 
-- #check Auto.ReifLam.LamWF.ofLam
--   (lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1))
--   (lctx := []) (argTy := (.atom 0)) (bodyTy := (.atom 1)) (body := (.app (.atom 1) (.atom 0))) (.ofApp (lctx := [(.atom 0)]) (argTy := (.atom 2)) (resTy := (.atom 1)) (.ofAtom 1) (.ofAtom 0))

def LamWF.complete_Aux
  {b : β} (p : Bool) (f : (p = true) → β) (eq : p = true) :
  (match (generalizing:=false) h : p with
  | true => f h
  | false => b) = f eq := by
  cases p
  case false => cases eq
  case true => simp

-- Of course `ofLamTerm` is sound with respect to `LamWF`. So, we
--   only need to show that it's complete
def LamWF.complete {lamVarTy : Nat → LamSort} :
  {j : LamJudge} → (wf : LamWF lamVarTy j) → LamWF.ofLamTerm j.rterm = .some ⟨j.rty, wf⟩
| .(_), @LamWF.ofAtom _ lctx n => rfl
| .(_), @LamWF.ofBVar _ lctx n => rfl
| .(_), @LamWF.ofLam _ lctx argTy bodyTy body H => by
  unfold ofLamTerm;
  have IH := LamWF.complete H; simp at IH; rw [IH];
| .(_), @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg => by
  unfold ofLamTerm;
  have IHFn := LamWF.complete HFn
  have IHArg := LamWF.complete HArg
  simp at IHFn; simp at IHArg
  rw [IHFn]; rw [IHArg]; simp; rw [LamSort.beq_refl]

def LamTerm.check_of_lamWF
  {lamVarTy : Nat → LamSort} {lctx : Nat → LamSort} {t : LamTerm} {ty : LamSort} :
  LamWF lamVarTy ⟨lctx, t, ty⟩ → t.check lamVarTy lctx = .some ty := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rty := ty : LamJudge} = Judge 
  intro HWf; revert lctx t ty JudgeEq; induction HWf
  case ofAtom lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq]; rfl
  case ofBVar lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]; rfl
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
    rw [@HFn_ih lctx' fn (LamSort.func argTy resTy)] <;> try rfl;
    rw [@HArg_ih lctx' arg argTy] <;> try rfl;
    simp [LamSort.beq_refl]

private def List.get?_eq_some' : {l : List α} → {n : Nat} → l.get? n = some a →
  (@PSigma (n < List.length l) (fun h => List.get l ⟨n, h⟩ = a))
| a::_,  0    , eq => ⟨Nat.succ_le_succ (Nat.zero_le _), by simp at eq; exact eq⟩
| _::as, n + 1, eq => by
    simp at eq; simp;
    match @List.get?_eq_some' α a as n eq with
    | PSigma.mk h' proof' =>
      apply PSigma.mk;
      case fst => apply Nat.succ_lt_succ; exact h'
      case snd => exact proof'
| .nil, _     , eq => by simp at eq

-- This function is meant to be `execute`-d (`eval`-ed), not `reduce`-d
def LamTerm.lamWF_of_check {lamVarTy : Nat → LamSort} :
  {lctx : Nat → LamSort} → {t : LamTerm} → {ty : LamSort} →
  t.check lamVarTy lctx = .some ty → LamWF lamVarTy ⟨lctx, t, ty⟩
| lctx, .atom n, ty, HCheck => by
  simp [check] at HCheck; rw [← HCheck]; apply LamWF.ofAtom
| lctx, .bvar n, ty, HCheck => by
  simp [check] at HCheck; rw [← HCheck]; apply LamWF.ofBVar
| lctx, .lam argTy body, ty, HCheck => by
  simp [check] at HCheck; revert HCheck
  cases CheckEq : check lamVarTy (pushLCtx lctx argTy) body
  case none => intro contra; cases contra
  case some bodyTy =>
    simp; intro tyEq; rw [← tyEq]
    apply LamWF.ofLam; apply (LamTerm.lamWF_of_check CheckEq)
| lctx, .app fn arg, ty, HCheck => by
  simp [check] at HCheck; revert HCheck
  match CheckFnEq : check lamVarTy lctx fn, CheckArgEq : check lamVarTy lctx arg with
  | .some (LamSort.func ty₁ ty₂), .some argTy =>
    simp;
    cases heq : LamSort.beq ty₁ argTy
    case false => intro contra; cases contra
    case true =>
      simp; intro H; rw [← H]; apply LamWF.ofApp (argTy:=ty₁);
      case HFn => apply (LamTerm.lamWF_of_check CheckFnEq)
      case HArg =>
        have heq' : ty₁ = argTy := LamSort.beq_eq _ _ heq
        rw [heq']
        apply (LamTerm.lamWF_of_check CheckArgEq)
  | .some (LamSort.func _ _), .none => intro contra; cases contra
  | .some (LamSort.atom _), _ => intro contra; cases contra
  | .none, _ => intro contra; cases contra

--#eval @LamTerm.wf_of_check
--  (lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1))
--  (lctx := [])
--  (t := .lam (.atom 0) (.app (.atom 1) (.atom 0)))
--  (ty := .func (.atom 0) (.atom 1))
--  rfl

structure LamValuation.{u} where
  lamVarTy  : Nat → LamSort
  tyVal     : Nat → Type u
  varVal    : ∀ (n : Nat), (lamVarTy n).interp tyVal

def LamTerm.interp.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (lwf : LamWF lval.lamVarTy ⟨lctxTy, t, rty⟩) → rty.interp lval.tyVal
| lctxTy, lctxTerm, @LamWF.ofAtom _ _ n => lval.varVal n
| lctxTy, lctxTerm, @LamWF.ofBVar _ _ n => lctxTerm n
| lctxTy, lctxTerm, @LamWF.ofLam _ _ argTy _ body H =>
  fun (x : argTy.interp lval.tyVal) =>
    LamTerm.interp lval (pushLCtx lctxTy argTy)
    (fun n => match n with | 0 => x | k + 1 => lctxTerm k) H
| lctxTy, lctxTerm, @LamWF.ofApp _ _ _ resTy _ _ HFn HArg =>
  let mfn := LamTerm.interp lval lctxTy lctxTerm HFn
  let marg := LamTerm.interp lval lctxTy lctxTerm HArg
  mfn marg

-- Valuation
structure Valuation.{u} where
  -- Valuation of free type variables to constants in COC
  tyVal  : Nat → Type u
  -- valuation of free variables to constants in COC
  varTy  : Nat → Type u
  varVal : ∀ (n : Nat), varTy n

@[reducible] def Valuation.ofLamValuation : LamValuation → Valuation :=
  fun ⟨lamVarTy, tyVal, varVal⟩ => ⟨tyVal, fun n => (lamVarTy n).interp tyVal, varVal⟩

-- Judgement, `lctx ⊢ rterm ≝ mterm : ty`
structure Judgement.{u} where
  -- Local context, list of CIC terms
  lctxTy   : Nat → Type u
  lctxTerm : ∀ (n : Nat), lctxTy n
  -- A term in simply typed lambda calculus
  rterm    : LamTerm
  -- Type of `mterm`
  ty       : Type u
  -- The CIC term that `rterm` translates into
  mterm    : ty

set_option genInjectivity false in
inductive WF.{u} (val : Valuation.{u}) : Judgement.{u} → Type (u + 1)
  | ofAtom
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n} (n : Nat) :
    WF val <|
      ⟨lctxTy, lctxTerm, (.atom n), val.varTy n, val.varVal n⟩
  | ofBVar
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n} (n : Nat) :
    WF val <|
      ⟨lctxTy, lctxTerm, .bvar n, lctxTy n, lctxTerm n⟩
  | ofLam
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hs : LamSort} {ht : LamTerm}
      (α β : Type u) (fn : α → β)
      (H : ∀ (t : α), WF val ⟨pushLCtx lctxTy α,
        (fun n => match n with | 0 => t | n + 1 => lctxTerm n), ht, β, fn t⟩)
      :
    WF val <|
      ⟨lctxTy, lctxTerm, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hfn harg : LamTerm}
      (α β : Type u) (fn : α → β) (arg : α)
      (Hfn : WF val ⟨lctxTy, lctxTerm, hfn, α → β, fn⟩)
      (Harg : WF val ⟨lctxTy, lctxTerm, harg, α, arg⟩)
      :
    WF val <|
      ⟨lctxTy, lctxTerm, .app hfn harg, β, fn arg⟩

def LamTerm.wf_of_lamWF.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (lwf : LamWF lval.lamVarTy ⟨lctxTy, t, rty⟩) →
  WF (Valuation.ofLamValuation lval)
    ⟨fun n => (lctxTy n).interp lval.tyVal, lctxTerm, t, rty.interp lval.tyVal, LamTerm.interp lval lctxTy lctxTerm lwf⟩
| lctxTy', lctxTerm', @LamWF.ofAtom _ _ n => WF.ofAtom _
| lctxTy', lctxTerm', @LamWF.ofBVar _ _ n => WF.ofBVar _
| lctxTy', lctxTerm', @LamWF.ofLam _ _ argTy bodyTy body H => @WF.ofLam (Valuation.ofLamValuation lval)
    (fun n => (lctxTy' n).interp lval.tyVal) lctxTerm'
    argTy body (LamSort.interp lval.tyVal argTy) (LamSort.interp lval.tyVal bodyTy)
    (LamTerm.interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H))
    (fun t' =>
      let ty₁ := fun n => LamSort.interp lval.tyVal (pushLCtx lctxTy' argTy n)
      let ty₂ := pushLCtx (fun n => LamSort.interp lval.tyVal (lctxTy' n)) (LamSort.interp lval.tyVal argTy)
      have hTyEq : ty₁ = ty₂ := by apply funext; intro n; cases n <;> simp
      let term₁ : ∀ (n : Nat), ty₁ n := fun n => match n with | 0 => t' | Nat.succ n => lctxTerm' n
      let term₂ : ∀ (n : Nat), ty₂ n := fun n => match n with | 0 => t' | Nat.succ n => lctxTerm' n
      have hTermEq : SigmaEq (fun (α : Nat → Type _) => (∀ (n : Nat), α n)) term₁ term₂ :=
        SigmaEq.of_heq (fun (α : Nat → Type u) => (n : Nat) → α n) (HEq.funext _ _ fun u =>
            match u with
            | 0 => HEq.refl _
            | n + 1 => HEq.refl _) hTyEq
      let motive := fun {ty : Nat → Type u} (term : ∀ n, ty n) =>
        WF (Valuation.ofLamValuation lval)
          ⟨ty, term, body, LamSort.interp lval.tyVal bodyTy, interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H) t'⟩
      let hWF : motive (ty:=ty₁) term₁ := LamTerm.wf_of_lamWF lval _ _ H
      @SigmaEq.ndrec (Nat → Type _) (fun α => (n : Nat) → α n) ty₁ term₁ motive hWF ty₂ term₂ hTermEq)
| lctxTy', lctxTerm', @LamWF.ofApp _ _ argTy resTy fn arg Hfn Harg =>
  let WFfn := LamTerm.wf_of_lamWF _ _ _ Hfn
  let WFarg := LamTerm.wf_of_lamWF _ _ _ Harg
  WF.ofApp _ _ _ _ WFfn WFarg

section Example
  
  def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  def interpEx₁.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .lam (.atom 0) (.app (.atom 0) (.bvar 0)),
     GLift.{1, u} Nat → GLift.{1, u} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  def valuation₁.{u} : Valuation.{u} :=
    ⟨fun _ => GLift Nat,
     fun _ => GLift.{1, u} Nat → GLift.{1, u} Nat,
     fun _ => Nat.succLift⟩

  def wf₁.{u} : WF valuation₁.{u} interpEx₁.{u} := by
    apply WF.ofLam
    intro t
    apply WF.ofApp
    case Hfn =>
      apply WF.ofAtom
    case Harg =>
      apply WF.ofBVar

  -- Original: Nat.add 2 3
  -- Lifting to: GLift.up (Nat.add 2 3)
  def Nat.addLift.{u} (x y : GLift.{1, u} Nat) :=
    GLift.up (Nat.add (GLift.down x) (GLift.down y))

  def interpEx₂.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .app (.app (.atom 0) (.atom 1)) (.atom 2),
      GLift.{1, u} Nat, GLift.up (Nat.add 2 3)⟩

  def valuation₂.{u} : Valuation.{u} :=
    ⟨fun _ => GLift Nat,
     fun n => [GLift.{1, u} Nat → GLift.{1, u} Nat → GLift.{1, u} Nat,
               GLift.{1, u} Nat, GLift.{1, u} Nat].getD n (GLift.{1, u} Nat),
     fun n =>
       match n with
       | 0 => Nat.addLift
       | 1 => GLift.up 2
       | 2 => GLift.up 3
       | _ + 3 => GLift.up 0⟩
  
  def wf₂.{u} : WF valuation₂.{u} interpEx₂.{u} := by
    apply WF.ofApp (fn := Nat.addLift (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg =>
      apply WF.ofAtom

  -- Original: @Eq Nat 2 3
  -- Lifting to: GLift.up (@Eq Nat 2 3)
  -- **Note**: Sometimes we might want to lift to universe `u + 1`
  --   to avoid universe level issues.
  def interpEx₃.{u} : Judgement.{u + 1} :=
    ⟨fun _ => Type u, fun _ => Sort u, .app (.app (.atom 0) (.atom 1)) (.atom 2), Type u, GLift (2 = 3)⟩
  
  def valuation₃.{u} : Valuation.{u + 1} :=
    ⟨fun _ => GLift Nat,
    fun n => [GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat → Type u,
              GLift.{1, u + 1} Nat,
              GLift.{1, u + 1} Nat].getD n (GLift.{1, u + 1} Nat),
    fun n =>
      match n with
      | 0 => @EqLift.{1, u + 1, u} Nat
      | 1 => GLift.up 2
      | 2 => GLift.up 3
      | _ + 3 => GLift.up 0⟩

  def wf₃.{u} : WF valuation₃.{u} interpEx₃.{u} := by
    apply WF.ofApp (fn := @EqLift.{1, u + 1, u} Nat (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg => apply WF.ofAtom

end Example

end Auto.ReifLam