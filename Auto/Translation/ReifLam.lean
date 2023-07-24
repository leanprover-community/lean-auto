import Auto.Translation.Lift
import Auto.Util.ExprExtra
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

-- Typecheck. `lamVarTy, lctx ⊢ term : type?`
-- `lamVarTy : Nat → LamSort` : Valuation
-- `List LamSort`        : Local Context
def LamTerm.check (lamVarTy : Nat → LamSort) : List LamSort → LamTerm → Option LamSort
| _,    .atom n  => lamVarTy n
| lctx, .bvar n  => lctx.get? n
| lctx, .lam s t =>
  match t.check lamVarTy (s :: lctx) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app fn arg =>
  match fn.check lamVarTy lctx, arg.check lamVarTy lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    if ty₁.beq argTy then .some ty₂ else none
  | _, _ => .none

-- Judgement. `lamVarTy, lctx ⊢ term : type?`
structure LamJudge where
  lctx   : List LamSort
  rterm  : LamTerm
  rty    : LamSort
deriving Inhabited, Hashable

inductive LamWF (lamVarTy : Nat → LamSort) : LamJudge → Type
  | ofAtom
      {lctx : List LamSort} (n : Nat) :
    LamWF lamVarTy ⟨lctx, .atom n, lamVarTy n⟩
  | ofBVar
      {lctx : List LamSort} (n : Fin lctx.length) :
    LamWF lamVarTy ⟨lctx, .bvar n, lctx[n]⟩
  | ofLam
      {lctx : List LamSort}
      {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
      (H : LamWF lamVarTy ⟨argTy :: lctx, body, bodyTy⟩) :
    LamWF lamVarTy ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
  | ofApp
      {lctx : List LamSort}
      (argTy : LamSort) {resTy : LamSort}
      {fn : LamTerm} {arg : LamTerm}
      (HFn : LamWF lamVarTy ⟨lctx, fn, .func argTy resTy⟩)
      (HArg : LamWF lamVarTy ⟨lctx, arg, argTy⟩) :
    LamWF lamVarTy ⟨lctx, .app fn arg, resTy⟩

def LamWF.reprPrec (wf : LamWF f judge) (n : Nat) :=
  let rec formatLCtxAux m : (lctx : List LamSort) → Lean.Format
    | .nil => f!""
    | .cons a as => ", " ++ a.reprPrec m ++ formatLCtxAux m as
  let formatLCtx m : (lctx : List LamSort) → Lean.Format
    | .nil => f!"[]"
    | a::as => f!"[" ++ a.reprPrec m ++ formatLCtxAux m as ++ f!"]"
  match wf with
  | @LamWF.ofAtom _ lctx m =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofAtom (lctx := {formatLCtx 1 lctx}) {m}"
    else
      f!"(.ofAtom {m})"
  | @LamWF.ofBVar _ lctx m =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofBVar (lctx := {formatLCtx 1 lctx}) {m}"
    else
      f!"(.ofBVar {m})"
  | @LamWF.ofLam _ lctx argTy bodyTy body H =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofLam (lctx := {formatLCtx 1 lctx}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"(body := {body.reprPrec 1}) {LamWF.reprPrec H 1}"
    else
      f!"(.ofLam (argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec H 1})"
  | @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofApp (lctx := {formatLCtx 1 lctx}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"(fn := {fn.reprPrec 1}) (arg := {arg.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1} {LamWF.reprPrec HArg 1}"
    else
      f!"(.ofApp (lctx := {formatLCtx 1 lctx}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1} {LamWF.reprPrec HArg 1})"

instance : Repr (LamWF lamVarTy judge) where
  reprPrec wf _ := LamWF.reprPrec wf 0

def LamWF.ofLamTerm {lamVarTy : Nat → LamSort} :
  {lctx : List LamSort} → (t : LamTerm) → Option ((rty : LamSort) × LamWF lamVarTy ⟨lctx, t, rty⟩)
| lctx, .atom n => .some ⟨lamVarTy n, .ofAtom n⟩
| lctx, .bvar n =>
  match h : Nat.blt n lctx.length with
  | true =>
    let h' := Nat.le_of_ble_eq_true h;
    let fin : Fin lctx.length := ⟨n, h'⟩
    .some ⟨lctx[fin], .ofBVar fin⟩
  | false => .none
| lctx, .lam argTy body =>
  let bodyWf := @LamWF.ofLamTerm lamVarTy (argTy :: lctx) body
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
| .(_), @LamWF.ofBVar _ lctx n => by
  unfold ofLamTerm;
  unfold Nat.blt;
  cases n;
  case mk val isLt =>
    have heq := @LamWF.complete_Aux
    simp at heq; rw [heq]; apply Nat.ble_eq_true_of_le; exact isLt
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
  {lamVarTy : Nat → LamSort} {lctx : List LamSort} {t : LamTerm} {ty : LamSort} :
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
  {lctx : List LamSort} → {t : LamTerm} → {ty : LamSort} →
  t.check lamVarTy lctx = .some ty → LamWF lamVarTy ⟨lctx, t, ty⟩
| lctx, .atom n, ty, HCheck => by
  simp [check] at HCheck; rw [← HCheck]; apply LamWF.ofAtom
| lctx, .bvar n, ty, HCheck => by
  simp [check] at HCheck;
  have HCheck' := List.get?_eq_some' HCheck
  cases HCheck'
  case mk hLt HEq =>
    rw [← HEq]; apply LamWF.ofBVar (n := ⟨n, hLt⟩)
| lctx, .lam argTy body, ty, HCheck => by
  simp [check] at HCheck; revert HCheck
  cases CheckEq : check lamVarTy (argTy :: lctx) body
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
  (lctx : List ((α : LamSort) × α.interp lval.tyVal)) →
  let lctx' := lctx.map (fun x => x.fst)
  (lwf : LamWF lval.lamVarTy ⟨lctx', t, rty⟩) → rty.interp lval.tyVal
| lctx,  @LamWF.ofAtom _ _ n => lval.varVal n
| lctx,  @LamWF.ofBVar _ _ n =>
  let rec bvarAux :
    (lctx : List ((α : LamSort) × α.interp lval.tyVal)) →
    (n : Fin (List.length (List.map (fun (x : (α : LamSort) × LamSort.interp lval.tyVal α) => x.fst) lctx))) →
    let lctx' := lctx.map (fun x => Sigma.fst x)
    LamSort.interp lval.tyVal lctx'[n]
  | a::_, ⟨0, _⟩  => a.snd
  | _::as, ⟨n + 1, hsn⟩ =>
    let hsn' : n < List.length (List.map (fun x => x.fst) as) :=
      Nat.lt_of_succ_lt_succ hsn
    bvarAux as ⟨n, hsn'⟩
  bvarAux lctx n
| lctx, @LamWF.ofLam _ _ argTy bodyTy body H =>
  fun (x : argTy.interp lval.tyVal) =>
    LamTerm.interp lval (⟨argTy, x⟩ :: lctx) H
| lctx, @LamWF.ofApp _ _ argTy resTy fn arg HFn HArg =>
  let mfn := LamTerm.interp lval lctx HFn
  let marg := LamTerm.interp lval lctx HArg
  mfn marg

-- Valuation
structure Valuation.{u} where
  -- Valuation of free type variables to constants in COC
  tyVal  : Nat → Type u
  -- valuation of free variables to constants in COC
  varVal : Nat → (α : Type u) × α

@[reducible] def Valuation.ofLamValuation : LamValuation → Valuation :=
  fun ⟨lamVarTy, tyVal, varVal⟩ => ⟨tyVal, fun n => ⟨(lamVarTy n).interp tyVal, varVal n⟩⟩

-- Judgement, `lctx ⊢ rterm ≝ mterm : ty`
structure Judgement.{u} where
  -- Local context, list of CIC terms
  lctx    : List ((α : Type u) × α)
  -- A term in simply typed lambda calculus
  rterm   : LamTerm
  -- Type of `mterm`
  ty      : Type u
  -- The CIC term that `rterm` translates into
  mterm   : ty

inductive WF.{u} (val : Valuation.{u}) : Judgement.{u} → Prop
  | ofAtom
      {lctx : List ((γ : Type u) × γ)}
      (n : Nat) :
    WF val <|
      let ci := val.varVal n
      ⟨lctx, (.atom n), ci.fst, ci.snd⟩
  | ofBVar
      {lctx : List ((α : Type u) × α)}
      (n : Fin lctx.length) :
    WF val <|
      ⟨lctx, .bvar n, lctx[n].fst, lctx[n].snd⟩
  | ofLam
      {lctx : List ((γ : Type u) × γ)}
      {hs : LamSort} {ht : LamTerm}
      (α β : Type u) (fn : α → β)
      (H : ∀ (t : α), WF val ⟨⟨α, t⟩ :: lctx, ht, β, fn t⟩)
      :
    WF val <|
      ⟨lctx, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctx : List ((γ : Type u) × γ)}
      {hfn harg : LamTerm}
      (α β : Type u) (fn : α → β) (arg : α)
      (Hfn : WF val ⟨lctx, hfn, α → β, fn⟩)
      (Harg : WF val ⟨lctx, harg, α, arg⟩)
      :
    WF val <|
      ⟨lctx, .app hfn harg, β, fn arg⟩

-- def LamTerm.wf_of_lamWF.{u} (lval : LamValuation.{u}) :
--   (lctx : List ((α : LamSort) × α.interp lval.tyVal)) →
--   let lctx' := lctx.map (fun x => x.fst)
--   (lwf : LamWF lval.lamVarTy ⟨lctx', t, rty⟩) →
--   let lctxW := lctx.map (fun x => ⟨x.fst.interp lval.tyVal, x.snd⟩)
--   WF (Valuation.ofLamValuation lval)
--     ⟨lctxW, t, rty.interp lval.tyVal, LamTerm.interp lval lctx lwf⟩
-- | lctx, @LamWF.ofAtom _ _ n => WF.ofAtom _
-- | lctx, @LamWF.ofBVar _ _ n => by
--   let rec bvarAux : (lctx : List _) → (n : Fin _) → WF (Valuation.ofLamValuation lval)
--     { lctx := List.map (fun x => { fst := LamSort.interp lval.tyVal x.fst, snd := x.snd }) lctx, rterm := bvar n.val,
--       ty := LamSort.interp lval.tyVal (List.map (fun x => x.fst) lctx)[n], mterm := interp lval lctx (LamWF.ofBVar n) }
--   | a::as, ⟨0, h0⟩ =>
--     let tr : List ((α : LamSort) × LamSort.interp lval.tyVal α) → List ((α : Type u) × α) :=
--       List.map (fun x => { fst := LamSort.interp lval.tyVal x.fst, snd := x.snd })
--     WF.ofBVar
--     (lctx := tr (a :: as))
--     ⟨0, Nat.zero_lt_succ (List.length (tr as))⟩
--   | a::as, ⟨k + 1, hsk⟩ =>
--     let hsk' := Nat.lt_of_succ_lt_succ hsk
--     bvarAux as ⟨k, hsk'⟩
--   bvarAux lctx n
-- | _, _ => sorry

section Example
  
  def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  def interpEx₁.{u} : Judgement.{u} :=
    ⟨[], .lam (.atom 0) (.app (.atom 0) (.bvar 0)),
     GLift.{1, u} Nat → GLift.{1, u} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  def valuation₁.{u} : Valuation.{u} :=
    ⟨fun _ => GLift Nat,
     fun _ => ⟨GLift.{1, u} Nat → GLift.{1, u} Nat, Nat.succLift⟩⟩

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

  def interpEx₂.{u} : Judgement.{u} :=
    ⟨[], .app (.app (.atom 0) (.atom 1)) (.atom 2),
      GLift.{1, u} Nat, GLift.up (Nat.add 2 3)⟩

  def valuation₂.{u} : Valuation.{u} :=
    ⟨fun _ => GLift Nat, fun n =>
      [⟨GLift.{1, u} Nat → GLift.{1, u} Nat → GLift.{1, u} Nat, Nat.addLift⟩,
       ⟨GLift.{1, u} Nat, GLift.up 2⟩, ⟨GLift.{1, u} Nat, GLift.up 3⟩].getD n ⟨GLift.{1, u} Nat, GLift.up 0⟩⟩
  
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
    ⟨[], .app (.app (.atom 0) (.atom 1)) (.atom 2), Type u, GLift (2 = 3)⟩
  
  def valuation₃.{u} : Valuation.{u + 1} :=
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