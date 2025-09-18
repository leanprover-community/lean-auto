import Lean
import Auto.MathlibEmulator
import Auto.Lib.BoolExtra
import Auto.Lib.NatExtra
import Auto.Lib.OptionExtra
import Auto.Lib.Containers
import Auto.Lib.Pos
-- Make sure that `Lean.toExpr Nat` is overriden
import Auto.Lib.ToExprExtra

set_option linter.unusedVariables false

/-
  Polymorphic binary tree
  For definitions with `'`, the tree behaves as `{n : Nat // n ≠ 0} → α`
  For definitions without `'`, the tree behaves as `Nat → α`
-/

namespace Auto

open ToExprExtra

namespace Bin

private theorem wfAux (n n' : Nat) : n = n' + 2 → n / 2 < n := by
  intro H; apply Nat.div_lt_self
  case hLtN =>
    cases n;
    contradiction;
    apply Nat.succ_le_succ; apply Nat.zero_le
  case hLtK => apply Nat.le_refl

def inductionOn.{u}
  {motive : Nat → Sort u} (x : Nat)
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : motive x :=
  match x with
  | 0 => base₀
  | 1 => base₁
  | x' + 2 => ind x' (inductionOn ((x' + 2) / 2) ind base₀ base₁)
decreasing_by apply wfAux; rfl

@[irreducible] def induction.{u}
  {motive : Nat → Sort u}
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : ∀ x, motive x :=
  fun x => inductionOn x ind base₀ base₁

end Bin

inductive BinTree (α : Type u) where
  | leaf : BinTree α
  | node : BinTree α → Option α → BinTree α → BinTree α
deriving Repr, Lean.ToExpr

namespace BinTree

instance : Inhabited (BinTree α) where
  default := .leaf

def beq [BEq α] (a b : BinTree α) :=
  match a, b with
  | .leaf, .leaf => true
  | .node la xa ra, .node lb xb rb => la.beq lb && xa == xb && ra.beq rb
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := beq

theorem beq_def [BEq α] {x y : BinTree α} : (x == y) = x.beq y := rfl

theorem beq_refl [BEq α] (α_beq_refl : ∀ (x : α), (x == x) = true)
  {a : BinTree α} : (a == a) = true := by
  induction a <;> try rfl
  case node l x r IHl IHr =>
    rw [beq_def]; rw [beq_def] at IHl IHr; dsimp [beq]; rw [IHl, IHr]
    rw [Option.beq_refl α_beq_refl]; rfl

def toString [ToString α] : BinTree α → String
| .leaf => ""
| .node l x r =>
  let sx := match x with | .some x => "|" ++ ToString.toString x ++ "|" | .none => ""
  "{" ++ l.toString ++ sx ++ r.toString ++ "}"

private def toStringDisplayAux [ToString α] (ctx : String) : BinTree α → String
| .leaf => ""
| .node l x r =>
  let sx := match x with | .some x => ctx ++ " : " ++ ToString.toString x ++ "\n" | .none => ""
  l.toStringDisplayAux (ctx ++ "0") ++ sx ++ r.toStringDisplayAux (ctx ++ "1")

def toStringDisplay [ToString α] (bt : BinTree α) := toStringDisplayAux "R" bt

theorem eq_of_beq_eq_true [BEq α] (α_eq_of_beq_eq_true : ∀ (x y : α), (x == y) = true → x = y)
  {a b : BinTree α} (H : (a == b) = true) : a = b := by
  induction a generalizing b <;> cases b <;> try cases H <;> try rfl
  case node.node la xa ra IHla IHra lb xb rb =>
    rw [beq_def] at H; dsimp [beq] at H; rw [Bool.and_eq_true, Bool.and_eq_true] at H
    have ⟨⟨leq, xeq⟩, req⟩ := H
    rw [IHla leq, IHra req, Option.eq_of_beq_eq_true α_eq_of_beq_eq_true xeq]

instance [BEq α] [LawfulBEq α] : LawfulBEq (BinTree α) where
  eq_of_beq := eq_of_beq_eq_true (@LawfulBEq.eq_of_beq _ _ _)
  rfl := beq_refl (@BEq.rfl _ _ _)

def val? (bt : BinTree α) : Option α :=
  match bt with
  | .leaf => .none
  | .node _ x _ => x

def valD (bt : BinTree α) (default : α) :=
  bt.val?.getD default

def left! (bt : BinTree α) :=
  match bt with
  | .leaf => leaf
  | .node l _ _ => l

def right! (bt : BinTree α) :=
  match bt with
  | .leaf => leaf
  | .node _ _ r => r

def get?'WF (bt : BinTree α) (n : Nat) : Option α :=
  match h : n with
  | 0 => .none
  | 1 => bt.val?
  | _ + 2 =>
    match Nat.mod n 2 with
    | 0 => get?'WF bt.left! (Nat.div n 2)
    | _ + 1 => get?'WF bt.right! (Nat.div n 2)
termination_by n
decreasing_by all_goals { rw [← h]; apply Bin.wfAux; assumption }

theorem get?'WF.succSucc (bt : BinTree α) (n : Nat) :
  get?'WF bt (n + 2) =
    match Nat.mod (n + 2) 2 with
    | 0 => get?'WF bt.left! (Nat.div (n + 2) 2)
    | _ + 1 => get?'WF bt.right! (Nat.div (n + 2) 2) := by
    rw [get?'WF]

def get?'Aux (bt : BinTree α) (n rd : Nat) : Option α :=
  match rd with
  | 0 => .none
  | .succ rd' =>
    match n with
    | 0 => .none
    | 1 => bt.val?
    | _ + 2 =>
      match Nat.mod n 2 with
      | 0 => get?'Aux bt.left! (Nat.div n 2) rd'
      | _ + 1 => get?'Aux bt.right! (Nat.div n 2) rd'

theorem get?'Aux.equiv (bt : BinTree α) (n rd : Nat) :
  rd ≥ n → get?'Aux bt n rd = get?'WF bt n := by
  induction rd generalizing bt n <;> intro H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero, get?'Aux, get?'WF]
  case succ rd' IH =>
    dsimp [get?'Aux]
    match n with
    | 0 => rw [get?'WF]
    | 1 => rw [get?'WF]
    | n' + 2 =>
      dsimp;
      rw [get?'WF.succSucc];
      have heq' : Nat.mod (n' + 2) 2 = n' % 2 := by
        suffices (n' + 2) % 2 = n' % 2 by exact this
        rw [Nat.add_mod_right]
      have heqDiv : Nat.div (n' + 2) 2 = Nat.succ (n' / 2) := by
        suffices (n' + 2) / 2 = Nat.succ (n' / 2) by exact this
        rw [Nat.add_div_right]; simp
      rw [heq', heqDiv];
      have hge : rd' ≥ Nat.succ (n' / 2) := by
        apply Nat.le_trans (m:=.succ n');
        apply Nat.succ_le_succ; apply Nat.div_le_self
        apply (Nat.le_of_succ_le_succ H)
      rw [IH (left! bt), IH (right! bt)] <;> assumption

def get?' (bt : BinTree α) (n : Nat) : Option α := get?'Aux bt n n

def get? (bt : BinTree α) (n : Nat) : Option α := get?' bt (.succ n)

theorem get?'.equiv (bt : BinTree α) (n : Nat) :
  get?' bt n = get?'WF bt n :=
  get?'Aux.equiv _ _ n .refl

theorem get?'_succSucc (bt : BinTree α) (n : Nat) :
  get?' bt (n + 2) =
    match (n + 2) % 2 with
    | 0 => get?' bt.left! ((n + 2) / 2)
    | _ + 1 => get?' bt.right! ((n + 2) / 2) := by
  rw [get?'.equiv bt, get?'.equiv bt.left!, get?'.equiv bt.right!]
  apply get?'WF.succSucc

theorem get?'_leaf (n : Nat) : @get?' α .leaf n = .none := by
  apply Bin.induction (motive := fun n => @get?' α .leaf n = .none)
  case base₀ => rfl
  case base₁ => rfl
  case ind =>
    intro n IH; rw [get?'_succSucc];
    cases (n + 2) % 2 <;> exact IH

def insert'WF (bt : BinTree α) (n : Nat) (x : α) : BinTree α :=
  match h : n with
  | 0 => bt
  | 1 =>
    match bt with
    | .leaf => .node .leaf x .leaf
    | .node l _ r => .node l x r
  | _ + 2 =>
    match Nat.mod n 2 with
    | 0 =>
      match bt with
      | .leaf => .node (insert'WF .leaf (Nat.div n 2) x) .none .leaf
      | .node l v r => .node (insert'WF l (Nat.div n 2) x) v r
    | _ + 1 =>
      match bt with
      | .leaf => .node .leaf .none (insert'WF .leaf (Nat.div n 2) x)
      | .node l v r => .node l v (insert'WF r (Nat.div n 2) x)
termination_by n
decreasing_by all_goals { rw [← h]; apply Bin.wfAux; assumption }

theorem insert'WF.succSucc (bt : BinTree α) (n : Nat) (x : α) :
  insert'WF bt (n + 2) x =
    match Nat.mod (n + 2) 2 with
    | 0 =>
      match bt with
      | .leaf => .node (insert'WF .leaf (Nat.div (n + 2) 2) x) .none .leaf
      | .node l v r => .node (insert'WF l (Nat.div (n + 2) 2) x) v r
    | _ + 1 =>
      match bt with
      | .leaf => .node .leaf .none (insert'WF .leaf (Nat.div (n + 2) 2) x)
      | .node l v r => .node l v (insert'WF r (Nat.div (n + 2) 2) x) := by
  cases bt <;> rw [insert'WF]

def insert'Aux (bt : BinTree α) (n : Nat) (x : α) (rd : Nat) : BinTree α :=
  match rd with
  | 0 => bt
  | .succ rd' =>
    match n with
    | 0 => bt
    | 1 =>
      match bt with
      | .leaf => .node .leaf x .leaf
      | .node l _ r => .node l x r
    | _ + 2 =>
      match Nat.mod n 2 with
      | 0 =>
        match bt with
        | .leaf => .node (insert'Aux .leaf (Nat.div n 2) x rd') .none .leaf
        | .node l v r => .node (insert'Aux l (Nat.div n 2) x rd') v r
      | _ + 1 =>
        match bt with
        | .leaf => .node .leaf .none (insert'Aux .leaf (Nat.div n 2) x rd')
        | .node l v r => .node l v (insert'Aux r (Nat.div n 2) x rd')

theorem insert'Aux.equiv (bt : BinTree α) (n : Nat) (x : α) (rd : Nat) :
  rd ≥ n → insert'Aux bt n x rd = insert'WF bt n x := by
  induction rd generalizing bt n <;> intro H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero, insert'Aux, insert'WF]
  case succ rd' IH =>
    match n with
    | 0 => rw [insert'Aux, insert'WF]
    | 1 => cases bt <;> rw [insert'Aux, insert'WF]
    | n' + 2 =>
      dsimp [insert'Aux];
      rw [insert'WF.succSucc];
      have heq' : Nat.mod (n' + 2) 2 = n' % 2 := by
        suffices (n' + 2) % 2 = n' % 2 by exact this
        rw [Nat.add_mod_right]
      have heqDiv : Nat.div (n' + 2) 2 = Nat.succ (n' / 2) := by
        suffices (n' + 2) / 2 = Nat.succ (n' / 2) by exact this
        rw [Nat.add_div_right]; simp
      rw [heq', heqDiv];
      have hge : rd' ≥ Nat.succ (n' / 2) := by
        apply Nat.le_trans (m:=.succ n');
        apply Nat.succ_le_succ; apply Nat.div_le_self
        apply (Nat.le_of_succ_le_succ H)
      cases (n' % 2) <;> cases bt <;> dsimp <;> rw [IH] <;> assumption

def insert' (bt : BinTree α) (n : Nat) (x : α) := insert'Aux bt n x n

def insert (bt : BinTree α) (n : Nat) (x : α) := insert' bt (.succ n) x

theorem insert'.equiv (bt : BinTree α) (n : Nat) (x : α) :
  insert' bt n x = insert'WF bt n x :=
  insert'Aux.equiv _ n x n .refl

theorem insert'.succSucc (bt : BinTree α) (n : Nat) (x : α) :
  insert' bt (n + 2) x =
    match (n + 2) % 2 with
    | 0 =>
      match bt with
      | .leaf => .node (insert' .leaf ((n + 2) / 2) x) .none .leaf
      | .node l v r => .node (insert' l ((n + 2) / 2) x) v r
    | _ + 1 =>
      match bt with
      | .leaf => .node .leaf .none (insert' .leaf ((n + 2) / 2) x)
      | .node l v r => .node l v (insert' r ((n + 2) / 2) x) := by
  rw [insert'.equiv bt, insert'WF.succSucc]
  rw [@id (Nat.mod (n + 2) 2 = (n + 2) % 2) rfl]
  rw [@id (Nat.div (n + 2) 2 = (n + 2) / 2) rfl]
  cases (n + 2) % 2 <;> cases bt <;> dsimp <;> rw [insert'.equiv];

theorem insert'.correct₁ (bt : BinTree β) (n : Nat) (x : β) : n ≠ 0 → get?' (insert' bt n x) n = .some x := by
  revert bt;
  let motive := fun n => ∀ (bt : BinTree β), n ≠ 0 →
    get?' (insert' bt n x) n = .some x
  apply Bin.induction (motive := motive)
  case base₀ => intros bt contra; contradiction
  case base₁ => intros bt _; cases bt <;> rfl
  case ind =>
    intros n IH bt _
    have hne' : (n + 2) / 2 ≠ 0 := by
      rw [Nat.add_div_right _ (.step .refl)]; intro h; cases h
    let IH' := fun bt => IH bt hne'
    rw [get?'_succSucc, insert'.succSucc, left!.eq_def, right!.eq_def]
    cases (n + 2) % 2 <;> cases bt <;> dsimp <;> rw [IH']

theorem insert.correct₁ (bt : BinTree β) (n : Nat) (x : β) : get? (insert bt n x) n = .some x :=
  insert'.correct₁ bt (.succ n) x (by intro h; cases h)

theorem insert'.correct₂ (bt : BinTree β) (n₁ n₂ : Nat) (x : β) : n₁ ≠ n₂ → get?' (insert' bt n₁ x) n₂ = get?' bt n₂ := by
  revert bt n₁;
  let motive := fun n₂ => ∀ (bt : BinTree β) (n₁ : Nat), n₁ ≠ n₂ →
    get?' (insert' bt n₁ x) n₂ = get?' bt n₂
  apply Bin.induction (motive:=motive)
  case base₀ => intros bt n₂ _; cases bt <;> rfl
  case base₁ =>
    intros bt n₂ contra;
    match n₂ with
    | 0 => rfl
    | 1 => contradiction
    | n₂ + 2 => rw [insert'.succSucc]; cases (n₂ + 2) % 2 <;> cases bt <;> rfl
  case ind =>
    intros n₂ IH bt n₁ hne;
    rw [get?'_succSucc bt, get?'_succSucc (insert' bt n₁ x)]
    match n₁ with
    | 0 => cases bt <;> rfl
    | 1 => cases bt <;> rfl
    | n₁ + 2 =>
      rw [insert'.succSucc, left!.eq_def, right!.eq_def]
      have hne' : (n₁ + 2) % 2 = (n₂ + 2) % 2 → (n₁ + 2) / 2 ≠ (n₂ + 2) / 2 := by
        intro heq h; apply hne;
        rw [← Nat.div_add_mod (n₁ + 2) 2, ← Nat.div_add_mod (n₂ + 2) 2]
        rw [heq, h]
      have hmod : ∀ {n n'}, (n % 2) = .succ n' → n % 2 = 1 := by
        intros n n' H;
        have hle : (n % 2) < 2 := Nat.mod_lt _ (.step .refl)
        revert H hle; cases (n % 2)
        case zero => intro contra; cases contra
        case succ a =>
          intro H hle; cases a
          case zero => rfl
          case succ a =>
            let u := fun {n m} => @Nat.le_of_succ_le_succ n m
            have hle' := u (u hle); cases hle'
      cases h₂ : (n₂ + 2) % 2 <;> cases h₁ : (n₁ + 2) % 2 <;> cases bt <;> dsimp <;> try rfl
      case zero.zero.leaf =>
        rw [IH _ _ (hne' (.trans h₁ (.symm h₂)))]; rfl;
      case zero.zero.node =>
        rw [IH _ _ (hne' (.trans h₁ (.symm h₂)))]; rfl;
      case succ.succ.leaf =>
        rw [IH _ _ (hne' (.trans (hmod h₁) (.symm (hmod h₂))))]; rfl;
      case succ.succ.node =>
        rw [IH _ _ (hne' (.trans (hmod h₁) (.symm (hmod h₂))))]; rfl;

theorem insert.correct₂ (bt : BinTree β) (n₁ n₂ : Nat) (x : β) (H : n₁ ≠ n₂) : get? (insert bt n₁ x) n₂ = get? bt n₂ :=
  insert'.correct₂ bt (.succ n₁) (.succ n₂) x (fun h => H (Nat.succ.inj h))

/-- Depth-first preorder traversal of the `BinTree` -/
def foldl (f : α → β → α) (init : α) : BinTree β → α
| .leaf => init
| .node l x r =>
  let lf := foldl f init l
  let mf :=
    match x with
    | .some x => f lf x
    | .none => lf
  foldl f mf r

theorem foldl_inv
  {f : α → β → α} {init : α} {bt : BinTree β}
  (inv : α → Prop) (zero : inv init) (ind : ∀ a b, inv a → inv (f a b)) :
  inv (foldl f init bt) := by
  revert init; induction bt <;> intros init zero
  case leaf => exact zero
  case node l x r IHl IHr =>
    dsimp [foldl]; apply IHr
    cases x
    case none => exact IHl zero
    case some x =>
      dsimp; apply ind; apply IHl zero

def allp' (p : α → Prop) (bt : BinTree α) := ∀ n, Option.allp p (bt.get?' n)

def allp (p : α → Prop) (bt : BinTree α) := ∀ n, Option.allp p (bt.get? n)

theorem allp_equiv : allp' p bt ↔ allp p bt := by
  apply Iff.intro <;> intro h n
  case mp => apply h
  case mpr =>
    cases n;
    case zero => exact True.intro
    case succ n => apply h

theorem allp'_leaf (p : α → Prop) : BinTree.leaf.allp' p ↔ True :=
  Iff.intro (fun _ => True.intro) (fun _ n => by rw [get?'_leaf]; exact True.intro)

theorem allp'_node (p : α → Prop) :
  (BinTree.node l x r).allp' p ↔ (l.allp' p) ∧ (Option.allp p x) ∧ (r.allp' p) := by
  dsimp [allp']; apply Iff.intro <;> intro h
  case mp =>
    apply And.intro ?left (And.intro ?middle ?right);
    case left =>
      intro n;
      match n with
      | 0 => exact True.intro
      | 1 => exact (h 2)
      | n + 2 =>
        have h' := h (2 * n + 4);
        rw [get?'_succSucc] at h'
        have eq₁ : (2 * n + 2 + 2) % 2 = 0 := by simp
        have eq₂ : (2 * n + 2 + 2) / 2 = n + 2 := by simp
        rw [eq₁, eq₂] at h'; exact h'
    case middle => exact (h 1)
    case right =>
      intro n;
      match n with
      | 0 => exact True.intro
      | 1 => exact (h 3)
      | n + 2 =>
        have h' := h (2 * n + 5)
        rw [get?'_succSucc] at h'
        have eq₁ : (2 * n + 5) % 2 = 1 := by
          simp [Nat.add_mod]
        have eq₂ : (2 * n + 5) / 2 = n + 2 := by
          rw [Nat.add_comm _ 5];
          rw [Nat.add_mul_div_left];
          rw [Nat.add_comm (5 / 2)]
          simp
        rw [eq₁, eq₂] at h'; exact h'
  case mpr =>
    intro n; let ⟨eql, ⟨eqx, eqr⟩⟩ := h
    match n with
    | 0 => exact True.intro
    | 1 => exact eqx
    | n + 2 =>
      rw [get?'_succSucc];
      cases (n + 2) % 2 <;> dsimp [left!, right!]
      case zero => apply eql
      case succ => apply eqr

theorem allp'_insert' (p : α → Prop) (bt : BinTree α) (n : Nat) (x : α) :
  allp' p (insert' bt n x) ↔ (n ≠ 0 → p x) ∧ (∀ n', n' ≠ n → Option.allp p (bt.get?' n')) := by
  apply Iff.intro
  case mp =>
    intro H; apply And.intro
    case left =>
      intro hne; have H' := H n
      rw [insert'.correct₁ _ _ _ hne] at H'; exact H'
    case right =>
      intro n' hne; have H' := H n'
      rw [insert'.correct₂ _ _ _ _ (fun h => hne (Eq.symm h))] at H'; exact H'
  case mpr =>
    intro ⟨hzero, hsucc⟩ n';
    cases h : n.beq n'
    case false =>
      let h' := Nat.ne_of_beq_eq_false h
      rw [insert'.correct₂ _ _ _ _ h']; apply hsucc _ (fun h => h' (Eq.symm h))
    case true =>
      let h' := Nat.eq_of_beq_eq_true h; cases h'
      cases n
      case zero => exact True.intro
      case succ n => rw [insert'.correct₁]; apply hzero; simp; simp

theorem allp_insert (p : α → Prop) (bt : BinTree α) (n : Nat) (x : α) :
  allp p (insert bt n x) ↔ p x ∧ (∀ n', n' ≠ n → Option.allp p (bt.get? n')) := by
  dsimp [insert]; rw [← allp_equiv]; rw [allp'_insert']; simp; intro _
  apply Iff.intro <;> intro h n' eq
  case mp => apply h; exact (fun h' => eq (Nat.succ.inj h'))
  case mpr =>
    match n' with | 0 => exact True.intro | .succ n' => apply h; exact (fun h' => eq (congrArg _ h'))

def all (p : α → Bool) := BinTree.foldl (fun i x => i && p x) true

theorem all_with_init (p : α → Bool) (bt : BinTree α) (init : Bool) :
  foldl (fun i x => i && p x) init bt = (all p bt && init) := by
  cases init <;> simp
  case false =>
    induction bt
    case leaf => rfl
    case node l x r IHl IHr =>
      cases x <;> dsimp [foldl] <;> rw [IHl] <;> exact IHr
  case true => rfl

theorem all_node (p : α → Bool) :
  all p (.node l x r) = (l.all p && x.all p && r.all p) := by
  dsimp [all, foldl]; rw [all_with_init]; dsimp [all]
  cases x <;> dsimp [Option.all]
  case none =>
    simp; apply Bool.and_comm
  case some x =>
    apply Bool.and_comm

theorem all_allp' (p : α → Bool) (bt : BinTree α) :
  (bt.all p = true) ↔ bt.allp' (fun x => p x = true) := by
  induction bt
  case leaf =>
    dsimp [all, foldl, allp']
    refine Iff.intro (fun _ n => by rw [get?'_leaf]; exact True.intro) (fun _ => rfl)
  case node l x r IHl IHr =>
    rw [all_node]; rw [Bool.and_eq_true]; rw [Bool.and_eq_true]
    rw [IHl, IHr]; rw [allp'_node]; rw [and_assoc]; rw [Option.all_allp]

theorem all_allp (p : α → Bool) (bt : BinTree α) :
  (bt.all p = true) ↔ bt.allp (fun x => p x = true) := by
  rw [← allp_equiv]; apply all_allp'

theorem all_spec' (p : α → Bool) (bt : BinTree α) :
  (bt.all p = true) ↔ (∀ n : Nat, (get?' bt n).all p = true) := by
  rw [all_allp']; dsimp [allp']; apply Iff.intro <;> intro h n
  case mp =>
    rw [Option.all_allp]; apply h
  case mpr =>
    rw [← Option.all_allp]; apply h

theorem all_spec (p : α → Bool) (bt : BinTree α) :
  (bt.all p = true) ↔ (∀ n : Nat, (get? bt n).all p = true) :=
  Iff.intro
    (fun h n => (all_spec' p bt).mp h (.succ n))
    (fun h => (all_spec' p bt).mpr (fun n => match n with | 0 => rfl | .succ n => h n))

theorem all_insert' (p : α → Bool) (bt : BinTree α) (n : Nat) (x : α) :
  (all p (insert' bt n x) = true) ↔ (n ≠ 0 → p x) ∧ (∀ n', n' ≠ n → (bt.get?' n').all p = true) := by
  rw [all_allp']; rw [allp'_insert']; simp; intro _;
  apply Iff.intro <;> intro h n' eq;
  case mp => rw [Option.all_allp]; apply h _ eq
  case mpr => rw [← Option.all_allp]; apply h _ eq

theorem all_insert (p : α → Bool) (bt : BinTree α) (n : Nat) (x : α) :
  (all p (insert bt n x) = true) ↔ p x ∧ (∀ n', n' ≠ n → (bt.get? n').all p = true) := by
  dsimp [insert]; rw [all_insert']; simp; intro _;
  apply Iff.intro <;> intro h n' eq
  case mp => apply h; exact (fun h' => eq (Nat.succ.inj h'))
  case mpr =>
    match n' with | 0 => rfl | .succ n' => apply h; exact (fun h' => eq (congrArg _ h'))

def mapOpt (f : α → Option β) : BinTree α → BinTree β
| .leaf => .leaf
| .node l x r => .node (mapOpt f l) (x.bind f) (mapOpt f r)

theorem mapOpt_allp' (f : α → Option β) (p : β → Prop) :
  (bt : BinTree α) → (bt.mapOpt f).allp' p ↔ bt.allp' (fun x => Option.allp p (f x))
| .leaf =>
  Iff.intro
    (fun _ n => by rw [get?'_leaf]; exact True.intro)
    (fun _ n => by dsimp [mapOpt]; rw [get?'_leaf]; exact True.intro)
| .node l x r => by
  dsimp [mapOpt]; rw [allp'_node p]; rw [allp'_node]
  rw [mapOpt_allp' f p l]; rw [mapOpt_allp' f p r];
  suffices h : Option.allp p (Option.bind x f) ↔ Option.allp (fun x => Option.allp p (f x)) x by rw [h]
  cases x <;> rfl

theorem mapOpt_allp (f : α → Option β) (p : β → Prop) (bt : BinTree α) :
  (bt.mapOpt f).allp p ↔ bt.allp (fun x => Option.allp p (f x)) := by
  rw [← allp_equiv]; rw [← allp_equiv]; apply mapOpt_allp'

theorem get?'_mapOpt (f : α → Option β) (bt : BinTree α) :
  (bt.mapOpt f).get?' n = (bt.get?' n).bind f := by
  induction bt generalizing n
  case leaf =>
    dsimp [mapOpt]; rw [get?'_leaf, get?'_leaf]; rfl
  case node l x r IHl IHr =>
    dsimp [mapOpt]
    match n with
    | 0 => rfl
    | 1 => rfl
    | n' + 2 =>
      rw [get?'_succSucc, get?'_succSucc]
      match (n' + 2) % 2 with
      | 0 => dsimp [left!]; rw [IHl]
      | .succ _ => dsimp [right!]; rw [IHr]

theorem get?_mapOpt (f : α → Option β) (bt : BinTree α) :
  (bt.mapOpt f).get? n = (bt.get? n).bind f := get?'_mapOpt f bt

-- **TODO**: Prove properties
-- Property : `xs.get? n = (ofListGet xs).get? n`
def ofListGet (xs : List α) : BinTree α :=
  let xs' := xs.zip (List.range xs.length)
  xs'.foldl (fun bt (x, n) => bt.insert' (.succ n) x) .leaf

/-- Property : `xs.foldl f init = (ofListFoldl xs).foldl f init` -/
partial def ofListFoldl (xs : List α) : BinTree α :=
  match xs with
  | [] => .leaf
  | _ :: _ =>
    let nElem := Nat.div xs.length 2
    let l := xs.take nElem
    let r := xs.drop (.succ nElem)
    let mid := xs[nElem]?
    .node (ofListFoldl l) mid (ofListFoldl r)

open Lean in
/-- Given a `bl : BinTree α`, return `Lean.toExpr (fun n => (BinTree.get? bl n).getD default)` -/
def toLCtx {α : Type u} [ToLevel.{u}] [ToExpr α] (bl : BinTree α) (default : α) : Expr :=
  let lvl := ToLevel.toLevel.{u}
  let type := toTypeExpr α
  let get?Expr := mkApp3 (.const ``BinTree.get? [lvl]) type (toExpr bl) (.bvar 0)
  let getDExpr := mkApp3 (.const ``Option.getD [lvl]) type get?Expr (ToExpr.toExpr default)
  .lam `n (.const ``Nat []) getDExpr .default

end BinTree


namespace BinTree

def get?Pos (bt : BinTree α) (p : Pos) : Option α :=
  match p with
  | .xH => bt.val?
  | .xO p' => get?Pos bt.left! p'
  | .xI p' => get?Pos bt.right! p'

theorem get?Pos_leaf (p : Pos) : @get?Pos α .leaf p = .none :=
  match p with
  | .xH => rfl
  | .xO p' => get?Pos_leaf p'
  | .xI p' => get?Pos_leaf p'

def insertPos (bt : BinTree α) (p : Pos) (x : α) : BinTree α :=
  match p with
  | .xH =>
    match bt with
    | .leaf => .node .leaf x .leaf
    | .node l _ r => .node l x r
  | .xO p' =>
    match bt with
    | .leaf => .node (insertPos .leaf p' x) .none .leaf
    | .node l v r => .node (insertPos l p' x) v r
  | .xI p' =>
    match bt with
    | .leaf => .node .leaf .none (insertPos .leaf p' x)
    | .node l v r => .node l v (insertPos r p' x)

theorem insertPos.correct₁ (bt : BinTree β) (p : Pos) (x : β) : get?Pos (insertPos bt p x) p = .some x := by
  induction p generalizing bt
  case xH =>
    cases bt <;> rfl
  case xO p' IH =>
    cases bt <;> apply IH
  case xI p' IH =>
    cases bt <;> apply IH

theorem insertPos.correct₂ (bt : BinTree β) (p₁ p₂ : Pos) (x : β) : p₁ ≠ p₂ → get?Pos (insertPos bt p₁ x) p₂ = get?Pos bt p₂ := by
  induction p₁ generalizing bt p₂ <;> intro hne
  case xH =>
    cases p₂ <;> cases bt <;> first | rfl | exact (False.elim (hne rfl))
  case xO p₁' IH =>
    cases bt <;> cases p₂ <;> try rfl
    case leaf.xO p₂' =>
      dsimp [insertPos, get?Pos, left!]; rw [IH _ _ (fun h => hne (congrArg _ h))]
    case node.xO l v r p₂' =>
      dsimp [insertPos, get?Pos, left!]; rw [IH _ _ (fun h => hne (congrArg _ h))]
  case xI p₁' IH =>
    cases bt <;> cases p₂ <;> try rfl
    case leaf.xI p₂' =>
      dsimp [insertPos, get?Pos, right!]; rw [IH _ _ (fun h => hne (congrArg _ h))]
    case node.xI l v r p₂' =>
      dsimp [insertPos, get?Pos, right!]; rw [IH _ _ (fun h => hne (congrArg _ h))]

def allpPos (p : α → Prop) (bt : BinTree α) := ∀ q, Option.allp p (bt.get?Pos q)

theorem allpPos_leaf (p : α → Prop) : BinTree.leaf.allpPos p ↔ True :=
  Iff.intro (fun _ => True.intro) (fun _ p => by rw [get?Pos_leaf]; exact True.intro)

theorem allpPos_node (p : α → Prop) :
  (BinTree.node l x r).allpPos p ↔ (l.allpPos p) ∧ Option.allp p x ∧ (r.allpPos p) := by
  dsimp [allpPos]; apply Iff.intro
  case mp =>
    intro h; apply And.intro ?left (And.intro ?middle ?right)
    case left =>
      intro p; exact (h (.xO p))
    case middle => exact (h .xH)
    case right =>
      intro p; exact (h (.xI p))
  case mpr =>
    intro ⟨hl, hx, hr⟩ q; cases q
    case xH => exact hx
    case xO p' => exact hl p'
    case xI p' => exact hr p'

theorem allpPos_insert (p : α → Prop) (bt : BinTree α) (q : Pos) (x : α) :
  allpPos p (insertPos bt q x) ↔ p x ∧ (∀ q', q ≠ q' → Option.allp p (bt.get?Pos q')) := by
  apply Iff.intro
  case mp =>
    intro H; apply And.intro
    case left =>
      have H' := H q; rw [insertPos.correct₁] at H'; exact H'
    case right =>
      intro q' hne;
      have H' := H q'; rw [insertPos.correct₂ _ _ _ _ hne] at H'; exact H'
  case mpr =>
    intro ⟨hx, ht⟩ q'; cases h : q.beq q'
    case false =>
      have hne : q ≠ q' := Pos.ne_of_beq_eq_false h
      rw [insertPos.correct₂ _ _ _ _ hne]; apply ht _ hne
    case true =>
      have he : q = q' := Pos.eq_of_beq_eq_true h
      rw [he]; rw [insertPos.correct₁]; exact hx

theorem mapOpt_allpPos (f : α → Option β) (p : β → Prop) :
  (bt : BinTree α) → (bt.mapOpt f).allpPos p ↔ bt.allpPos (fun x => Option.allp p (f x))
| .leaf =>
  Iff.intro
    (fun _ n => by rw [get?Pos_leaf]; exact True.intro)
    (fun _ n => by dsimp [mapOpt]; rw [get?Pos_leaf]; exact True.intro)
| .node l x r => by
  dsimp [mapOpt]; rw [allpPos_node]; rw [allpPos_node];
  apply Iff.intro
  case mp =>
    intro ⟨hl, hx, hr⟩;
    apply And.intro ?left (And.intro ?middle ?right)
    case left => exact (mapOpt_allpPos _ _ _).mp hl
    case middle =>
      cases x
      case none => exact True.intro
      case some x => exact hx
    case right => exact (mapOpt_allpPos _ _ _).mp hr
  case mpr =>
    intro ⟨hl, hx, hr⟩;
    apply And.intro ?left (And.intro ?middle ?right)
    case left => exact (mapOpt_allpPos _ _ _).mpr hl
    case middle =>
      cases x
      case none => exact True.intro
      case some x => exact hx
    case right => exact (mapOpt_allpPos _ _ _).mpr hr

open Lean in
/-- Given a `bl : BinTree α`, return `Lean.toExpr (fun n => (BinTree.get?Pos bl n).getD default)` -/
def toLCtxPos {α : Type u} [ToLevel.{u}] [ToExpr α] (bl : BinTree α) (default : α) : Expr :=
  let lvl := ToLevel.toLevel.{u}
  let type := toTypeExpr α
  let get?Expr := mkApp3 (.const ``BinTree.get?Pos [lvl]) type (toExpr bl) (.bvar 0)
  let getDExpr := mkApp3 (.const ``Option.getD [lvl]) type get?Expr (ToExpr.toExpr default)
  .lam `n (.const ``Pos []) getDExpr .default

end BinTree

end Auto
