import Lean
import Auto.MathlibEmulator
import Auto.Lib.BoolExtra
import Auto.Lib.NatExtra
import Auto.Lib.OptionExtra
import Auto.Lib.Containers
import Auto.Lib.Pos
import Auto.Lib.Bin
-- Make sure that `Lean.toExpr Nat` is overriden
import Auto.Lib.ToExprExtra

/-
  Polymorphic complete binary tree
  For definitions with `'`, the tree behaves as `{n : Nat // n ≠ 0} → α`
  For definitions without `'`, the tree behaves as `Nat → α`
-/

namespace Auto

open ToExprExtra

inductive TreeList (α : Type u) where
  | leaf : TreeList α
  | node : TreeList α → α → TreeList α → TreeList α
deriving Repr, Lean.ToExpr

namespace TreeList

instance : Inhabited (TreeList α) where
  default := .leaf

def beq [BEq α] (a b : TreeList α) : Bool :=
  match a, b with
  | .leaf, .leaf => true
  | .node la xa ra, .node lb xb rb => la.beq lb && xa == xb && ra.beq rb
  | _, _ => false

instance [BEq α] : BEq (TreeList α) where
  beq := beq

theorem beq_def [BEq α] {x y : TreeList α} : (x == y) = x.beq y := rfl

theorem beq_refl [BEq α] (α_beq_refl : ∀ (x : α), (x == x) = true)
    {a : TreeList α} : (a == a) = true := by
  induction a <;> try rfl
  case node l x r IHl IHr =>
    rw [beq_def]; rw [beq_def] at IHl IHr; dsimp [beq]; rw [IHl, IHr, α_beq_refl]; rfl

theorem eq_of_beq_eq_true [BEq α] (α_eq_of_beq_eq_true : ∀ (x y : α), (x == y) = true → x = y)
    {a b : TreeList α} (H : (a == b) = true) : a = b := by
  induction a generalizing b <;> cases b <;> try cases H <;> try rfl
  case node.node la xa ra IHla IHra lb xb rb =>
    rw [beq_def] at H; dsimp [beq] at H; rw [Bool.and_eq_true, Bool.and_eq_true] at H
    have ⟨⟨leq, xeq⟩, req⟩ := H
    rw [IHla leq, IHra req, α_eq_of_beq_eq_true _ _ xeq]

instance [BEq α] [LawfulBEq α] : LawfulBEq (TreeList α) where
  eq_of_beq := eq_of_beq_eq_true (@LawfulBEq.eq_of_beq _ _ _)
  rfl := beq_refl (@BEq.rfl _ _ _)

def val? (tl : TreeList α) : Option α :=
  match tl with
  | .leaf => .none
  | .node _ x _ => .some x

def valD (tl : TreeList α) (default : α) : α :=
  tl.val?.getD default

def left! (tl : TreeList α) : TreeList α :=
  match tl with
  | .leaf => .leaf
  | .node l _ _ => l

def right! (tl : TreeList α) : TreeList α :=
  match tl with
  | .leaf => .leaf
  | .node _ _ r => r

attribute [local simp] Bin.wfAux

def get?'WF (tl : TreeList α) (n : Nat) : Option α :=
  match _ : n with
  | 0 => .none
  | 1 => tl.val?
  | _ + 2 =>
    match Nat.mod n 2 with
    | 0 => get?'WF tl.left! (Nat.div n 2)
    | _ + 1 => get?'WF tl.right! (Nat.div n 2)

theorem get?'WF.succSucc (tl : TreeList α) (n : Nat) :
    get?'WF tl (n + 2) =
      match Nat.mod (n + 2) 2 with
      | 0 => get?'WF tl.left! (Nat.div (n + 2) 2)
      | _ + 1 => get?'WF tl.right! (Nat.div (n + 2) 2) := by
  rw [get?'WF]

def get?'Aux (tl : TreeList α) (n rd : Nat) : Option α :=
  match rd with
  | 0 => .none
  | .succ rd' =>
    match n with
    | 0 => .none
    | 1 => tl.val?
    | _ + 2 =>
      match Nat.mod n 2 with
      | 0 => get?'Aux tl.left! (Nat.div n 2) rd'
      | _ + 1 => get?'Aux tl.right! (Nat.div n 2) rd'

theorem get?'Aux.equiv (tl : TreeList α) (n rd : Nat) :
    rd ≥ n → get?'Aux tl n rd = get?'WF tl n := by
  induction rd generalizing tl n <;> intro H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero, get?'Aux, get?'WF]
  case succ rd' IH =>
    dsimp [get?'Aux]
    match n with
    | 0 => rw [get?'WF]
    | 1 => rw [get?'WF]
    | n' + 2 =>
      dsimp
      rw [get?'WF.succSucc]
      have heq' : Nat.mod (n' + 2) 2 = n' % 2 := by
        suffices (n' + 2) % 2 = n' % 2 by exact this
        rw [Nat.add_mod_right]
      have heqDiv : Nat.div (n' + 2) 2 = Nat.succ (n' / 2) := by
        suffices (n' + 2) / 2 = Nat.succ (n' / 2) by exact this
        rw [Nat.add_div_right]; simp
      rw [heq', heqDiv]
      have hge : rd' ≥ Nat.succ (n' / 2) := by
        apply Nat.le_trans (m := .succ n')
        apply Nat.succ_le_succ; apply Nat.div_le_self
        apply (Nat.le_of_succ_le_succ H)
      rw [IH (left! tl), IH (right! tl)] <;> assumption

def get?' (tl : TreeList α) (n : Nat) : Option α := get?'Aux tl n n

def get? (tl : TreeList α) (n : Nat) : Option α := get?' tl (.succ n)

theorem get?'.equiv (tl : TreeList α) (n : Nat) :
    get?' tl n = get?'WF tl n :=
  get?'Aux.equiv _ _ n .refl

theorem get?'_succSucc (tl : TreeList α) (n : Nat) :
    get?' tl (n + 2) =
      match (n + 2) % 2 with
      | 0 => get?' tl.left! ((n + 2) / 2)
      | _ + 1 => get?' tl.right! ((n + 2) / 2) := by
  rw [get?'.equiv tl, get?'.equiv tl.left!, get?'.equiv tl.right!]
  apply get?'WF.succSucc

theorem get?'_leaf (n : Nat) : @get?' α .leaf n = .none := by
  apply Bin.induction (motive := fun n => @get?' α .leaf n = .none)
  case base₀ => rfl
  case base₁ => rfl
  case ind =>
    intro n IH; rw [get?'_succSucc]
    cases (n + 2) % 2 <;> exact IH

/-
  `insert'` inserts value `x` at position `n`.
  When extending the tree to reach position `n`, newly created intermediate nodes
  are populated with `fill` (analogous to `Option.none` in `BinTree.insert'`).
-/
def insert'WF (tl : TreeList α) (n : Nat) (fill x : α) : TreeList α :=
  match _ : n with
  | 0 => tl
  | 1 =>
    match tl with
    | .leaf => .node .leaf x .leaf
    | .node l _ r => .node l x r
  | _ + 2 =>
    match Nat.mod n 2 with
    | 0 =>
      match tl with
      | .leaf => .node (insert'WF .leaf (Nat.div n 2) fill x) fill .leaf
      | .node l v r => .node (insert'WF l (Nat.div n 2) fill x) v r
    | _ + 1 =>
      match tl with
      | .leaf => .node .leaf fill (insert'WF .leaf (Nat.div n 2) fill x)
      | .node l v r => .node l v (insert'WF r (Nat.div n 2) fill x)

theorem insert'WF.succSucc (tl : TreeList α) (n : Nat) (fill x : α) :
    insert'WF tl (n + 2) fill x =
      match Nat.mod (n + 2) 2 with
      | 0 =>
        match tl with
        | .leaf => .node (insert'WF .leaf (Nat.div (n + 2) 2) fill x) fill .leaf
        | .node l v r => .node (insert'WF l (Nat.div (n + 2) 2) fill x) v r
      | _ + 1 =>
        match tl with
        | .leaf => .node .leaf fill (insert'WF .leaf (Nat.div (n + 2) 2) fill x)
        | .node l v r => .node l v (insert'WF r (Nat.div (n + 2) 2) fill x) := by
  cases tl <;> rw [insert'WF]

def insert'Aux (tl : TreeList α) (n : Nat) (fill x : α) (rd : Nat) : TreeList α :=
  match rd with
  | 0 => tl
  | .succ rd' =>
    match n with
    | 0 => tl
    | 1 =>
      match tl with
      | .leaf => .node .leaf x .leaf
      | .node l _ r => .node l x r
    | _ + 2 =>
      match Nat.mod n 2 with
      | 0 =>
        match tl with
        | .leaf => .node (insert'Aux .leaf (Nat.div n 2) fill x rd') fill .leaf
        | .node l v r => .node (insert'Aux l (Nat.div n 2) fill x rd') v r
      | _ + 1 =>
        match tl with
        | .leaf => .node .leaf fill (insert'Aux .leaf (Nat.div n 2) fill x rd')
        | .node l v r => .node l v (insert'Aux r (Nat.div n 2) fill x rd')

theorem insert'Aux.equiv (tl : TreeList α) (n : Nat) (fill x : α) (rd : Nat) :
    rd ≥ n → insert'Aux tl n fill x rd = insert'WF tl n fill x := by
  induction rd generalizing tl n <;> intro H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero, insert'Aux, insert'WF]
  case succ rd' IH =>
    match n with
    | 0 => rw [insert'Aux, insert'WF]
    | 1 => cases tl <;> rw [insert'Aux, insert'WF]
    | n' + 2 =>
      dsimp [insert'Aux]
      rw [insert'WF.succSucc]
      have heq' : Nat.mod (n' + 2) 2 = n' % 2 := by
        suffices (n' + 2) % 2 = n' % 2 by exact this
        rw [Nat.add_mod_right]
      have heqDiv : Nat.div (n' + 2) 2 = Nat.succ (n' / 2) := by
        suffices (n' + 2) / 2 = Nat.succ (n' / 2) by exact this
        rw [Nat.add_div_right]; simp
      rw [heq', heqDiv]
      have hge : rd' ≥ Nat.succ (n' / 2) := by
        apply Nat.le_trans (m := .succ n')
        apply Nat.succ_le_succ; apply Nat.div_le_self
        apply (Nat.le_of_succ_le_succ H)
      cases (n' % 2) <;> cases tl <;> dsimp <;> rw [IH] <;> assumption

def insert' (tl : TreeList α) (n : Nat) (fill x : α) : TreeList α :=
  insert'Aux tl n fill x n

def insert (tl : TreeList α) (n : Nat) (fill x : α) : TreeList α :=
  insert' tl (.succ n) fill x

theorem insert'.equiv (tl : TreeList α) (n : Nat) (fill x : α) :
    insert' tl n fill x = insert'WF tl n fill x :=
  insert'Aux.equiv _ n fill x n .refl

theorem insert'.succSucc (tl : TreeList α) (n : Nat) (fill x : α) :
    insert' tl (n + 2) fill x =
      match (n + 2) % 2 with
      | 0 =>
        match tl with
        | .leaf => .node (insert' .leaf ((n + 2) / 2) fill x) fill .leaf
        | .node l v r => .node (insert' l ((n + 2) / 2) fill x) v r
      | _ + 1 =>
        match tl with
        | .leaf => .node .leaf fill (insert' .leaf ((n + 2) / 2) fill x)
        | .node l v r => .node l v (insert' r ((n + 2) / 2) fill x) := by
  rw [insert'.equiv tl, insert'WF.succSucc]
  rw [@id (Nat.mod (n + 2) 2 = (n + 2) % 2) rfl]
  rw [@id (Nat.div (n + 2) 2 = (n + 2) / 2) rfl]
  cases (n + 2) % 2 <;> cases tl <;> dsimp <;> rw [insert'.equiv]

end TreeList

end Auto
