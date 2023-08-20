import Std.Data.Nat.Lemmas
import Auto.Lib.NatExtra
import Auto.Lib.OptionExtra
import Auto.Lib.Containers

namespace Auto

namespace Bin

private theorem wfAux (n n' : Nat) : n = n' + 2 → n / 2 < n := by
  intro H; apply Nat.div_lt_self
  case hLtN =>
    cases n;
    contradiction;
    apply Nat.succ_le_succ; apply Nat.zero_le
  case hLtK => apply Nat.le_refl

theorem inductionOn.{u}
  {motive : Nat → Sort u} (x : Nat)
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : motive x :=
  match h : x with
  | 0 => base₀
  | 1 => base₁
  | x' + 2 => ind x' (inductionOn ((x' + 2) / 2) ind base₀ base₁)
decreasing_by apply wfAux; rfl

theorem induction.{u}
  {motive : Nat → Sort u}
  (ind : ∀ x, motive ((x + 2) / 2) → motive (x + 2))
  (base₀ : motive 0) (base₁ : motive 1) : ∀ x, motive x :=
  fun x => inductionOn x ind base₀ base₁

end Bin

inductive BinTree (α : Sort _) where
  | leaf : BinTree α
  | node : BinTree α → Option α → BinTree α → BinTree α

namespace BinTree

instance : Inhabited (BinTree α) where
  default := .leaf

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

def get?WF (bt : BinTree α) (n : Nat) : Option α :=
  match h : n with
  | 0 => .none
  | 1 => bt.val?
  | _ + 2 =>
    match Nat.mod n 2 with
    | 0 => get?WF bt.left! (Nat.div n 2)
    | _ + 1 => get?WF bt.right! (Nat.div n 2)
termination_by get?WF bt n => n
decreasing_by apply Bin.wfAux; assumption

theorem get?WF.succSucc (bt : BinTree α) (n : Nat) :
  get?WF bt (n + 2) = 
    match Nat.mod (n + 2) 2 with
    | 0 => get?WF bt.left! (Nat.div (n + 2) 2)
    | _ + 1 => get?WF bt.right! (Nat.div (n + 2) 2) := rfl

def get?Aux (bt : BinTree α) (n rd : Nat) : Option α :=
  match rd with
  | 0 => .none
  | .succ rd' =>
    match n with
    | 0 => .none
    | 1 => bt.val?
    | _ + 2 =>
      match Nat.mod n 2 with
      | 0 => get?Aux bt.left! (Nat.div n 2) rd'
      | _ + 1 => get?Aux bt.right! (Nat.div n 2) rd'

theorem get?Aux.equiv (bt : BinTree α) (n rd : Nat) :
  rd ≥ n → get?Aux bt n rd = get?WF bt n := by
  revert n bt; induction rd <;> intros bt n H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero]; rfl
  case succ rd' IH =>
    dsimp [get?Aux]
    match n with
    | 0 => rfl
    | 1 => rfl
    | n' + 2 =>
      dsimp;
      rw [get?WF.succSucc];
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

def get? (bt : BinTree α) (n : Nat) : Option α :=
  get?Aux bt n n

theorem get?.equiv (bt : BinTree α) (n : Nat) :
  get? bt n = get?WF bt n :=
  get?Aux.equiv _ _ n .refl

theorem get?_succSucc (bt : BinTree α) (n : Nat) :
  get? bt (n + 2) = 
    match (n + 2) % 2 with
    | 0 => get? bt.left! ((n + 2) / 2)
    | _ + 1 => get? bt.right! ((n + 2) / 2) := by
  rw [get?.equiv bt, get?.equiv bt.left!, get?.equiv bt.right!]
  apply get?WF.succSucc

theorem get?_leaf (n : Nat) : @get? α .leaf n = .none := by
  apply Bin.induction (motive := fun n => @get? α .leaf n = .none)
  case base₀ => rfl
  case base₁ => rfl
  case ind =>
    intro n IH; rw [get?_succSucc];
    cases (n + 2) % 2 <;> exact IH

def insertWF (bt : BinTree α) (n : Nat) (x : α) : BinTree α :=
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
      | .leaf => .node (insertWF .leaf (Nat.div n 2) x) .none .leaf
      | .node l v r => .node (insertWF l (Nat.div n 2) x) v r
    | _ + 1 =>
      match bt with
      | .leaf => .node .leaf .none (insertWF .leaf (Nat.div n 2) x)
      | .node l v r => .node l v (insertWF r (Nat.div n 2) x)
termination_by insertWF bt n x => n
decreasing_by rw [← h]; apply Bin.wfAux; assumption

theorem insertWF.succSucc (bt : BinTree α) (n : Nat) (x : α) :
  insertWF bt (n + 2) x = 
    match Nat.mod (n + 2) 2 with
    | 0 =>
      match bt with
      | .leaf => .node (insertWF .leaf (Nat.div (n + 2) 2) x) .none .leaf
      | .node l v r => .node (insertWF l (Nat.div (n + 2) 2) x) v r
    | _ + 1 =>
      match bt with
      | .leaf => .node .leaf .none (insertWF .leaf (Nat.div (n + 2) 2) x)
      | .node l v r => .node l v (insertWF r (Nat.div (n + 2) 2) x) := rfl

def insertAux (bt : BinTree α) (n : Nat) (x : α) (rd : Nat) : BinTree α :=
  match rd with
  | 0 => bt
  | .succ rd' =>
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
        | .leaf => .node (insertAux .leaf (Nat.div n 2) x rd') .none .leaf
        | .node l v r => .node (insertAux l (Nat.div n 2) x rd') v r
      | _ + 1 =>
        match bt with
        | .leaf => .node .leaf .none (insertAux .leaf (Nat.div n 2) x rd')
        | .node l v r => .node l v (insertAux r (Nat.div n 2) x rd')

theorem insertAux.equiv (bt : BinTree α) (n : Nat) (x : α) (rd : Nat) :
  rd ≥ n → insertAux bt n x rd = insertWF bt n x := by
  revert n bt; induction rd <;> intros bt n H
  case zero =>
    have hzero : n = 0 := Nat.eq_zero_of_le_zero H
    rw [hzero]; rfl
  case succ rd' IH =>
    dsimp [get?Aux]
    match n with
    | 0 => rfl
    | 1 => rfl
    | n' + 2 =>
      dsimp [insertAux];
      rw [insertWF.succSucc];
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

def insert (bt : BinTree α) (n : Nat) (x : α) := insertAux bt n x n

theorem insert.equiv (bt : BinTree α) (n : Nat) (x : α) :
  insert bt n x = insertWF bt n x :=
  insertAux.equiv _ n x n .refl

theorem insert.succSucc (bt : BinTree α) (n : Nat) (x : α) :
  insert bt (n + 2) x = 
    match (n + 2) % 2 with
    | 0 =>
      match bt with
      | .leaf => .node (insert .leaf ((n + 2) / 2) x) .none .leaf
      | .node l v r => .node (insert l ((n + 2) / 2) x) v r
    | _ + 1 =>
      match bt with
      | .leaf => .node .leaf .none (insert .leaf ((n + 2) / 2) x)
      | .node l v r => .node l v (insert r ((n + 2) / 2) x) := by
  rw [insert.equiv bt, insertWF.succSucc]
  rw [show Nat.mod (n + 2) 2 = (n + 2) % 2 by rfl]
  rw [show Nat.div (n + 2) 2 = (n + 2) / 2 by rfl]
  cases (n + 2) % 2 <;> cases bt <;> dsimp <;> rw [insert.equiv];

theorem insert.correct₁ (bt : BinTree β) (n : Nat) (x : β) : n ≠ 0 → get? (insert bt n x) n = .some x := by
  revert bt;
  let motive := fun n => ∀ (bt : BinTree β), n ≠ 0 →
    get? (insert bt n x) n = .some x
  apply Bin.induction (motive := motive)
  case base₀ => intros bt contra; contradiction
  case base₁ => intros bt _; cases bt <;> rfl
  case ind =>
    intros n IH bt _
    have hne' : (n + 2) / 2 ≠ 0 := by
      rw [Nat.add_div_right _ (.step .refl)]; intro h; cases h
    let IH' := fun bt => IH bt hne'
    rw [get?_succSucc, insert.succSucc, left!, right!]
    cases (n + 2) % 2 <;> cases bt <;> dsimp <;> rw [IH']

theorem insert.correct₂ (bt : BinTree β) (n₁ n₂ : Nat) (x : β) : n₁ ≠ n₂ → get? (insert bt n₁ x) n₂ = get? bt n₂ := by
  revert bt n₁;
  let motive := fun n₂ => ∀ (bt : BinTree β) (n₁ : Nat), n₁ ≠ n₂ →
    get? (insert bt n₁ x) n₂ = get? bt n₂
  apply Bin.induction (motive:=motive)
  case base₀ => intros bt n₂ _; cases bt <;> rfl
  case base₁ =>
    intros bt n₂ contra;
    match n₂ with
    | 0 => rfl
    | 1 => contradiction
    | n₂ + 2 => rw [insert.succSucc]; cases (n₂ + 2) % 2 <;> cases bt <;> rfl
  case ind =>
    intros n₂ IH bt n₁ hne;
    rw [get?_succSucc bt, get?_succSucc (insert bt n₁ x)]
    match n₁ with
    | 0 => cases bt <;> rfl
    | 1 => cases bt <;> rfl
    | n₁ + 2 =>
      rw [insert.succSucc, left!, right!]
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

def fold? (f : α → Option β → α → α) (init : α) : BinTree β → α
| .leaf => init
| .node l x r => f (fold? f init l) x (fold? f init r)

def all (p : α → Bool) := fold? (fun l x r => l && x.all p && r) true

theorem all_node (p : α → Bool) : all p (.node l x r) = (all p l && x.all p && all p r) := rfl

theorem all_spec (p : α → Bool) : BinTree.all p bt ↔
  (∀ n : Nat, (BinTree.get? bt n).all p = true) := by
  induction bt
  case leaf =>
    dsimp [all, fold?]; apply Iff.intro
    case mp => intro _ n; rw [get?_leaf]; rfl
    case mpr => intro _; rfl
  case node l x r IHl IHr =>
    rw [all_node]; apply Iff.intro
    case mp =>
      intro h n;
      simp at h; let ⟨⟨eql, eqx⟩, eqr⟩ := h
      match n with
      | 0 => rfl
      | 1 => exact eqx
      | n + 2 =>
        rw [get?_succSucc];
        cases (n + 2) % 2 <;> dsimp [left!, right!]
        case zero => apply IHl.mp eql
        case succ => apply IHr.mp eqr
    case mpr =>
      intro h; simp
      apply And.intro; apply And.intro
      case left.left =>
        apply IHl.mpr; intro n;
        match n with
        | 0 => rfl
        | 1 => exact (h 2)
        | n + 2 =>
          have h' := h (2 * n + 4);
          rw [get?_succSucc] at h'
          have eq₁ : (2 * n + 2 + 2) % 2 = 0 := by simp
          have eq₂ : (2 * n + 2 + 2) / 2 = n + 2 := by simp
          rw [eq₁, eq₂] at h'; exact h'
      case left.right => exact (h 1)
      case right =>
        apply IHr.mpr; intro n;
        match n with
        | 0 => rfl
        | 1 => exact (h 3)
        | n + 2 =>
          have h' := h (2 * n + 5)
          rw [get?_succSucc] at h'
          have eq₁ : (2 * n + 5) % 2 = 1 := by
            rw [Nat.add_mod]; simp
          have eq₂ : (2 * n + 5) / 2 = n + 2 := by
            rw [Nat.add_comm _ 5];
            rw [Nat.add_mul_div_left];
            rw [Nat.add_comm (5 / 2)]; rfl
            simp
          rw [eq₁, eq₂] at h'; exact h'

theorem all_insert (p : α → Bool) (bt : BinTree α) (n : Nat) (x : α) :
  all p (insert bt n x) ↔ (n ≠ 0 → p x) ∧ (∀ n', n' ≠ n → (bt.get? n').all p) := by
  rw [all_spec]; apply Iff.intro
  case mp =>
    intro H; apply And.intro
    case left =>
      intro hne; have H' := H n
      rw [insert.correct₁ _ _ _ hne] at H'; exact H'
    case right =>
      intro n' hne; have H' := H n'
      rw [insert.correct₂ _ _ _ _ (fun h => hne (Eq.symm h))] at H'; exact H'
  case mpr =>
    intro ⟨hzero, hsucc⟩ n';
    cases h : n.beq n'
    case false =>
      let h' := Nat.ne_of_beq_eq_false h
      rw [insert.correct₂ _ _ _ _ h']; apply hsucc _ (fun h => h' (Eq.symm h))
    case true =>
      let h' := Nat.eq_of_beq_eq_true h; cases h'
      cases n
      case zero => rfl
      case succ n => rw [insert.correct₁]; apply hzero; simp; simp

def allp (p : α → Prop) (bt : BinTree α) := ∀ n, Option.allp p (bt.get? n)

theorem allp_insert (p : α → Prop) (bt : BinTree α) (n : Nat) (x : α) :
  allp p (insert bt n x) ↔ (n ≠ 0 → p x) ∧ (∀ n', n' ≠ n → Option.allp p (bt.get? n')) := by
  apply Iff.intro
  case mp =>
    intro H; apply And.intro
    case left =>
      intro hne; have H' := H n
      rw [insert.correct₁ _ _ _ hne] at H'; exact H'
    case right =>
      intro n' hne; have H' := H n'
      rw [insert.correct₂ _ _ _ _ (fun h => hne (Eq.symm h))] at H'; exact H'
  case mpr =>
    intro ⟨hzero, hsucc⟩ n';
    cases h : n.beq n'
    case false =>
      let h' := Nat.ne_of_beq_eq_false h
      rw [insert.correct₂ _ _ _ _ h']; apply hsucc _ (fun h => h' (Eq.symm h))
    case true =>
      let h' := Nat.eq_of_beq_eq_true h; cases h'
      cases n
      case zero => exact True.intro
      case succ n => rw [insert.correct₁]; apply hzero; simp; simp

end BinTree
    
structure BinList (α : Sort _) where
  head : Option α
  tail : BinTree α

namespace BinList

def get? (bl : BinList α) (n : Nat) : Option α :=
  match n with
  | 0 => bl.head
  | _ + 1 => bl.tail.get? n

def insert (bl : BinList α) (n : Nat) (x : α) : BinList α :=
  match n with
  | 0 =>
    match bl with | ⟨_, tail⟩ => ⟨.some x, tail⟩
  | _ + 1 =>
    match bl with | ⟨head, tail⟩ => ⟨head, tail.insert n x⟩

theorem insert.correct₁ (bl : BinList α) (n : Nat) (x : α) : get? (insert bl n x) n = .some x := by
  match n with
  | 0 =>
    match bl with
    | ⟨_, tail⟩ => rfl
  | n + 1 => exact BinTree.insert.correct₁ _ _ _ (by intro h; cases h)

theorem insert.correct₂ (bl : BinList α) (n₁ n₂ : Nat) (x : α) : n₁ ≠ n₂ → get? (insert bl n₁ x) n₂ = get? bl n₂ := by
  match n₂ with
  | 0 =>
    match bl with
    | ⟨_, tail⟩ => intro hne; cases n₁ <;> first | contradiction | rfl
  | n + 1 =>
    match bl with
    | ⟨head, tail⟩ =>
      intro hne; dsimp [get?, insert];
      cases n₁
      case zero => rfl
      case succ _ => exact BinTree.insert.correct₂ _ _ _ _ hne

end BinList

end Auto