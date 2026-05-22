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

inductive CBStatus
  | f -- full
  | p -- partially full
  | e -- empty

inductive CBTreeList (α : Type u) : Nat → CBStatus → Type u
  | f : α → CBTreeList α 1 .f
  | e : CBTreeList α 0 .e
  | ff {m n : Nat} : CBTreeList α m .f → CBTreeList α n .f → CBTreeList α (m + n) .f
  | fp {m n : Nat} : CBTreeList α m .f → CBTreeList α n .p → CBTreeList α (m + n) .p
  | fe {m : Nat} : CBTreeList α m .f → CBTreeList α 0 .e → CBTreeList α m .p
  | pe {m : Nat} : CBTreeList α m .p → CBTreeList α 0 .e → CBTreeList α m .p
  | ee : CBTreeList α 0 .e → CBTreeList α 0 .e → CBTreeList α 0 .e
  deriving Repr

namespace CBTreeList

theorem empty_iff_zero {α : Type u} {n : Nat} {s : CBStatus} (t : CBTreeList α n s) : s = .e ↔ n = 0 := by
  induction t <;> simp_all

def fapp {α : Type u} {m n : Nat} {s : CBStatus} (l : CBTreeList α m .f) (r : CBTreeList α n s) : (s' : CBStatus) × CBTreeList α (m + n) s' :=
  match s with
  | .f => ⟨.f, .ff l r⟩
  | .p => ⟨.p, .fp l r⟩
  | .e =>
    match r with
    | .e => ⟨.p, .fe l .e⟩
    | .ee rl rr => ⟨.p, .fe l (.ee rl rr)⟩

def appe {α : Type u} {m : Nat} {s : CBStatus} (l : CBTreeList α m s) (r : CBTreeList α 0 .e) : (s' : CBStatus) × CBTreeList α m s' :=
  match s with
  | .f => ⟨.p, .fe l r⟩
  | .p => ⟨.p, .pe l r⟩
  | .e =>
    match l with
    | .e => ⟨.e, .ee .e r⟩
    | .ee ll lr => ⟨.e, .ee (.ee ll lr) r⟩

def clear {α : Type u} {n : Nat} (s : CBStatus) : CBTreeList α n s → CBTreeList α 0 .e
| .f _ => .e
| .e => .e
| .ff l r => .ee (clear _ l) (clear _ r)
| .fp l r => .ee (clear _ l) (clear _ r)
| .fe l r => .ee (clear _ l) (clear _ r)
| .pe l r => .ee (clear _ l) r
| .ee l r => .ee l r

def pushEmpty {α : Type u} {n : Nat} : CBTreeList α n .e → (x : α) → (s' : CBStatus) × CBTreeList α 1 s'
| .e, x => ⟨.f, .f x⟩
| .ee l r, x =>
  match pushEmpty l x with
  | ⟨s', o⟩ => appe o r

def push {α : Type u} {n : Nat} {s : CBStatus} : CBTreeList α n s → (x : α) → (s' : CBStatus) × CBTreeList α (n + 1) s'
| .f l, x => ⟨.f, .ff (.f l) (.f x)⟩
| .e, x => ⟨.f, .f x⟩
| .ff l r, x => CBTreeList.fapp (.ff l r) (pushEmpty (clear .f (.ff l r)) x).snd
| @CBTreeList.fp _ m n l r, x =>
  (CBTreeList.fapp l (push r x).snd : (s' : CBStatus) × CBTreeList α (m + (n + 1)) s')
| .fe l r, x => CBTreeList.fapp l (push r x).snd
| .pe l r, x => appe (push l x).snd r
| .ee l r, x => appe (pushEmpty l x).snd r

def get {α : Type u} {n : Nat} {s : CBStatus} (t : CBTreeList α n s) (i : Nat) (h : i < n) : α :=
  match n, s, t with
  | _, _, .f x => x
  | 0, .e, .e => False.elim (Nat.not_lt_zero _ h)
  | _, _, @CBTreeList.ff _ m' n' l r =>
    if hi : i < m' then
      get l i hi
    else
      get r (i - m') (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h)
  | _, _, @CBTreeList.fp _ m' n' l r =>
    if hi : i < m' then
      get l i hi
    else
      get r (i - m') (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h)
  | _, _, @CBTreeList.fe _ m' l _ => get l i h
  | _, _, @CBTreeList.pe _ m' l _ => get l i h
  | 0, .e, .ee _ _ => False.elim (Nat.not_lt_zero _ h)

theorem get_fapp {α : Type u} {m n : Nat} {s : CBStatus} {l : CBTreeList α m .f} {r : CBTreeList α n s} {i : Nat} (h : i < m + n) :
  (l.fapp r).snd.get i h = if hi : i < m then l.get i hi else r.get (i - m) (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h) := by
  cases s <;> simp only [fapp]
  case f => simp [get]
  case p => simp [get]
  case e => cases r <;> simp only [Nat.add_zero] at h <;> simp [get, h]

theorem get_appe {α : Type u} {m : Nat} {s : CBStatus} {l : CBTreeList α m s} {r : CBTreeList α 0 .e} {i : Nat} (h : i < m) :
  (l.appe r).snd.get i h = l.get i h := by
  cases s <;> simp only [appe]
  case f => simp [get]
  case p => simp [get]
  case e => cases (empty_iff_zero l).mp rfl; contradiction

theorem get_pushEmpty_zero_ind {α : Type u} {m : Nat} {s : CBStatus} {t : CBTreeList α m s} {x : α} (hs : s = .e) :
  ((hs ▸ t).pushEmpty x).snd.get 0 .refl = x := by
  induction t <;> try contradiction
  case e => rw [pushEmpty]; simp [get]
  case ee l r hl hr =>
    rw [pushEmpty]
    have hl' : (l.pushEmpty x).snd.get 0 .refl = x := hl rfl
    revert hl'; cases l.pushEmpty x
    simp [get_appe]

theorem get_pushEmpty_zero {α : Type u} {m : Nat} {t : CBTreeList α m .e} {x : α} :
  (t.pushEmpty x).snd.get 0 .refl = x := by
  apply get_pushEmpty_zero_ind (t:=t) rfl

theorem get_push_lt {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} {x : α} {i : Nat} (h : i < n) :
    have hi' : i < n + 1 := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (t.push x).snd.get i hi' = t.get i h := by
  induction t generalizing i
  case f => cases Nat.lt_one_iff.mp h; simp [push, get]
  case e => contradiction
  case ff => simp [push, get, get_fapp, h]
  case fp m n l r hl hr =>
    simp only [push, get, get_fapp]
    by_cases him : i < m <;> simp only [him, ↓reduceDIte]
    rw [hr]
  case fe => simp [push, get, get_fapp, h]
  case pe => simp [push, get, get_appe, *]
  case ee => contradiction

theorem get_push_eq {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} {x : α} :
  (t.push x).snd.get n .refl = x := by
  induction t <;> try (simp [push, get]; done)
  case ff => simp [push, get_fapp, get_pushEmpty_zero]
  case fp m n l r hl hr =>
    have hmn : ¬ (m + n < m) := Nat.not_lt_of_le (Nat.le_add_right _ _)
    simp [push, get_fapp, hmn, hr]
  case fe => simp [push, get_fapp, *]
  case pe => simp [push, get_appe, *]
  case ee => simp [push, get_appe, get_pushEmpty_zero]

theorem get_push {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} {x : α} {i : Nat} (h : i < n + 1) :
  (t.push x).snd.get i h = if h : i < n then t.get i h else x := by
  by_cases h' : i < n
  case pos => simp [get_push_lt h', h']
  case neg =>
    have hin : i = n := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_lt h') h
    cases hin
    rw [get_push_eq]
    simp only [Nat.lt_irrefl, ↓reduceDIte]

end CBTreeList

structure TreeList (α : Type u) where
  length : Nat
  status : CBStatus
  data : CBTreeList α length status

namespace TreeList

def push {α : Type u} : TreeList α → α → TreeList α
| ⟨n, _, d⟩, x =>
  match CBTreeList.push d x with
  | ⟨s', o⟩ => ⟨n + 1, s', o⟩

def get {α : Type u} (t : TreeList α) (i : Nat) (h : i < t.length) :=
  t.data.get i h

instance {α : Type u} : GetElem (TreeList α) Nat α fun xs i => i < xs.length where
  getElem xs i h := xs.data.get i h

@[grind =] theorem getElem_push {α : Type u} {xs : TreeList α} {x : α} {i : Nat} (h : i < (xs.push x).length) :
  (xs.push x)[i] = if h : i < xs.length then xs[i] else x := CBTreeList.get_push h

end TreeList

end Auto
