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

def prune {α : Type u} {n : Nat} : CBTreeList α n .p → CBTreeList α n .f
| .fp l r => .ff l (prune r)
| .fe l r => l
| .pe l r => prune l

def append {α : Type u} {m n : Nat} {s₁ s₂ : CBStatus} (l : CBTreeList α m s₁) (r : CBTreeList α n s₂) :
  (s' : CBStatus) × (CBTreeList α (m + n) s') :=
  match s₁ with
  | .f => l.fapp r
  | .p => (prune l).fapp r
  | .e => ⟨s₂, ((empty_iff_zero l).mp rfl ▸ (Nat.zero_add _ ▸ r : CBTreeList α (0 + n) s₂))⟩

@[semireducible] def pushEmpty {α : Type u} {n : Nat} : CBTreeList α n .e → (x : α) → (s' : CBStatus) × CBTreeList α 1 s'
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

def pushManyRev {α : Type u} {n : Nat} {s : CBStatus} (t : CBTreeList α n s) : (xs : List α) → (s' : CBStatus) × CBTreeList α (n + xs.length) s'
| .nil => ⟨s, t⟩
| .cons x xs => (pushManyRev t xs).snd.push x

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

def toList {α : Type u} {n : Nat} {s : CBStatus} : CBTreeList α n s → List α
| .f x => [x]
| .e => []
| .ff l r => l.toList ++ r.toList
| .fp l r => l.toList ++ r.toList
| .fe l _ => l.toList
| .pe l _ => l.toList
| .ee _ _ => []

def toListRev {α : Type u} {n : Nat} {s : CBStatus} : CBTreeList α n s → List α
| .f x => [x]
| .e => []
| .ff l r => r.toListRev ++ l.toListRev
| .fp l r => r.toListRev ++ l.toListRev
| .fe l _ => l.toListRev
| .pe l _ => l.toListRev
| .ee _ _ => []

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

theorem get_prune_ind {α : Type u} {m : Nat} {s : CBStatus} {t : CBTreeList α m s} {i : Nat} (h : i < m) (hs : s = .p) :
  t.get i h = (hs ▸ t).prune.get i h := by
  induction t generalizing i <;> try contradiction
  case fp l r hl hr => simp [get, prune, hr]
  case fe => simp [get, prune]
  case pe l r hl hr => simp [get, prune, hl]

theorem get_prune {α : Type u} {m : Nat} {t : CBTreeList α m .p} {i : Nat} (h : i < m) :
  t.get i h = t.prune.get i h := get_prune_ind _ rfl

theorem get_append {α : Type u} {m n : Nat} {s₁ s₂ : CBStatus} {t₁ : CBTreeList α m s₁} {t₂ : CBTreeList α n s₂} {i : Nat} (h : i < m + n) :
  (t₁.append t₂).snd.get i h = if hi : i < m then t₁.get i hi else t₂.get (i - m) (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h) := by
  cases s₁
  case f => simp only [append, get_fapp]
  case p => simp only [append, get_fapp, get_prune]
  case e =>
    cases (empty_iff_zero t₁).mp rfl
    simp only [append, Nat.not_lt_zero, ↓reduceDIte]
    congr
    . apply Nat.zero_add
    . apply eqRec_heq
    . simp

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

theorem toList_length {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} :
  t.toList.length = n := by
  induction t <;> simp [toList, List.length_append, *]

theorem toList_get {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} {i : Nat} (h : i < n) :
  t.toList[i]'(toList_length ▸ h) = t.get i h := by
  induction t generalizing i <;> simp only [toList, get, List.getElem_append, toList_length]
  case e => contradiction
  case f => cases Nat.lt_one_iff.mp h; simp
  case ff m n l r ihl ihr =>
    by_cases hi : i < m <;> simp only [hi, ihl, ↓reduceDIte]
    case neg => exact ihr (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h)
  case fp m n l r ihl ihr =>
    by_cases hi : i < m <;> simp only [hi, ihl, ↓reduceDIte]
    case neg => exact ihr (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h)
  case fe m l r ihl ihr => rw [ihl]
  case pe m l r ihl ihr => rw [ihl]
  case ee => contradiction

theorem toList_fapp {α : Type u} {m n : Nat} {s : CBStatus} {l : CBTreeList α m .f} {r : CBTreeList α n s} :
  (l.fapp r).snd.toList = l.toList ++ r.toList := by
  cases s <;> simp only [fapp, toList]
  case e => cases r <;> simp [toList]

theorem toList_appe {α : Type u} {m : Nat} {s : CBStatus} {l : CBTreeList α m s} {r : CBTreeList α 0 .e}:
  (l.appe r).snd.toList = l.toList := by
  cases s <;> simp only [appe, toList]
  case e => cases l <;> simp [toList]

theorem toList_prune_ind {α : Type u} {m : Nat} {s : CBStatus} {t : CBTreeList α m s} (hs : s = .p) :
  (hs ▸ t).prune.toList = t.toList := by
  induction t <;> try contradiction
  case fp l r hl hr => simp [toList, prune, hr]
  case fe => simp [toList, prune]
  case pe l r hl hr => simp [toList, prune, hl]

theorem toList_prune {α : Type u} {m : Nat} {t : CBTreeList α m .p} :
  t.prune.toList = t.toList := toList_prune_ind rfl

theorem toList_append {α : Type u} {m n : Nat} {s₁ s₂ : CBStatus} {t₁ : CBTreeList α m s₁} {t₂ : CBTreeList α n s₂} :
  (t₁.append t₂).snd.toList = t₁.toList ++ t₂.toList := by
  cases s₁ <;> simp only [append]
  case f => simp [toList_fapp]
  case p => simp [toList_fapp, toList_prune]
  case e =>
    cases t₁ <;> simp [toList] <;> congr <;>
      first | apply Nat.zero_add | apply eqRec_heq

theorem toListRev_eq_reverse_toList {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} :
  t.toListRev = t.toList.reverse := by
  induction t <;> simp [toList, toListRev, *]

theorem toListRev_length {α : Type u} {n : Nat} {s : CBStatus} {t : CBTreeList α n s} :
  t.toListRev.length = n := by
  rw [toListRev_eq_reverse_toList, List.length_reverse, toList_length]

end CBTreeList

structure TreeList (α : Type u) where
  length : Nat
  status : CBStatus
  data : CBTreeList α length status

namespace TreeList

def empty {α : Type u} : TreeList α := ⟨0, .e, .e⟩

def push {α : Type u} (xs : TreeList α) (x : α) : TreeList α :=
  match CBTreeList.push xs.data x with
  | ⟨s', o⟩ => ⟨xs.length + 1, s', o⟩

theorem length_push {α : Type u} (xs : TreeList α) (x : α) : (xs.push x).length = xs.length + 1 := rfl

def getInternal {α : Type u} (t : TreeList α) (i : Nat) (h : i < t.length) :=
  t.data.get i h

def get!Internal {α : Type u} [Inhabited α] (t : TreeList α) (i : Nat) : α :=
  if h : i < t.length then t.data.get i h else default

instance {α : Type u} : GetElem (TreeList α) Nat α fun xs i => i < xs.length where
  getElem t i h := t.getInternal i h

instance {α : Type u} : GetElem? (TreeList α) Nat α fun xs i => i < xs.length where
  getElem? t i := decidableGetElem? t i
  getElem! t i := t.get!Internal i

@[grind =] theorem getElem_push {α : Type u} {xs : TreeList α} {x : α} {i : Nat} (h : i < (xs.push x).length) :
  (xs.push x)[i] = if h : i < xs.length then xs[i] else x := CBTreeList.get_push h

instance {α : Type u} : LawfulGetElem (TreeList α) Nat α fun xs i => i < xs.length where
  getElem?_def xs i h := by
    simp only [getElem?, decidableGetElem?]
    split <;> rfl
  getElem!_def xs i := by
    simp only [getElem!, getElem?, decidableGetElem?, get!Internal]
    split <;> rfl

def append {α : Type u} (xs ys : TreeList α) : TreeList α :=
  match CBTreeList.append xs.data ys.data with
  | ⟨s', o⟩ => ⟨xs.length + ys.length, s', o⟩

theorem length_append {α : Type u} (xs ys : TreeList α) : (xs.append ys).length = xs.length + ys.length := rfl

def getElem_append {α : Type u} {xs ys : TreeList α} {i : Nat} (h : i < (xs.append ys).length) :
  (xs.append ys)[i] = if hi : i < xs.length then xs[i] else ys[i - xs.length]'((Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) h)) :=
  CBTreeList.get_append _

def toList {α : Type u} (xs : TreeList α) : List α := xs.data.toList

theorem length_toList {α : Type u} {xs : TreeList α} : xs.toList.length = xs.length := CBTreeList.toList_length

theorem getElem_eq_getElem_toList {α : Type u} {xs : TreeList α} {i : Nat} (h : i < xs.length) :
  xs.toList[i]'(length_toList ▸ h) = xs[i] := CBTreeList.toList_get _

end TreeList

end Auto
