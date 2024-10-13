import Auto.Lib.IsomType

namespace Auto

/--
  This function is slow and is not meant to be used in computation
  It's main use is in the pushs_pops theorems
-/
def List.ofFun (f : Nat → α) (n : Nat) : List α :=
  match n with
  | 0 => .nil
  | .succ n' => f 0 :: ofFun (fun n => f (.succ n)) n'

theorem List.ofFun_length (f : Nat → α) (n : Nat) :
  (List.ofFun f n).length = n := by
  induction n generalizing f
  case zero => rfl
  case succ n IH => dsimp [ofFun]; rw [IH]

theorem List.ofFun_get?_eq_some (f : Nat → α) (n m : Nat) (h : n > m) :
  (List.ofFun f n).get? m = .some (f m) := by
  induction m generalizing f n
  case zero =>
    cases n
    case zero => cases h
    case succ n => rfl
  case succ m IH =>
    cases n
    case zero => cases h
    case succ n =>
      let h' := Nat.le_of_succ_le_succ h
      dsimp [ofFun, List.get?]; rw [IH (fun n => f (.succ n)) _ h']

theorem List.beq_def [BEq α] {x y : List α} : (x == y) = x.beq y := rfl

theorem List.beq_refl [BEq α] (H : ∀ (x : α), (x == x) = true) :
  {l : List α} → (l == l) = true
| .nil => rfl
| .cons x xs => by
  rw [List.beq_def]; dsimp [List.beq]; rw [Bool.and_eq_true];
  exact And.intro (H x) (List.beq_refl H)

theorem List.eq_of_beq_eq_true [BEq α] (H : ∀ (x y : α), (x == y) = true → x = y) :
  {l₁ l₂ : List α} → l₁ == l₂ → l₁ = l₂
| .nil,       .nil       => fun _ => rfl
| .nil,       .cons _ _  => fun h => by cases h
| .cons _ _,  .nil       => fun h => by cases h
| .cons u us, .cons v vs => fun h => by
  rw [List.beq_def] at h; dsimp [List.beq] at h; rw [Bool.and_eq_true] at h
  have ⟨hHead, hTail⟩ := h
  exact congr (congrArg _ (H _ _ hHead)) (List.eq_of_beq_eq_true H hTail)

section

  variable (l : List α) (x : α) (xs : List α) (d : α)

  @[simp]
  theorem List.getD_cons_zero : List.getD (x :: xs) 0 d = x :=
    rfl

  @[simp]
  theorem List.getD_cons_succ : List.getD (x :: xs) (n + 1) d = List.getD xs n d :=
    rfl

  theorem List.getD_eq_get {n : Nat} (hn : n < l.length) : l.getD n d = l.get ⟨n, hn⟩ := by
    induction l generalizing n
    case nil => cases hn
    case cons head tail IH =>
      cases n
      case zero => rfl
      case succ n => apply IH

end

@[simp]
def List.split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)

theorem List.split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) :
    split (a :: l) = (a :: l₂, l₁) := by rw [split, h]

theorem List.length_split_le :
    ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → List.length l₁ ≤ List.length l ∧ List.length l₂ ≤ List.length l
  | [], _, _, rfl => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | a :: l, l₁', l₂', h => by
    cases e : split l
    case mk l₁ l₂ =>
      injection (split_cons_of_eq _ e).symm.trans h; subst l₁' l₂'
      cases length_split_le e
      case intro h₁ h₂ =>
        exact ⟨Nat.succ_le_succ h₂, Nat.le_succ_of_le h₁⟩

theorem List.length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    List.length l₁ < List.length (a :: b :: l) ∧ List.length l₂ < List.length (a :: b :: l) := by
  cases e : split l
  case mk l₁' l₂' =>
    injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h; subst l₁ l₂
    cases length_split_le e
    case intro h₁ h₂ =>
      exact ⟨Nat.succ_le_succ (Nat.succ_le_succ h₁), Nat.succ_le_succ (Nat.succ_le_succ h₂)⟩

def List.merge (r : α → α → Prop) [DecidableRel r] : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if r a b then a :: merge r l (b :: l') else b :: merge r (a :: l) l'
  termination_by l₁ l₂ => List.length l₁ + List.length l₂

def List.mergeSort (r : α → α → Prop) [DecidableRel r]  : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    let ls := split (a :: b :: l)
    have e : split (a :: b :: l) = ⟨ls.1, ls.2⟩ := rfl
    have h := length_split_lt e
    have : (split l).fst.length < l.length + 1 := Nat.lt_of_succ_lt_succ h.1
    have : (split l).snd.length < l.length + 1 := Nat.lt_of_succ_lt_succ h.2
    exact merge r (mergeSort r ls.1) (mergeSort r ls.2)
  termination_by l => List.length l

theorem List.map_equiv (f₁ f₂ : α → β) (hequiv : ∀ x, f₁ x = f₂ x) : List.map f₁ xs = List.map f₂ xs := by
  induction xs
  case nil => rfl
  case cons head tail IH =>
    dsimp [List.map]; rw [hequiv, IH]

theorem List.length_reverseAux (l₁ l₂ : List α) : (l₁.reverseAux l₂).length = l₁.length + l₂.length := by
  rw [List.reverseAux_eq]; rw [List.length_append]; rw [List.length_reverse]

def List.reverse_IsomType : IsomType (List α) (List α) :=
  ⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩

end Auto
