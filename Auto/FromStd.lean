
namespace List

theorem getD_eq_get? : ∀ l n (a : α), getD l n a = (get? l n).getD a
  | [], _, _ => rfl
  | _a::_, 0, _ => rfl
  | _::l, _+1, _ => getD_eq_get? (l := l) ..

theorem get?_append_right : ∀ {l₁ l₂ : List α} {n : Nat}, l₁.length ≤ n →
  (l₁ ++ l₂).get? n = l₂.get? (n - l₁.length)
| [], _, n, _ => rfl
| a :: l, _, n+1, h₁ => by rw [cons_append]; simp [get?_append_right (Nat.lt_succ.1 h₁)]

theorem get?_reverse' : ∀ {l : List α} (i j), i + j + 1 = length l →
    get? l.reverse i = get? l j
  | [], _, _, _ => rfl
  | a::l, i, 0, h => by simp at h; simp [h, get?_append_right]
  | a::l, i, j+1, h => by
    have := Nat.succ.inj h; simp at this ⊢
    rw [get?_append, get?_reverse' _ j this]
    rw [length_reverse, ← this]; apply Nat.lt_add_of_pos_right (Nat.succ_pos _)

theorem get?_reverse {l : List α} (i) (h : i < length l) :
    get? l.reverse i = get? l (l.length - 1 - i) :=
  get?_reverse' _ _ <| by
    rw [Nat.add_sub_of_le (Nat.le_sub_one_of_lt h),
      Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) h)]

end List
