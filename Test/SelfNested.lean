inductive MyListPre (α : Type u) : Nat → Type u
  | nil {α} (n : Nat) : MyListPre α n
  | consZero {α} (x : α) : MyListPre α 1 → MyListPre α 0
  | consSucc {α} {n : Nat} : MyListPre α n → MyListPre α (n + 2) → MyListPre α (n + 1)

def MyListPre.join {α : Type u} : MyListPre (MyListPre α n) m → MyListPre α (n + m + 1)
| .nil k => .nil (n + k + 1)
| .consZero x xs => .consSucc x (join (n := n) xs)
| .consSucc x xs => .consSucc (join x) (join (n := n) xs)

def MyListPre.splitAux {α : Type u} : (m : Nat) → MyListPre α k → k = n + m + 1 → MyListPre (MyListPre α n) m
| m, .nil _, _ => .nil m
| _, .consZero _ _, h => nomatch h
| 0, .consSucc x xs, rfl => .consZero x (splitAux 1 xs rfl)
| m + 1, .consSucc x xs, rfl => .consSucc (splitAux m x rfl) (splitAux (m + 2) xs rfl)

def MyListPre.split {α : Type u} : MyListPre α (n + m + 1) → MyListPre (MyListPre α n) m :=
  (splitAux m · rfl)

theorem MyListPre.split_join {α : Type u} : (t : MyListPre (MyListPre α n) m) → t.join.split = t
| .nil _ => rfl
| .consZero x xs => by
  show MyListPre.consZero x xs.join.split = _
  rw [split_join xs]
| .consSucc x xs => by
  show MyListPre.consSucc x.join.split xs.join.split = _
  rw [split_join x, split_join xs]

theorem MyListPre.join_splitAux {α : Type u} :
  (m : Nat) → (t : MyListPre α k) → (h : k = n + m + 1) → (splitAux m t h).join = h ▸ t
| _, .nil _, h => by subst h; rfl
| _, .consZero _ _, h => nomatch h
| 0, .consSucc x xs, rfl => by
  show MyListPre.consSucc x (splitAux 1 xs rfl).join = _
  rw [join_splitAux 1 xs rfl]
| m + 1, .consSucc x xs, rfl => by
  show MyListPre.consSucc (splitAux m x rfl).join (splitAux (m + 2) xs rfl).join = _
  rw [join_splitAux m x rfl, join_splitAux (m + 2) xs rfl]

theorem MyListPre.join_split {α : Type u} (t : MyListPre α (n + m + 1)) : t.split.join = t :=
  join_splitAux m t rfl

def MyList (α : Type u) := MyListPre α 0

def MyList.nil (α : Type u) : MyList α := MyListPre.nil (α := α) 0

def MyList.cons {α : Type u} (x : α) (xs : MyList (MyList α)) : MyList α :=
  .consZero x (MyListPre.join xs)

def MyList.split {α : Type u} {n : Nat} (xs : MyListPre α (n + 1)) : MyList (MyListPre α n) :=
  MyListPre.split xs

/-- `MyList` iterated `a` times over `α` -/
def MyList.iter (α : Type u) : Nat → Type u
| 0 => α
| a + 1 => MyList (iter α a)

/-- A list of level `a` as a `MyList` over `MyList.iter α a`. Lists of level `0` are unchanged -/
def MyListPre.conv {α : Type u} : {a : Nat} → MyListPre α a → MyList (MyList.iter α a)
| _, .nil _ => MyList.nil _
| _, .consZero x xs => MyListPre.consZero x xs
| _, .consSucc x xs => MyList.cons x.conv xs.conv

def MyListPre.deepJoinAux {α β : Type u} (a : Nat) (h : β → MyListPre α (a + 1) → MyListPre α a) :
  MyListPre β m → MyListPre α (a + m)
| .nil _ => .nil _
| .consZero x xs => h x (deepJoinAux a h xs)
| .consSucc x xs => .consSucc (deepJoinAux a h x) (deepJoinAux a h xs)

/-- The inverse of `MyListPre.conv` (see `MyListPre.deepJoin_conv`) -/
def MyListPre.deepJoin {α : Type u} : (a : Nat) → {m : Nat} → MyListPre (MyList.iter α a) m → MyListPre α (a + m)
| 0 => deepJoinAux 0 MyListPre.consZero
| a + 1 => deepJoinAux (a + 1) fun x r => .consSucc (deepJoin a x) r

theorem MyListPre.heq_nil {α : Type u} {k k' : Nat} (h : k = k') :
  HEq (MyListPre.nil (α := α) k) (MyListPre.nil (α := α) k') := by subst h; rfl

theorem MyListPre.heq_consSucc {α : Type u} {k k' : Nat} (h : k = k')
  {x : MyListPre α k} {x' : MyListPre α k'} {xs : MyListPre α (k + 2)} {xs' : MyListPre α (k' + 2)}
  (hx : HEq x x') (hxs : HEq xs xs') : HEq (MyListPre.consSucc x xs) (MyListPre.consSucc x' xs') := by
  subst h; cases hx; cases hxs; rfl

theorem MyListPre.deepJoinAux_zero {α : Type u} : (x : MyListPre α m) → HEq (deepJoinAux 0 MyListPre.consZero x) x
| .nil _ => heq_nil (Nat.zero_add _)
| .consZero x xs => heq_of_eq (congrArg (MyListPre.consZero x) (eq_of_heq (deepJoinAux_zero xs)))
| .consSucc x xs => heq_consSucc (Nat.zero_add _) (deepJoinAux_zero x) (deepJoinAux_zero xs)

theorem MyListPre.deepJoinAux_join {α β : Type u} (a : Nat) (h : β → MyListPre α (a + 1) → MyListPre α a) :
  (z : MyListPre (MyList β) m) → HEq (deepJoinAux a h (MyListPre.join (n := 0) z))
    (deepJoinAux (a + 1) (fun x r => .consSucc (deepJoinAux a h x) r) z)
| .nil _ => heq_nil (by omega)
| .consZero x xs => heq_of_eq (congrArg (MyListPre.consSucc _) (eq_of_heq (deepJoinAux_join a h xs)))
| .consSucc x xs => heq_consSucc (by simp only [Nat.add_eq]; omega) (deepJoinAux_join a h x) (deepJoinAux_join a h xs)

theorem MyListPre.deepJoin_conv {α : Type u} : {a : Nat} → (t : MyListPre α a) → deepJoin a t.conv = t
| a, .nil _ => by cases a <;> rfl
| _, .consZero x xs => congrArg (MyListPre.consZero x) (eq_of_heq (deepJoinAux_zero xs))
| _, .consSucc (n := k) x xs => by
  have hxs : deepJoinAux (k + 1) (fun y r => .consSucc (deepJoin k y) r)
      (MyListPre.join (n := 0) (m := 0) xs.conv) = xs :=
    (eq_of_heq (deepJoinAux_join (k + 1) _ xs.conv)).trans (deepJoin_conv xs)
  show MyListPre.consSucc (deepJoin k x.conv) (deepJoinAux (k + 1) (fun y r => .consSucc (deepJoin k y) r)
    (MyListPre.join (n := 0) (m := 0) xs.conv)) = _
  rw [deepJoin_conv x, hxs]

theorem MyListPre.join_conv {α : Type u} (xs : MyListPre α 1) : MyListPre.join (n := 0) (m := 0) xs.conv = xs :=
  eq_of_heq (((deepJoinAux_zero _).symm.trans (deepJoinAux_join 0 MyListPre.consZero xs.conv)).trans
    (heq_of_eq (deepJoin_conv xs)))

def MyList.recMotive (β : Sort v) (motive : ∀ (α : Type u), MyList α → β)
  (α : Type u) (a : Nat) (x : MyListPre α a) : β :=
  match a with
  | 0 => motive α x
  | n + 1 => motive (MyList.iter α (n + 1)) x.conv

noncomputable def MyList.rec {motive : ∀ (α : Type u), MyList α → Sort v}
  (nil : ∀ α, motive α (.nil _))
  (cons : ∀ (α) (head : α) (tail : MyList (MyList α)), motive _ tail → motive _ (MyList.cons head tail))
  (α) : (t : MyList α) → motive α t :=
  @MyListPre.rec α (MyList.recMotive _ motive α)
    (fun n =>
      match n with
      | 0 => nil _
      | _ + 1 => nil _)
    (fun (x : α) (xs : MyListPre α 1) ih =>
      MyListPre.join_conv xs ▸ cons α x xs.conv ih)
    (fun {n : Nat} (x : MyListPre α n) (xs : MyListPre α (n + 2)) _ ihxs =>
      cons (MyList.iter α (n + 1)) x.conv xs.conv ihxs)
    _
