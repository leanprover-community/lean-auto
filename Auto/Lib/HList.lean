module

public import Auto.Lib.HEqExtra
public import Auto.Lib.IsomType

@[expose] public section

namespace Auto

inductive HList (β : α → Sort _) : List α → Sort _
  | nil  : HList β .nil
  | cons : (x : β ty) → HList β tys → HList β (ty :: tys)

@[irreducible] def HList.nil_IsomType
  {α : Type u} {β : α → Sort v} : IsomType (HList β .nil) PUnit :=
  ⟨fun _ => .unit, fun _ => .nil,
   fun x => match x with | .nil => rfl, fun _ => rfl⟩

@[irreducible] def HList.cons_IsomType
  {α : Type u} {β : α → Type v} {a : α} {as : List α} :
  IsomType (HList β (a :: as)) (β a × HList β as) :=
  ⟨fun xs => match xs with | .cons x xs => (x, xs), fun (x, xs) => .cons x xs,
   fun xs => match xs with | .cons _ _ => rfl,
   fun (_, _) => rfl⟩

@[irreducible] def HList.singleton_IsomType
  {α : Type u_1} {β : α → Sort u_2} {a : α} : IsomType (HList β [a]) (β a) :=
  ⟨fun xs => match xs with | .cons x .nil => x,
   fun x => .cons x .nil,
   fun xs => match xs with | .cons _ .nil => rfl,
   fun _ => rfl⟩

def HList.getD {β : α → Sort _} {ty : α} (default : β ty) :
  {tys : List α} → HList β tys → (n : Nat) → β (tys.getD n ty)
  | .nil, .nil,       _       => default
  | .(_), .cons a _,  0       => a
  | .(_), .cons _ as, .succ n => HList.getD default as n

theorem HList.getD_heq
  {β₁ : α₁ → Sort _} {ty₁ : α₁} {default₁ : β₁ ty₁} {tys₁ : List α₁} {hl₁ : HList β₁ tys₁} {n₁ : Nat}
  {β₂ : α₂ → Sort _} {ty₂ : α₂} {default₂ : β₂ ty₂} {tys₂ : List α₂} {hl₂ : HList β₂ tys₂} {n₂ : Nat}
  (hβ : HEq β₁ β₂) (hty : HEq ty₁ ty₂) (hdefault : HEq default₁ default₂)
  (htys : HEq tys₁ tys₂) (hhl : HEq hl₁ hl₂) (hn : n₁ = n₂) :
  HEq (HList.getD default₁ hl₁ n₁) (HList.getD default₂ hl₂ n₂) := by
  cases hty; cases hβ; cases hdefault; cases htys; cases hhl; cases hn; apply HEq.rfl

def HList.ofMapTy {γ : β → Sort _} (f : α → β) :
  {tys : List α} → HList γ (List.map f tys) → HList (γ ∘ f) tys
  | .nil,      .nil       => .nil
  | .cons _ _, .cons x xs => .cons x (ofMapTy f xs)

def HList.toMapTy {γ : β → Sort _} (f : α → β) :
  {tys : List α} → HList (γ ∘ f) tys → HList γ (List.map f tys)
  | .nil,      .nil       => .nil
  | .cons _ _, .cons x xs => .cons x (toMapTy f xs)

def HList.ofMapList {β : α → Sort _} (f : ∀ (x : α), β x) : (xs : List α) →  HList β xs
  | .nil => .nil
  | .cons x xs => .cons (f x) (ofMapList f xs)

def HList.map {β : α → Sort _} {γ : α → Sort _} (f : ∀ (a : α), β a → γ a) :
  {tys : List α} → (xs : HList β tys) → HList γ tys
  | .nil,      .nil       => .nil
  | .cons _ _, .cons x xs => .cons (f _ x) (map f xs)

def HList.append : (xs : HList β as) → (ys : HList β bs) → HList β (as ++ bs)
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

theorem HList.append_assoc (xs : HList β as) (ys : HList β bs) (zs : HList β cs) :
  HEq (append (append xs ys) zs) (append xs (append ys zs)) := by
  induction xs
  case nil => apply HEq.rfl
  case cons a as x xs IH =>
    dsimp [append];
    apply congr_h_heq
    case Hβ => rw [List.append_assoc]
    case h₁ =>
      apply congr_h_heq;
      case Hβ => rw [List.append_assoc]
      case h₁ =>
        apply congr_hd_heq <;> try apply HEq.rfl;
        rw [List.append_assoc]
      case h₂ => apply HEq.rfl
    case h₂ => exact IH

theorem HList.getD_append_left (xs : HList β as) (ys : HList β bs) (h : i < as.length) :
  HEq ((append xs ys).getD df i) (xs.getD df i) := by
  induction xs generalizing i bs
  case nil => contradiction
  case cons a as x xs IH =>
    dsimp [append]; cases i
    case zero => apply HEq.rfl
    case succ i =>
      dsimp [getD]; apply IH; apply Nat.le_of_succ_le_succ h

theorem HList.getD_append_right (xs : HList β as) (ys : HList β bs) (h : i ≥ as.length) :
  HEq ((append xs ys).getD df i) (ys.getD df (i - as.length)) := by
  induction xs generalizing i bs
  case nil => apply HEq.rfl
  case cons a as x xs IH =>
    dsimp [append]; cases i
    case zero => contradiction
    case succ i =>
      dsimp [getD]; rw [Nat.succ_sub_succ];
      apply IH; apply Nat.le_of_succ_le_succ h

def HList.append_get_left (xs : HList β (as ++ bs)) : HList β as :=
  match as, xs with
  | .nil, _ => .nil
  | .cons _ _, .cons x xs => .cons x xs.append_get_left

def HList.append_get_right (xs : HList β (as ++ bs)) : HList β bs :=
  match as, xs with
  | .nil, xs => xs
  | .cons _ _, .cons _ xs => xs.append_get_right

theorem HList.append_get_left_eq (xs : HList β as) (ys : HList β bs) :
  HList.append_get_left (xs.append ys) = xs := by
  induction xs
  case nil => rfl
  case cons x xs IH =>
    simp only [append, append_get_left]; rw [IH]

theorem HList.append_get_right_eq (xs : HList β as) (ys : HList β bs) :
  HList.append_get_right (xs.append ys) = ys := by
  induction xs
  case nil => rfl
  case cons x xs IH =>
    simp only [append, append_get_right]; rw [IH]

theorem HList.append_get_append_eq (xs : HList β (as ++ bs)) :
  HList.append xs.append_get_left xs.append_get_right = xs := by
  induction as
  case nil => rfl
  case cons a as IH =>
    cases xs; case cons x xs =>
      simp only [append_get_left, append_get_right, append]; rw [IH]

@[irreducible] def HList.append_IsomType {α : Type u} {β : α → Sort v} {xs ys : List α} :
  IsomType (HList β (xs ++ ys)) (PProd (HList β xs) (HList β ys)) :=
  ⟨fun l => ⟨l.append_get_left, l.append_get_right⟩,
   fun ⟨l₁, l₂⟩ => HList.append l₁ l₂,
   HList.append_get_append_eq,
   fun ⟨l₁, l₂⟩ => by dsimp; congr; rw [append_get_left_eq]; rw [append_get_right_eq]⟩

@[irreducible] def HList.append_singleton_IsomType {α : Type u} {β : α → Sort v} {xs : List α} {x : α} :
  IsomType (HList β (xs ++ [x])) (PProd (HList β xs) (β x)) :=
  ⟨fun l => ⟨l.append_get_left, match l.append_get_right with | .cons x .nil => x⟩,
   fun ⟨l, e⟩ => HList.append l (.cons e .nil),
   fun l => by
      dsimp; conv => enter [2]; rw [← HList.append_get_append_eq (xs:=l)]
      apply congrArg; generalize append_get_right l = l'
      match l' with
      | .cons e .nil => rfl,
   fun ⟨l, e⟩ => by simp [append_get_left_eq, append_get_right_eq]⟩

def HList.reverseAux : {as : _} → (xs : HList β as) → (ys : HList β bs) → HList β (List.reverseAux as bs)
  | .nil,       .nil,       r => r
  | .cons _ as, .cons x xs, r => reverseAux (as:=as) xs (.cons x r)

def HList.reverse (xs : HList β as) : HList β (List.reverse as) := HList.reverseAux xs .nil

theorem HList.reverse_nil : reverse (β:=β) .nil = .nil := rfl

theorem HList.reverseAux_eq_append {xs : HList β as} {ys : HList β bs} :
  HEq (reverseAux xs ys) (append (reverseAux xs .nil) ys) := by
  induction xs generalizing bs ys
  case nil => apply HEq.rfl
  case cons a as x xs IH =>
    dsimp [reverseAux]
    apply HEq.trans (@IH (a :: bs) (.cons x ys))
    apply HEq.trans (b:=append (append (reverseAux xs .nil) (cons x nil)) ys)
    case h₁ =>
      apply HEq.symm; apply HList.append_assoc
    case h₂ =>
      congr
      case e_3 =>
        rw [List.reverseAux_eq_append (bs := [a])]
      case e_5 =>
        apply HEq.symm; apply IH

theorem HList.reverse_cons {x : β a} {xs : HList β as} :
  HEq ((HList.cons x xs).reverse) (xs.reverse.append (.cons x .nil)) :=
  reverseAux_eq_append (xs:=xs) (ys:=.cons x .nil)

theorem HList.reverseAux_reverseAux (xs : HList β as) (ys : HList β bs) :
  HEq (reverseAux xs ys).reverse (reverseAux ys xs) := by
  induction xs generalizing bs ys
  case nil => apply HEq.rfl
  case cons x xs IH => exact IH (.cons x ys)

theorem HList.reverse_reverse (xs : HList β as) : HEq xs.reverse.reverse xs :=
  reverseAux_reverseAux xs .nil

theorem HList.forall_reverse {β : α → Sort _} {as : List α} {p : HList β as.reverse → Prop} :
  (∀ xs, p xs) ↔ (∀ ys : HList β as, p ys.reverse) := by
  refine ⟨fun h ys => h ys.reverse, fun h xs => ?_⟩
  have hrev : ∀ {bs} (heq : bs = as) (zs : HList β bs), HEq (heq ▸ zs).reverse zs.reverse := by
    intro _ heq _; cases heq; rfl
  have heq := (hrev (List.reverse_reverse as) xs.reverse).trans (reverse_reverse xs)
  exact (eq_of_heq heq) ▸ h _

/-- The `i`-th element of `xs` -/
def HList.get {β : α → Sort _} : {as : List α} → HList β as → (i : Fin as.length) → β as[i]
  | _ :: _, .cons x _, ⟨0, _⟩ => x
  | _ :: _, .cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The `HList` whose `i`-th element is `f i` -/
def HList.ofFn {β : α → Sort _} : {as : List α} → ((i : Fin as.length) → β as[i]) → HList β as
  | [], _ => .nil
  | _ :: _, f => .cons (f ⟨0, Nat.zero_lt_succ _⟩) (ofFn fun i => f i.succ)

theorem HList.get_ofFn {β : α → Sort _} : {as : List α} → (f : (i : Fin as.length) → β as[i]) →
  (i : Fin as.length) → (ofFn f).get i = f i
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: _, f, ⟨i + 1, h⟩ => get_ofFn (fun i => f i.succ) ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem HList.ext {β : α → Sort _} : {as : List α} → {xs ys : HList β as} → (∀ i, xs.get i = ys.get i) → xs = ys
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x xs, .cons y ys, h => by
    have h₀ : x = y := h ⟨0, Nat.zero_lt_succ _⟩
    have h₁ : xs = ys := ext fun ⟨i, hi⟩ => h ⟨i + 1, Nat.succ_lt_succ hi⟩
    rw [h₀, h₁]

theorem HList.get_map {β : α → Sort _} {γ : α → Sort _} (f : ∀ (a : α), β a → γ a) :
  {as : List α} → (xs : HList β as) → (i : Fin as.length) → (xs.map f).get i = f as[i] (xs.get i)
  | _ :: _, .cons _ _, ⟨0, _⟩ => rfl
  | _ :: _, .cons _ xs, ⟨i + 1, h⟩ => get_map f xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- `β a₁ → ⋯ → β aₙ → γ`, where `as = [a₁, ⋯, aₙ]` -/
def HList.Funcs (β : α → Type u) : List α → Type u → Type u
  | [], γ => γ
  | a :: as, γ => β a → Funcs β as γ

/-- Apply a curried function to the elements of `xs` -/
def HList.uncurry {β : α → Type u} : {as : List α} → HList.Funcs β as γ → HList β as → γ
  | [], f, .nil => f
  | _ :: _, f, .cons x xs => uncurry (f x) xs

/-- The curried form of `f` -/
def HList.curry {β : α → Type u} : {as : List α} → (HList β as → γ) → HList.Funcs β as γ
  | [], f => f .nil
  | _ :: _, f => fun x => curry fun xs => f (.cons x xs)

theorem HList.uncurry_curry {β : α → Type u} : {as : List α} → (f : HList β as → γ) → uncurry (curry f) = f
  | [], _ => funext fun .nil => rfl
  | _ :: _, f => funext fun (.cons x xs) => congrFun (uncurry_curry (fun xs => f (.cons x xs))) xs

theorem HList.curry_uncurry {β : α → Type u} : {as : List α} → (f : HList.Funcs β as γ) → curry (uncurry f) = f
  | [], _ => rfl
  | _ :: _, f => funext fun x => curry_uncurry (f x)

theorem HList.uncurry_inj {β : α → Type u} {f g : HList.Funcs β as γ} (h : uncurry f = uncurry g) : f = g := by
  rw [← curry_uncurry f, ← curry_uncurry g, h]

theorem HList.nonempty_of_forall_mem {β : α → Sort _} :
  {as : List α} → (∀ a ∈ as, Nonempty (β a)) → Nonempty (HList β as)
  | [], _ => ⟨.nil⟩
  | _ :: _, h =>
    have ⟨x⟩ := h _ List.mem_cons_self
    have ⟨xs⟩ := nonempty_of_forall_mem fun a ha => h a (List.mem_cons_of_mem _ ha)
    ⟨.cons x xs⟩

end Auto
