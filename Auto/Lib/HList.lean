import Auto.Lib.HEqExtra

namespace Auto

inductive HList (β : α → Sort _) : List α → Sort _
  | nil  : HList β .nil
  | cons : (x : β ty) → HList β tys → HList β (ty :: tys)

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
        rw [List.append_assoc]; apply HEq.rfl
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

def HList.reverseAux : {as : _} → (xs : HList β as) → (ys : HList β bs) → HList β (List.reverseAux as bs)
  | .nil,       .nil,       r => r
  | .cons _ as, .cons x xs, r => reverseAux (as:=as) xs (.cons x r)

def HList.reverse (xs : HList β as) : HList β (List.reverse as) := HList.reverseAux xs .nil

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
      case e_3.h =>
        dsimp [List.reverseAux]; rw [List.reverseAux_eq_append _ [a]]
      case e_5 =>
        apply HEq.symm; apply IH

end Auto