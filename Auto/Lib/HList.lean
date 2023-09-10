namespace Auto

inductive HList (β : α → Sort _) : List α → Sort _
  | nil  : HList β .nil
  | cons : (x : β ty) → HList β tys → HList β (ty :: tys)

def HList.getD {β : α → Sort _} {ty : α} (default : β ty) :
  {tys : List α} → HList β tys → (n : Nat) → β (tys.getD n ty)
  | .nil, .nil,       _       => default
  | .(_), .cons a _,  0       => a
  | .(_), .cons _ as, .succ n => HList.getD default as n

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

end Auto