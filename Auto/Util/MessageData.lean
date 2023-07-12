import Lean
open Lean

namespace Auto

def ExprPairToMessageData : Expr × Expr → MessageData
| (e1, e2) => MessageData.compose m!"({e1}, " m!"{e2})"

def ListToMessageData (as : List α) (f : α → MessageData) : MessageData :=
  .compose m!"[" (.compose (go as) m!"]")
  where go as :=
    match as with
    | .nil => m!""
    | .cons a .nil => f a
    | .cons a as@(.cons _ _) => .compose (f a) (.compose ", " (go as))

def ArrayToMessageData (as : Array α) (f : α → MessageData) : MessageData :=
  ListToMessageData as.data f

end Auto