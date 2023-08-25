import Lean
open Lean

namespace Auto

def MessageData.exprPair : Expr × Expr → MessageData
| (e1, e2) => MessageData.compose m!"({e1}, " m!"{e2})"

def MessageData.intercalate (m : MessageData) : List MessageData → MessageData
  | []      => m!""
  | a :: as => go a m as
where go (acc : MessageData) (m : MessageData) : List MessageData → MessageData
  | a :: as => go (.compose acc (.compose m a)) m as
  | []      => acc

def MessageData.list (as : List α) (f : α → MessageData) : MessageData :=
  .compose m!"[" (.compose (MessageData.intercalate m!", " (as.map f)) m!"]")

def MessageData.array (as : Array α) (f : α → MessageData) : MessageData :=
  MessageData.list as.data f

end Auto