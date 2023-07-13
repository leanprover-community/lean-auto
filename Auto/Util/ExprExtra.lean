import Lean
open Lean

namespace Auto.Util

def Expr.binders (e : Expr) : Array (Name × Expr × BinderInfo) :=
  let rec aux (e : Expr) :=
    match e with
    | .forallE n ty b bi => (n, ty, bi) :: aux b
    | _ => []
  Array.mk (aux e)

end Auto.Util