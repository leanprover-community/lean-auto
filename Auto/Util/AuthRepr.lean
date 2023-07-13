import Lean
open Lean

namespace Auto

-- Lean's "repr" does not deal with LevelMVarId correctly
partial def levelAuthRepr (l : Level) : String :=
  match l with
  | .zero => "Level.zero"
  | .succ l' => "Level.succ (" ++ levelAuthRepr l' ++ ")"
  | .max l1 l2 => "Level.max (" ++ levelAuthRepr l1 ++ ") (" ++ levelAuthRepr l2 ++ ")"
  | .imax l1 l2 => "Level.imax (" ++ levelAuthRepr l1 ++ ") (" ++ levelAuthRepr l2 ++ ")"
  | .param n => "Level.param `" ++ n.toString
  | .mvar id => "Level.mvar (LevelMVarId.mk `" ++ id.name.toString ++ ")"

-- Lean's "repr" does not deal with LevelMVarId correctly
partial def exprAuthRepr (e : Expr) : String :=
  match e with
  | Expr.forallE _ d b _ => "Expr.forallE `_ (" ++ exprAuthRepr d ++ ") (" ++ exprAuthRepr b ++ ") BinderInfo.default"
  | Expr.lam _ d b _ => "Expr.lam `_ (" ++ exprAuthRepr d ++ ") (" ++ exprAuthRepr b ++ ") BinderInfo.default"
  | Expr.mdata _ b => exprAuthRepr b
  | Expr.letE _ t v b _ => "Expr.letE `_ (" ++ exprAuthRepr t ++ ") (" ++ exprAuthRepr v ++ ") ("  ++ exprAuthRepr b ++ ") BinderInfo.default"
  | Expr.app f a => "Expr.app (" ++ exprAuthRepr f ++ ") (" ++ exprAuthRepr a ++ ")"
  | Expr.proj name idx b => "Expr.proj `" ++ name.toString ++ " " ++ idx.repr ++ " (" ++ exprAuthRepr b ++ ")"
  | Expr.const name us => "Expr.const `" ++ name.toString ++ " [" ++ String.intercalate ", " (us.map levelAuthRepr) ++ "]"
  | Expr.lit l =>
    match l with
    | .natVal l => "Expr.lit (Literal.natVal " ++ l.repr ++ ")"
    | .strVal s => "Expr.lit (Literal.strVal " ++ "\"" ++ s ++ "\"" ++ ")"
  | Expr.sort l => "Expr.sort (" ++ levelAuthRepr l ++ ")"
  | Expr.mvar id => "Expr.mvar (Lean.MVarId.mk " ++ id.name.toString ++ ")"
  | Expr.fvar id => "Expr.fvar (Lean.FVarId.mk " ++ id.name.toString ++ ")"
  | Expr.bvar n => "Expr.bvar " ++ n.repr

end Auto