import Lean
open Lean

namespace Auto

attribute [-instance] Lean.instToExprNat
instance : ToExpr Nat where
  toExpr := fun n => .lit (.natVal n)
  toTypeExpr := .const ``Nat []

-- Used when the elements of a container are already expressions
-- For example, consider the ordinary
--   `l₁ := toExpr (a : List Nat)`
--   `l₂ := (a : List Nat).map toExpr`
-- We require that `toExpr (self:=instExprToExprId (.const ``Nat [])) l₂ ≝ l₁`
-- It is obvious that this shouldn't be marked as an `instance`
def instExprToExprId (ty : Expr) : ToExpr Expr :=
  { toExpr := id, toTypeExpr := ty}

end Auto