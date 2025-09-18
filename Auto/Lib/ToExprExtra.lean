import Lean
import Auto.MathlibEmulator
open Lean

namespace Auto.ToExprExtra

scoped instance : ToExpr Nat where
  toExpr := fun n => .lit (.natVal n)
  toTypeExpr := .const ``Nat []

scoped instance : ToExpr Int where
  toExpr := fun n =>
    match n with
    | .ofNat n => .app (.const ``Int.ofNat []) (.lit (.natVal n))
    | .negSucc n => .app (.const ``Int.negSucc []) (.lit (.natVal n))
  toTypeExpr := .const ``Int []

/--
  Used when the elements of a container are already expressions
  For example, consider the ordinary
    `l₁ := toExpr (a : List Nat)`
    `l₂ := (a : List Nat).map toExpr`
  We require that `toExpr (self:=instExprToExprId (.const ``Nat [])) l₂ ≝ l₁`
  It is obvious that this shouldn't be marked as an `instance`
-/
def instExprToExprId (ty : Expr) : ToExpr Expr :=
  { toExpr := id, toTypeExpr := ty}

end Auto.ToExprExtra
