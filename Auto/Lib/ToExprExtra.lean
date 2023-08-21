import Lean
open Lean

namespace Auto

class ToSortLevel.{u} where
  dummy : Type u := Sort u
  toSortLevel : Level

instance : ToSortLevel.{0} where
  toSortLevel := .zero

instance : ToSortLevel.{1} where
  toSortLevel := .succ .zero

instance : ToSortLevel.{2} where
  toSortLevel := .succ (.succ .zero)

attribute [-instance] Lean.instToExprNat
instance : ToExpr Nat where
  toExpr := fun n => .lit (.natVal n)
  toTypeExpr := .const ``Nat []

attribute [-instance] Lean.instToExprOption
instance {α : Type u} [ToSortLevel.{u}] [ToExpr α] : ToExpr (Option α) :=
  let type := toTypeExpr α
  let lvl := ToSortLevel.toSortLevel.{u}
  { toExpr     := fun o => match o with
      | none   => mkApp (mkConst ``Option.none [lvl]) type
      | some a => mkApp2 (mkConst ``Option.some [lvl]) type (toExpr a),
    toTypeExpr := mkApp (mkConst ``Option [lvl]) type }

private def List.toExprAux [ToExpr α] (nilFn : Expr) (consFn : Expr) : List α → Expr
  | []    => nilFn
  | a::as => mkApp2 consFn (toExpr a) (toExprAux nilFn consFn as)

attribute [-instance] Lean.instToExprList
instance {α : Type u} [ToSortLevel.{u}] [ToExpr α] : ToExpr (List α) :=
  let type := toTypeExpr α
  let lvl := ToSortLevel.toSortLevel.{u}
  let nil  := mkApp (mkConst ``List.nil [lvl]) type
  let cons := mkApp (mkConst ``List.cons [lvl]) type
  { toExpr     := List.toExprAux nil cons,
    toTypeExpr := mkApp (mkConst ``List [lvl]) type }

attribute [-instance] Lean.instToExprArray
instance {α : Type u} [ToSortLevel.{u}] [ToExpr α] : ToExpr (Array α) :=
  let type := toTypeExpr α
  let lvl := ToSortLevel.toSortLevel.{u}
  { toExpr     := fun as => mkApp2 (mkConst ``Array.mk [lvl]) type (toExpr as.toList),
    toTypeExpr := mkApp (mkConst ``Array [lvl]) type }

end Auto