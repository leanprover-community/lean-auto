/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Auto.MathlibEmulator.DeriveToExpr

/-! # `ToExpr` instances for Auto

This module should be imported by any module that intends to define `ToExpr` instances.
It provides necessary dependencies (the `Lean.ToLevel` class) and it also overrides the instances
that come from core Lean 4 that do not handle universe polymorphism.
(See the module `Lean.ToExpr` for the instances that are overridden.)

In addition, we provide some additional `ToExpr` instances for core definitions.
-/

set_option autoImplicit true

section override
namespace Auto

attribute [-instance] Lean.instToExprOptionOfToLevel

deriving instance Lean.ToExpr for Option

attribute [-instance] Lean.instToExprListOfToLevel

deriving instance Lean.ToExpr for List

attribute [-instance] Lean.instToExprArrayOfToLevel

instance {α : Type u} [Lean.ToExpr α] [ToLevel.{u}] : Lean.ToExpr (Array α) :=
  let type := Lean.toTypeExpr α
  { toExpr     := fun as => Lean.mkApp2 (Lean.mkConst ``List.toArray [toLevel.{u}]) type (Lean.toExpr as.toList)
    toTypeExpr := Lean.mkApp (Lean.mkConst ``Array [toLevel.{u}]) type }

attribute [-instance] Lean.instToExprProdOfToLevel

deriving instance Lean.ToExpr for Prod

deriving instance Lean.ToExpr for System.FilePath

end Auto
end override

namespace Auto
open Lean

deriving instance ToExpr for Int

deriving instance ToExpr for ULift

/-- Hand-written instance since `PUnit` is a `Sort` rather than a `Type`. -/
instance [ToLevel.{u}] : ToExpr PUnit.{u+1} where
  toExpr _ := mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExpr := mkConst ``PUnit [toLevel.{u+1}]

deriving instance ToExpr for String.Pos
deriving instance ToExpr for Substring
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax.Preresolved
deriving instance ToExpr for Syntax

open DataValue in
/-- Core of a hand-written `ToExpr` handler for `MData`.
Uses the `KVMap.set*` functions rather than going into the internals
of the `KVMap` data structure. -/
private def toExprMData (md : MData) : Expr := Id.run do
  let mut e := mkConst ``MData.empty
  for (k, v) in md do
    let k := toExpr k
    e := match v with
          | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (mkStrLit v)
          | ofBool v   => mkApp3 (mkConst ``KVMap.setBool) e k (toExpr v)
          | ofName v   => mkApp3 (mkConst ``KVMap.setName) e k (toExpr v)
          | ofNat v    => mkApp3 (mkConst ``KVMap.setNat) e k (mkNatLit v)
          | ofInt v    => mkApp3 (mkConst ``KVMap.setInt) e k (toExpr v)
          | ofSyntax v => mkApp3 (mkConst ``KVMap.setSyntax) e k (toExpr v)
  return e

instance : ToExpr MData where
  toExpr := toExprMData
  toTypeExpr := mkConst ``MData

deriving instance ToExpr for FVarId
deriving instance ToExpr for MVarId
deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for Literal
deriving instance ToExpr for Expr

end Auto
