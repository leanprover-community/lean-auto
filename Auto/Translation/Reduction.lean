import Lean
import Auto.Lib.ExprExtra
open Lean Meta

private instance : ToString TransparencyMode where
  toString : TransparencyMode → String
  | .all       => "all"
  | .default   => "default"
  | .reducible => "reducible"
  | .instances => "instances"

private instance : Lean.KVMap.Value TransparencyMode where
  toDataValue t := toString t
  ofDataValue?
  | "all"       => some .all
  | "default"   => some .default
  | "reducible" => some .reducible
  | "instances" => some .instances
  | _           => none

register_option auto.redMode : TransparencyMode := {
  defValue := .reducible
  descr := "TransparencyMode used when reducing collected facts"
}

namespace Auto

def unfoldProj (e : Expr) : MetaM Expr :=
  match e with
  | .proj name idx struct => do
    let some (.inductInfo indi) := (← getEnv).find? name
      | throwError s!"unfoldProj :: {name} is not a inductive type"
    let some structInfo := getStructureInfo? (← getEnv) name
      | throwError s!"unfoldProj :: {name} is not a structure"
    let nameMap : HashMap Name StructureFieldInfo := HashMap.ofList
      (structInfo.fieldInfo.map (fun sfi => (sfi.fieldName, sfi))).data
    let sorted := structInfo.fieldNames.map (fun name => nameMap.find? name)
    let .some (.some sfi) := sorted[idx]?
      | throwError s!"unfoldProj :: Projection index out of bound"
    let nones : List (Option Expr) := (List.range indi.numParams).map (fun _ => .none)
    Meta.mkAppOptM sfi.projFn ((Array.mk nones).push struct)
  | _ => return e

/-- This function is expensive -/
partial def prepReduceExpr (term : Expr) : MetaM Expr := do
  let red (e : Expr) : MetaM TransformStep := do
    let e := e.consumeMData
    let e ← Meta.whnf e
    return .continue e
  -- Reduce
  let trMode := auto.redMode.get (← getOptions)
  let term ← Meta.withTransparency trMode <| Meta.transform term (pre := red) (usedLetOnly := false)
  let redProj (e : Expr) : MetaM TransformStep := do
    let e ← unfoldProj e
    return .continue e
  let term ← Meta.transform term (pre := redProj)
  return term

/--
  We assume that all defeq facts have the form
    `∀ (x₁ : ⋯) ⋯ (xₙ : ⋯), c ... = ...`
  where `c` is a constant. To avoid `whnf` from reducing
  `c ⋯` (which can happen when e.g. `c` is a recursor), we
  call `forallTelescope`, then call `prepReduceExpr` on
  · All the arguments of `c`, and
  · The right-hand side of the equation
-/
def prepReduceDefeq (type : Expr) : MetaM (Option Expr) := do
  let type := Expr.eraseMData type
  Meta.forallTelescope type fun xs b => do
    let .app (.app (.app (.const ``Eq lvls) ty) lhs) rhs := b
      | return .none
    let ty ← prepReduceExpr ty
    let lhFn := lhs.getAppFn
    let lhArgs ← lhs.getAppArgs.mapM prepReduceExpr
    let lhs := mkAppN lhFn lhArgs
    let rhs ← prepReduceExpr rhs
    let eq' := Lean.mkApp3 (.const ``Eq lvls) ty lhs rhs
    return .some (← mkForallFVars xs eq')

end Auto