import Lean
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
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

register_option auto.mono.tyRed.mode : Meta.TransparencyMode := {
  defValue := .reducible
  descr := "Transparency level used when reducing types. The default mode `reducible` does nothing."
}

register_option auto.mono.tyDefEq.mode : Meta.TransparencyMode := {
  defValue := .default
  descr := "Transparency level used when testing definitional equality of types"
}

namespace Auto

def unfoldProj (e : Expr) : MetaM Expr :=
  match e with
  | .proj name idx struct => do
    let some (.inductInfo indi) := (← getEnv).find? name
      | throwError s!"{decl_name%} :: {name} is not a inductive type"
    let some structInfo := getStructureInfo? (← getEnv) name
      | throwError s!"{decl_name%} :: {name} is not a structure"
    let nameMap : Std.HashMap Name StructureFieldInfo := Std.HashMap.ofList
      (structInfo.fieldInfo.map (fun sfi => (sfi.fieldName, sfi))).toList
    let sorted := structInfo.fieldNames.map (fun name => nameMap.get? name)
    let .some (.some sfi) := sorted[idx]?
      | throwError s!"{decl_name%} :: Projection index out of bound"
    let nones : List (Option Expr) := (List.range indi.numParams).map (fun _ => .none)
    Meta.mkAppOptM sfi.projFn ((Array.mk nones).push struct)
  | _ => return e

def prepReduceExprWithMode (term : Expr) (mode : TransparencyMode) : MetaM Expr := do
  let red (e : Expr) : MetaM TransformStep := do
    let e := e.consumeMData
    let e ← Meta.whnf e
    return .continue e
  -- Reduce
  let term ← Meta.withTransparency mode <| Meta.transform term (pre := red) (usedLetOnly := false)
  -- Unfold projection
  let term ← Meta.transform term (pre := fun e => do return .continue (← unfoldProj e))
  return term

/-- This function is expensive -/
def prepReduceExpr (term : Expr) : MetaM Expr := do
  let mode := auto.redMode.get (← getOptions)
  prepReduceExprWithMode term mode

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

def prepReduceTypeForall (e : Expr) : MetaM Expr := do
  let e ← prepReduceExpr e
  let mode := auto.mono.tyRed.mode.get (← getOptions)
  Meta.withTransparency mode <| Meta.normalizeNondependentForall e

end Auto
