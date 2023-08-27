import Mathlib
import Auto.Lib.ExprExtra

open Lean Auto

def showClasses (env : Environment) : Except String (Array (ConstantInfo × Array Nat)) := do
  let outParamMap := (classExtension.getState env).outParamMap
  (Array.mk outParamMap.toList).mapM (fun (name, outParams) => do
    let .some decl := env.find? name
      | throw s!"showClasses :: unknown declarationn {name}"
    return (decl, outParams))

#eval @id (MetaM Unit) (do
  let env ← getEnv
  let .ok arr := showClasses env
    | throwError "Failure"
  let mut insts := 0
  for (ci, params) in arr do
    if (Expr.instArgs ci.type).size != 0 then
      IO.println s!"Has inst arg : {ci.name}"
    else
      IO.println s!"No inst arg  : {ci.name}")

#check IsAtomistic
#check VAddAssocClass
#check isCoatomistic_dual_iff_isAtomistic
#check sSup_atoms_le_eq
#check IsAtom
#check FirstOrder.Language.Theory.Model
#check UniformContinuousConstVAdd
#check BooleanAlgebra
#check CircularPartialOrder.btw_antisymm
#check IsInvariantSubfield.smul_mem
#check @HilbertBasis

def inspectDepArgs (c : Expr) : Elab.Term.TermElabM Unit := do
  let ty ← Meta.inferType c
  IO.println (Expr.depArgs ty)

#getExprAndApply[@HAdd.hAdd|inspectDepArgs]