import Mathlib
import Auto.Lib.ClassExtra

open Lean Auto

#eval @id (MetaM Unit) (do
  let env ← getEnv
  let .ok arr := showClasses env
    | throwError "Failure"
  let mut insts := 0
  for (ci, params) in arr do
    if (instArgs ci.type).size != 0 then
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
#check CircularPartialOrder
#check IsInvariantSubfield