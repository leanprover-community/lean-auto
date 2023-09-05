import Lean
import Auto.Lib.MonadUtils
import Auto.Translation.Assumptions
open Lean

namespace Auto.Reif

structure State where
  -- We will introduce let-binders during reification.
  --   This field records the list of let-binders introduced
  --   during the process so that we know which binders
  --   to abstract when we're done.
  fvarsToAbstract : Array FVarId        := #[]
  -- The set of facts to be processed
  --   This field changes during translation. For example,
  --   during monomorphization, the polymorphic facts
  --   will be removed from `facts` and the instantiated
  --   versions will be added to `facts`.
  facts           : Array UMonoFact     := #[]
  -- During monomorphization, constants will be turned
  --   into free variables. This map records the original expression
  --   corresponding to these free variables.
  exprFVarVal     : HashMap FVarId Expr := {}
  -- Canonicalization map for types
  tyCanMap        : HashMap Expr Expr   := {}  

abbrev ReifM := StateT State MetaM

#genMonadState ReifM

@[inline] def pushFVar (id : FVarId) : ReifM Unit := do
  let fvarsToAbstract ← getFvarsToAbstract
  setFvarsToAbstract (fvarsToAbstract.push id)

-- Given an expression `e`, if it's a `fvar` and is in `polyVal`,
--   return its value recorded in `polyVal`. Otherwise return `e`
@[inline] def resolveVal (e : Expr) : ReifM Expr :=
  match e with
  | .fvar id => do return ((← getExprFVarVal).find? id).getD e
  | _ => return e

@[inline] def resolveTy (e : Expr) : ReifM Expr := do
  match (← getTyCanMap).find? e with
  | .some id => return id
  | .none => throwError "resolveTy :: Unable to resolve {e}"

end Auto.Reif