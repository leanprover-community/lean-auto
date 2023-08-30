import Lean
import Auto.Lib.MonadUtils
import Auto.Lib.Containers
open Lean

namespace Auto.Reif

-- Universe monomprphic facts
-- User-supplied facts should have their universe level parameters
--   instantiated before being put into `Reif.State.facts`
-- The first `Expr` is the proof, and the second `Expr` is the fact
abbrev UMonoFact := Expr × Expr

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
  -- During monomorphization, polymorphic constants will be turned
  --   into free variables. This map records the original expression
  --   corresponding to these free variables.
  polyVal         : HashMap FVarId Expr := HashMap.empty

abbrev ReifM := StateT State MetaM

#genMonadState ReifM

@[inline] def pushFVar (id : FVarId) : ReifM Unit := do
  let fvarsToAbstract ← getFvarsToAbstract
  setFvarsToAbstract (fvarsToAbstract.push id)

-- Given an expression `e`, if it's a `fvar` and is in `polyVal`,
--   return its value recorded in `polyVal`. Otherwise return `e`
@[inline] def resolvePolyVal (e : Expr) : ReifM Expr :=
  match e with
  | .fvar id => do return ((← getPolyVal).find? id).getD e
  | _ => return e

end Auto.Reif