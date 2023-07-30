import Lean
import Auto.Util.MonadUtils
open Lean

namespace Auto.Front

structure FrontM.State where
  -- We will introduce let-binders during reification.
  --   This field records the list of let-binders introduced
  --   during the process so that we know which binders
  --   to abstract when we're done.
  fvarsToAbstract : Array FVarId
  -- The set of facts to be processed
  --   This field changes during translation. For example,
  --   during monomorphization, the polymorphic facts
  --   will be removed from `facts` and the instantiated
  --   versions will be added to `facts`.
  facts           : Array Expr

abbrev FrontM := StateT FrontM.State MetaM
#genMonadState FrontM

@[inline] def pushFVar (id : FVarId) : FrontM Unit := do
  let fvarsToAbstract ← getFvarsToAbstract
  setFvarsToAbstract (fvarsToAbstract.push id)

end Auto.Front