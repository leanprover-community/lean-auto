import Lean
import Auto.Util.MonadUtils
open Lean

namespace Auto.TFront

inductive ILogicalType where
  | eqF
  | forallF
  | existsF
deriving Hashable, Inhabited, BEq

structure TFrontM.State where
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
  -- During monomorphization, polymorphic logical
  --   constants (=, ∀, ∃) will be turned into free
  --   variables representing instances of these
  --   constants. We have to record these free variables
  --   so that we know they're interpreted logical
  --   constants during reification.
  iLogical : HashMap FVarId ILogicalType

abbrev TFrontM := StateT TFrontM.State MetaM
#genMonadState TFrontM

@[inline] def pushFVar (id : FVarId) : TFrontM Unit := do
  let fvarsToAbstract ← getFvarsToAbstract
  setFvarsToAbstract (fvarsToAbstract.push id)

end Auto.TFront