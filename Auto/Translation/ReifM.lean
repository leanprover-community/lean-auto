import Lean
import Auto.Util.MonadUtils
open Lean

namespace Auto.Reif

-- Universe monomprphic facts
-- User-supplied facts should have their universe level parameters
--   instantiated before being put into `Reif.State.facts`
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
  -- The first `Expr` is the proof, and the second `Expr` is the fact
  facts           : Array UMonoFact     := #[]
  -- During monomorphization, interpreted constants
  --   (¬, ∧, ∨, →, ↔, =, ∀, ∃, ...), except for `prop,
  --   will be turned into free variables representing
  --   (instances of) these constants. We have to record
  --   these free variables so that we know they're interpreted
  --   constants during reification.
  interpreted     : HashMap FVarId Expr := HashMap.empty

abbrev ReifM := StateT State MetaM
#genMonadState ReifM

@[inline] def pushFVar (id : FVarId) : ReifM Unit := do
  let fvarsToAbstract ← getFvarsToAbstract
  setFvarsToAbstract (fvarsToAbstract.push id)

end Auto.Reif