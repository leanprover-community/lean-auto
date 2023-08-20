import Auto.Embedding.LamConv
import Auto.Lib.BinTree

namespace Auto.Embedding.Lam

-- Table of valid propositions and well-formed formulas
-- Note that `Auto.BinTree α` is equivalent to `{n : Nat // n ≠ 0} → Option α`,
--   which means that
--   1. Index `0` is not present. Inserting element to index `0` does nothing,
--      and retrieving element from index `0` produces `.none`
--   2. `.some` entries may be interspersed with `.none` entries
structure RTable where
  -- Well-formed formulas, with types
  wf    : Auto.BinTree (List LamSort × LamTerm × LamSort)
  -- Valid propositions
  valid : Auto.BinTree (List LamSort × LamTerm)

inductive ChkStep (lval : LamValuation) where
  -- Adds `⟨lctx, t, dest⟩` to `rtable.wf`
  | wf_of_check
      (lctx : List LamSort)
      (t : LamTerm)
      (dest : Nat) : ChkStep lval
  | valid_of_interp
      (p : LamTerm)
      (h : (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down)
      (dest : Nat) : ChkStep lval

end Auto.Embedding.Lam