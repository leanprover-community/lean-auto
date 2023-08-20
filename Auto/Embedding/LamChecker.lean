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
  wf    : Auto.BinTree (List LamSort × LamSort × LamTerm)
  -- Valid propositions
  valid : Auto.BinTree (List LamSort × LamTerm)

-- An entry of RTable
inductive REntry where
  | none    : REntry
  | wf      : List LamSort → LamSort → LamTerm → REntry
  | valid   : List LamSort → LamTerm → REntry

def RTable.addEntry (r : RTable) (n : Nat) : REntry → RTable
| .none         => r
| .wf lctx s t  => ⟨r.wf.insert n ⟨lctx, s, t⟩, r.valid⟩
| .valid lctx t => ⟨r.wf, r.valid.insert n ⟨lctx, t⟩⟩

-- Invariant of `wf`
def RTable.wfInv
  (lval : LamValuation.{u})
  (wf : Auto.BinTree (List LamSort × LamSort × LamTerm)) :=
  wf.allp (fun ⟨lctx, rty, t⟩ => LamThmWF' lval lctx rty t)

-- Invariant of `valid
def RTable.validInv
  (lval : LamValuation.{u})
  (valid : Auto.BinTree (List LamSort × LamTerm)) :=
  valid.allp (fun ⟨lctx, t⟩ => LamThmValid lval lctx t)

-- Invariant of `RTable`
def RTable.inv (lval : LamValuation.{u}) (r : RTable) :=
  wfInv lval r.wf ∧ validInv lval r.valid

inductive ChkStep where
  -- Adds `⟨lctx, t, t.lamCheck!⟩` to `rtable.wf`
  | wfOfCheck (lctx : List LamSort) (t : LamTerm) : ChkStep

def ChkStep.eval (ltv : LamTyVal) (r : RTable) : (cs : ChkStep) → REntry
| .wfOfCheck lctx t =>
  match LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t with
  | .some rty =>
    match Nat.ble (t.maxLooseBVarSucc) (lctx.length) with
    | true  => .wf lctx rty t
    | false => .none
  | .none => .none

end Auto.Embedding.Lam