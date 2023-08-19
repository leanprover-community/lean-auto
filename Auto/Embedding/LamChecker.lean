import Auto.Embedding.LamConv
import Auto.Lib.BinTree

namespace Auto.Embedding.Lam

structure TTable where
  valid : Auto.BinTree (List LamSort × LamTerm)
  wf    : Auto.BinTree (List LamSort × LamTerm × LamSort)

inductive ChkStep where
  | valid_of_interp (lctx : List LamSort) (t : LamTerm) (dest : Nat) : ChkStep
  | wf_of_check (lctx : List LamSort) (t : LamTerm) (dest : Nat) : ChkStep

end Auto.Embedding.Lam