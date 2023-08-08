import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

theorem Eq.symm (lval : LamValuation)
  {lctxTy : Nat → LamSort} {lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal}
  (wf : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, .app (.app (.base (.eq n)) a) b, .base .prop⟩)
  (H : GLift.down (LamWF.interp lval lctxTy lctxTerm wf)) : Nat := sorry

end Auto.Embedding.Lam