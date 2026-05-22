import Lean
import Auto.Lib.TreeList

namespace Auto.Embedding.Coc

inductive PropConst

inductive BoolConst

inductive NatConst

inductive CocBaseTerm
  | prop
  | bool
  | nat
  | pcst : PropConst → CocBaseTerm
  | bcst : BoolConst → CocBaseTerm
  | ncst : NatConst → CocBaseTerm

inductive CocTerm
  | b : Nat → CocTerm -- bound variable, de bruijn index
  | t : CocBaseTerm → CocTerm
  | «λ» : CocTerm → CocTerm → CocTerm
  | «∀» : CocTerm → CocTerm → CocTerm

-- `Γ ⊢ term : type`
inductive CocWF : TreeList CocTerm → CocTerm → CocTerm → Type
  | ofBVar {lctx : TreeList CocTerm} (n : Nat) : CocWF lctx (.b n) sorry
  -- TODO

end Auto.Embedding.Coc
