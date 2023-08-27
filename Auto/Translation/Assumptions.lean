import Lean
import Auto.Lib.MessageData 
open Lean

namespace Auto

structure Lemma where
  proof  : Expr       -- Proof of the lemma
  type   : Expr       -- The statement of the lemma
  params : Array Name -- Universe Levels
deriving Inhabited, Hashable, BEq

instance : ToMessageData Lemma where
  toMessageData lem := MessageData.compose
    m!"⦗⦗ {lem.proof} : {lem.type} @@ " (.compose (MessageData.array lem.params toMessageData) m!" ⦘⦘")

-- `lem₁` subsumes `lem₂`
def Lemma.subsumeQuick (lem₁ lem₂ : Lemma) : MetaM Bool := Meta.withNewMCtxDepth <| do
  let paramInst₁ ← lem₁.params.mapM (fun _ => Meta.mkFreshLevelMVar)
  let type₁ := lem₁.type.instantiateLevelParamsArray lem₁.params paramInst₁
  let (_, _, body₁) ← Meta.forallMetaTelescope type₁
  Meta.forallTelescope lem₂.type fun _ body₂ =>
    Meta.isDefEq body₁ body₂

def Lemma.equiv (lem₁ lem₂ : Lemma) : MetaM Bool := do
  let s₁₂ ← Lemma.subsumeQuick lem₁ lem₂
  let s₂₁ ← Lemma.subsumeQuick lem₂ lem₁
  return s₁₂ && s₂₁

end Auto