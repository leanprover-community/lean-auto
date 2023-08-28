import Lean
import Auto.Lib.MessageData
import Auto.Lib.ExprExtra
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

def Lemma.equivQuick (lem₁ lem₂ : Lemma) : MetaM Bool := do
  let s₁₂ ← Lemma.subsumeQuick lem₁ lem₂
  let s₂₁ ← Lemma.subsumeQuick lem₂ lem₁
  return s₁₂ && s₂₁

-- An instance of a `Lemma`, which is basically the
--   proof of the lemma applied to some arguments
-- Bound variables in `args` and `binders` are
--   represented by loose bound variables
-- Refer to `Lemma.ofLemmaInst` for the exact semantics
structure LemmaInst where
  args    : Array Expr
  binders : Array (Name × Expr × BinderInfo)
  levels  : Array Level
  params  : Array Name
deriving Inhabited, Hashable, BEq

def Lemma.ofLemmaInst (lem : Lemma) (lemInst : LemmaInst) : Option Lemma :=
  let ⟨proof, type, lemparams⟩ := lem
  let ⟨args, binders, levels, instparams⟩ := lemInst
  let proof := proof.instantiateLevelParamsArray lemparams levels
  let type := type.instantiateLevelParamsArray lemparams levels
  let proof := Lean.mkAppN proof lemInst.args
  match Expr.stripForall args.size type with
  | .some typeStripped =>
    let type := Expr.instantiateRev typeStripped args
    let proof := Expr.mkLambdaBinderDescrs binders proof
    let type := Expr.mkForallBinderDescrs binders type
    .some ⟨proof, type, instparams⟩
  | .none => .none

-- A `Lemma`, but after `forallMetaTelescope`
structure MLemma where
  proof : Expr
  type  : Expr
deriving Inhabited, Hashable, BEq

instance : ToMessageData MLemma where
  toMessageData lem := m!"⦗⦗ {lem.proof} : {lem.type} ⦘⦘"

def MLemma.ofLemma (lem : Lemma) : MetaM MLemma := do
  let ⟨proof, type, params⟩ := lem
  let lvls ← params.mapM (fun _ => Meta.mkFreshLevelMVar)
  let proof := proof.instantiateLevelParamsArray params lvls
  let type := type.instantiateLevelParamsArray params lvls
  let (mvars, bis, _) ← Meta.forallMetaTelescope type
  sorry

end Auto