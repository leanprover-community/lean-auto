import Lean
import Auto.Lib.MessageData
import Auto.Lib.ExprExtra
import Auto.Lib.AbstractMVars
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
  let s ← saveState
  let paramInst₁ ← lem₁.params.mapM (fun _ => Meta.mkFreshLevelMVar)
  let type₁ := lem₁.type.instantiateLevelParamsArray lem₁.params paramInst₁
  -- Extremely important: Don't put the following line here
  --  `let (_, _, body₁) ← Meta.forallMetaTelescope type₁`
  -- `mvars` can only depend on free variables  which are already
  --   inside the lctx when they're creates. Therefore, the
  --   above line must follow `Meta.forallTelescope`
  let ret ← Meta.forallTelescope lem₂.type fun _ body₂ => do
    let (_, _, body₁) ← Meta.forallMetaTelescope type₁
    Meta.isDefEq body₁ body₂
  restoreState s
  return ret

def Lemma.equivQuick (lem₁ lem₂ : Lemma) : MetaM Bool := do
  let s₁₂ ← Lemma.subsumeQuick lem₁ lem₂
  let s₂₁ ← Lemma.subsumeQuick lem₂ lem₁
  return s₁₂ && s₂₁

axiom List.map_append.{u_2, u_1} : ∀ {α : Type u_2} {β : Type u_1} (f : α → β) (l₁ l₂ : List α),
  List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂

def sjd (_ : Expr) : Elab.Term.TermElabM Unit := do
  let proof := Expr.const ``List.map_append [.param `x, .param `y]
  let type ← Meta.inferType proof
  let lem := Lemma.mk proof type #[`x, `y]
  let b ← Lemma.subsumeQuick lem lem
  logInfo m!"{b}, {lem}"
  return

#getExprAndApply[2|sjd]

-- An instance of a `Lemma`. If a lemma has proof `H`,
--   then an instance of the lemma would be like
--   `fun (ys : βs), H ts`,
--   where `ts` can depend on `ys`
-- Note that if `li : LemmaInst`, then `li.toLemma` would not be the
--   original lemmas that `li` is an instance of. Instead,
--   `(li.stripForall nbinders).getAppFnN nargs` would be the
--   original lemma
structure LemmaInst extends Lemma where
  -- Number of binders, i.e. the length of the above `ys`
  nbinders : Nat
  -- Number of arguments that are supplied to the lemma
  -- This should be equal to the number of top-level `∀` binders
  --   of the original lemma's type
  nargs    : Nat
deriving Inhabited, Hashable, BEq

def LemmaInst.ofLemma (lem : Lemma) : MetaM LemmaInst := do
  let ⟨proof, type, params⟩ := lem
  Meta.forallTelescope type fun xs _ => do
    let proof ← Meta.mkLambdaFVars xs (mkAppN proof xs)
    let lem' : Lemma := ⟨proof, type, params⟩
    return ⟨lem', xs.size, xs.size⟩

instance : ToMessageData LemmaInst where
  toMessageData li := MessageData.compose
    m!"LemmaInst (binders:={li.nbinders}) (args:={li.nargs}) "
    (toMessageData li.toLemma)

-- A `LemmaInst`, but after `lambdaMetaTelescope` on the `proof`
structure MLemmaInst where
  origProof : Expr
  args      : Array Expr
  type      : Expr
deriving Inhabited, Hashable, BEq

instance : ToMessageData MLemmaInst where
  toMessageData mi := MessageData.compose
    m!"MLemmaInst ⦗⦗ {mi.origProof} " (.compose
      (MessageData.intercalate " " (mi.args.data.map (fun e => m!"({e})")))
        m!" : {mi.type} ⦘⦘")

def MLemmaInst.ofLemmaInst (li : LemmaInst) : MetaM MLemmaInst := do
  let ⟨proof, type, params⟩ := li.toLemma
  let lvls ← params.mapM (fun _ => Meta.mkFreshLevelMVar)
  let proof := proof.instantiateLevelParamsArray params lvls
  let type := type.instantiateLevelParamsArray params lvls
  let (mvars, _, proof) ← Meta.lambdaMetaTelescope proof li.nbinders
  let .some origProof := Expr.getAppFnN li.nargs proof
    | throwError "MLemmaInst.ofLemmaInst :: Insufficient number of arguments"
  let args := Expr.getAppBoundedArgs li.nargs proof
  if args.size != li.nargs then
    throwError "MLemmaInst.ofLemmaInst :: Unexpected error"
  let type ← Meta.instantiateForall type mvars
  return ⟨origProof, args, type⟩

def LemmaInst.ofMLemmaInst (mi : MLemmaInst) : MetaM LemmaInst := do
  let ⟨origProof, args, type⟩ := mi
  let origProof ← instantiateMVars origProof
  let args ← args.mapM instantiateMVars
  let type ← instantiateMVars type
  let (proof, s) := Auto.AbstractMVars.abstractExprMVars (mkAppN origProof args)
    { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  let (type, s) := Auto.AbstractMVars.abstractExprMVars type s
  setNGen s.ngen
  setMCtx s.mctx
  let nbinders := s.fvars.size
  let nargs := args.size
  let proof := s.lctx.mkLambda s.fvars proof
  let type := s.lctx.mkForall s.fvars type
  let lem : Lemma := ⟨proof, type, s.paramNames⟩
  return ⟨lem, nbinders, nargs⟩

end Auto