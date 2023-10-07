import Lean
import Auto.Lib.MessageData
import Auto.Lib.ExprExtra
import Auto.Lib.Containers
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

/-- Check whether `lem₁` subsumes `lem₂` -/
def Lemma.subsumeQuick (lem₁ lem₂ : Lemma) : MetaM Bool := Meta.withNewMCtxDepth <| do
  let paramInst₁ ← lem₁.params.mapM (fun _ => Meta.mkFreshLevelMVar)
  let type₁ := lem₁.type.instantiateLevelParamsArray lem₁.params paramInst₁
  -- Extremely important: Don't put the following line here
  --  `let (_, _, body₁) ← Meta.forallMetaTelescope type₁`
  -- `mvars` can only depend on free variables which are already
  --   inside the lctx when they're creates. Therefore, the
  --   above line must follow `Meta.forallTelescope`
  let ret ← Meta.forallTelescope lem₂.type fun _ body₂ => do
    let (_, _, body₁) ← Meta.forallMetaTelescope type₁
    Meta.isDefEq body₁ body₂
  return ret

def Lemma.equivQuick (lem₁ lem₂ : Lemma) : MetaM Bool := do
  let s₁₂ ← Lemma.subsumeQuick lem₁ lem₂
  let s₂₁ ← Lemma.subsumeQuick lem₂ lem₁
  return s₁₂ && s₂₁

def Lemma.unfoldConst (lem : Lemma) (declName : Name) : MetaM Lemma := do
  let result ← Meta.unfold lem.type declName
  match result.proof? with
  | .some eqProof =>
    let tySort ← Expr.normalizeType (← Meta.inferType lem.type)
    let Expr.sort lvl := tySort
      | throwError "Lemma.unfoldConst :: {tySort} is not a sort"
    let eq ← Meta.mkEq lem.type result.expr
    let eqProof' ← Meta.mkExpectedTypeHint eqProof eq
    let proof := mkAppN (Lean.mkConst ``Eq.mp [lvl]) #[lem.type, result.expr, eqProof', lem.proof]
    -- **TODO**: Remove?
    if !(← Meta.isTypeCorrect proof) then
      throwError "Lemma.unfoldConst :: Proof {proof} is not type correct"
    return ⟨proof, result.expr, lem.params⟩
  | .none => return ⟨lem.proof, result.expr, lem.params⟩

/--
  `declNames` must be topologically sorted, i.e., we do not allow
    the situation where
    · `n` and `m` are both in `declNames`
    · `n` is before `m`
    · The declaration body of `m` contains `n`
-/
def Lemma.unfoldConsts (lem : Lemma) (declNames : Array Name) : MetaM Lemma := do
  declNames.foldlM (fun lem name => lem.unfoldConst name) lem

/-- Reorder top-level `∀` so that (non-prop / dependent) ones precede other ones -/
def Lemma.reorderForallInstDep (lem : Lemma) : MetaM Lemma := do
  let depargs := HashSet.empty.insertMany (Expr.depArgs lem.type)
  Meta.forallTelescope lem.type fun xs body => do
    let mut prec := #[]
    let mut trail := #[]
    for (fvar, i) in xs.data.zip (List.range xs.size) do
      if depargs.contains i || !(← Meta.isProp (← Meta.inferType fvar)) then
        prec := prec.push fvar
      else
        trail := trail.push fvar
    let proof := Expr.headBeta (Lean.mkAppN lem.proof xs)
    let proof ← Meta.mkLambdaFVars prec (← Meta.mkLambdaFVars trail proof)
    let type ← Meta.mkForallFVars prec (← Meta.mkForallFVars trail body)
    return ⟨proof, type, lem.params⟩

/-
  An instance of a `Lemma`. If a lemma has proof `H`,
    then an instance of the lemma would be like
    `fun (ys : βs), H ts`,
    where `ts` can depend on `ys`
  Note that if `li : LemmaInst`, then `li.toLemma` would not be the
    original lemmas that `li` is an instance of. Instead,
    `(li.stripForallN nbinders).getAppFnN nargs` would be the
    original lemma
-/
structure LemmaInst extends Lemma where
  -- Number of binders, i.e. the length of the above `ys`
  nbinders : Nat
  -- Number of arguments that are supplied to the lemma
  -- This should be equal to the number of top-level `∀` binders
  --   of the original lemma's type
  -- Therefore, if two LemmaInsts are instances of the same
  --   lemma, they should have the same `nargs`
  nargs    : Nat
deriving Inhabited, Hashable, BEq

def LemmaInst.ofLemma (lem : Lemma) : MetaM LemmaInst := do
  let ⟨proof, type, params⟩ := lem
  Meta.forallTelescope type fun xs _ => do
    let proof ← Meta.mkLambdaFVars xs (mkAppN proof xs)
    let lem' : Lemma := ⟨proof, type, params⟩
    return ⟨lem', xs.size, xs.size⟩

/--
  Only introduce leading non-prop binders
  But, if a prop-binder is an instance binder, we still introduce it
-/
def LemmaInst.ofLemmaHOL (lem : Lemma) : MetaM LemmaInst := do
  let ⟨proof, type, params⟩ := lem
  Meta.forallTelescope type fun xs _ => do
    let mut xs' := #[]
    for x in xs do
      let xty ← Meta.inferType x
      if (← Meta.isProp xty) && !(← Meta.isClass? xty).isSome then
        break
      xs' := xs'.push x
    let proof ← Meta.mkLambdaFVars xs' (mkAppN proof xs')
    let lem' : Lemma := ⟨proof, type, params⟩
    return ⟨lem', xs'.size, xs'.size⟩

def LemmaInst.ofLemmaLeadingDepOnly (lem : Lemma) : MetaM LemmaInst := do
  let ⟨proof, type, params⟩ := lem
  let nld := Expr.numLeadingDepArgs type
  Meta.forallBoundedTelescope type nld fun xs _ => do
    if xs.size != nld then
      throwError "LemmaInst.ofLemmaLeadingDepOnly :: Unexpected error"
    let proof ← Meta.mkLambdaFVars xs (mkAppN proof xs)
    let lem' : Lemma := ⟨proof, type, params⟩
    return ⟨lem', xs.size, xs.size⟩  

/-- Get the proof of the lemma that `li` is an instance of -/
def LemmaInst.getProofOfLemma (li : LemmaInst) : Option Expr :=
  Option.bind (Expr.stripLambdaN li.nbinders li.proof) (Expr.getAppFnN li.nargs)

instance : ToMessageData LemmaInst where
  toMessageData li := MessageData.compose
    m!"LemmaInst (binders:={li.nbinders}) (args:={li.nargs}) "
    (toMessageData li.toLemma)

def LemmaInst.subsumeQuick (li₁ li₂ : LemmaInst) : MetaM Bool := Meta.withNewMCtxDepth <| do
  if li₁.nargs != li₂.nargs then
    throwError "LemmaInst.subsumeQuick :: {li₁} and {li₂} are not instance of the same lemma"
  let lem₁ := li₁.toLemma
  let lem₂ := li₂.toLemma
  let (_, _, body₂) ← Meta.lambdaMetaTelescope lem₂.proof li₂.nbinders
  let args₂ := Expr.getAppBoundedArgs li₂.nargs body₂
  if args₂.size != li₂.nargs then
    throwError "LemmaInst.subsumeQuick :: {li₂} is expected to have {li₂.nargs} args, but actually has {args₂.size}"
  Meta.withNewMCtxDepth do
    let paramInst₁ ← lem₁.params.mapM (fun _ => Meta.mkFreshLevelMVar)
    let (_, _, body₁) ← Meta.lambdaMetaTelescope lem₁.proof li₁.nbinders
    let args₁ := Expr.getAppBoundedArgs li₁.nargs body₁
    if args₁.size != li₁.nargs then
      throwError "LemmaInst.subsumeQuick :: {li₁} is expected to have {li₁.nargs} args, but actually has {args₁.size}"
    let args₁ := args₁.map (fun e => e.instantiateLevelParamsArray lem₁.params paramInst₁)
    for (arg₁, arg₂) in args₁.zip args₂ do
      if !(← Meta.isDefEq arg₁ arg₂) then
        return false
    return true

def LemmaInst.equivQuick (li₁ li₂ : LemmaInst) : MetaM Bool := do
  let s₁₂ ← LemmaInst.subsumeQuick li₁ li₂
  let s₂₁ ← LemmaInst.subsumeQuick li₂ li₁
  return s₁₂ && s₂₁

abbrev LemmaInsts := Array LemmaInst

def LemmaInsts.newInst? (lis : LemmaInsts) (li : LemmaInst) : MetaM Bool := do
  for li' in lis do
    if ← li'.equivQuick li then
      return false
  return true

/-- A `LemmaInst`, but after `lambdaMetaTelescope` on the `proof` -/
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

def MLemmaInst.ofLemmaInst (li : LemmaInst) : MetaM (Array Level × Array Expr × MLemmaInst) := do
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
  return (lvls, mvars, ⟨origProof, args, type⟩)

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

partial def collectUniverseLevels : Expr → MetaM (HashSet Level)
| .bvar _ => return HashSet.empty
| e@(.fvar _) => do collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
| e@(.mvar _) => do collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
| .sort u => return HashSet.empty.insert u
| e@(.const _ us) => do
  let hus := HashSet.empty.insertMany us
  let tys ← collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
  return mergeHashSet hus tys
| .app fn arg => do
  let fns ← collectUniverseLevels fn
  let args ← collectUniverseLevels arg
  return mergeHashSet fns args
| .lam _ biTy body _ => do
  let tys ← collectUniverseLevels biTy
  let bodys ← collectUniverseLevels body
  return mergeHashSet tys bodys
| .forallE _ biTy body _ => do
  let tys ← collectUniverseLevels biTy
  let bodys ← collectUniverseLevels body
  return mergeHashSet tys bodys
| .letE _ ty v body _ => do
  let tys ← collectUniverseLevels ty
  let vs ← collectUniverseLevels v
  let bodys ← collectUniverseLevels body
  return mergeHashSet (mergeHashSet tys vs) bodys
| .lit _ => return HashSet.empty.insert (.succ .zero)
| .mdata _ e' => collectUniverseLevels e'
| .proj .. => throwError "Please unfold projections before collecting universe levels"

/--
  Universe monomprphic facts
  User-supplied facts should have their universe level parameters
    instantiated before being put into `Reif.State.facts`
  The first `Expr` is the proof, and the second `Expr` is the fact
-/
abbrev UMonoFact := Expr × Expr

def computeMaxLevel (facts : Array UMonoFact) : MetaM Level := do
  let levels ← facts.foldlM (fun hs (proof, ty) => do
    let proofUs ← collectUniverseLevels proof
    let tyUs ← collectUniverseLevels ty
    return mergeHashSet (mergeHashSet proofUs tyUs) hs) HashSet.empty
  -- Compute the universe level that we need to lift to
  -- Use `.succ` two times to reveal bugs
  let level := Level.succ (.succ (levels.fold (fun l l' => Level.max l l') Level.zero))
  let normLevel := level.normalize
  return normLevel

end Auto