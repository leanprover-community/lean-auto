import Lean
import Auto.Lib.BoolExtra
import Auto.Lib.MessageData
import Auto.Lib.ExprExtra
import Auto.Lib.ListExtra
import Auto.Lib.MetaExtra
import Auto.Lib.Containers
import Auto.Lib.AbstractMVars
open Lean

namespace Auto

/-- Proof Tree -/
inductive DTr where
  | node : String → Array DTr → DTr
  | leaf : String → DTr
deriving Inhabited, Hashable, BEq

partial def DTr.toString : DTr → String
| .node s dtrs =>
  s ++ " [" ++ String.intercalate ", " (dtrs.map DTr.toString).toList ++ "]"
| .leaf s => s

instance : ToString DTr where
  toString := DTr.toString

partial def DTr.collectLeafStrings : DTr → Array String
| .node _ dtrs => dtrs.foldl (fun acc l => acc ++ l.collectLeafStrings) #[]
| .leaf s => #[s]

/--
  Universe monomprphic facts
  User-supplied facts should have their universe level parameters
    instantiated before being put into `Reif.State.facts`
-/
structure UMonoFact where
  proof  : Expr
  type   : Expr
  deriv  : DTr
deriving Inhabited, Hashable, BEq

structure Lemma extends UMonoFact where
  params : Array Name -- Universe Levels
deriving Inhabited, Hashable, BEq

instance : ToMessageData Lemma where
  toMessageData lem := MessageData.compose
    m!"⦗⦗ {lem.proof} : {lem.type} @@ " (.compose (MessageData.array lem.params toMessageData) m!" ⦘⦘")

def Lemma.ofUMonoFact (fact : UMonoFact) : Lemma := { fact with params := #[] }

def Lemma.toUMonoFact? (lem : Lemma) : Option UMonoFact :=
  match lem.params with
  | ⟨.nil⟩ => .some lem.toUMonoFact
  | ⟨_::_⟩ => .none

def Lemma.instantiateLevelParamsArray (lem : Lemma) (lvls : Array Level) : Lemma :=
  let ⟨⟨proof, type, deriv⟩, params⟩ := lem
  ⟨⟨proof.instantiateLevelParamsArray params lvls,
   type.instantiateLevelParamsArray params lvls,
   deriv⟩,
   params[lvls.size:]⟩

def Lemma.instantiateLevelParams (lem : Lemma) (lvls : List Level) : Lemma :=
  Lemma.instantiateLevelParamsArray lem ⟨lvls⟩

def Lemma.instantiateMVars (lem : Lemma) : MetaM Lemma := do
  let ⟨⟨proof, type, deriv⟩, params⟩ := lem
  let proof ← Lean.instantiateMVars proof
  let type ← Lean.instantiateMVars type
  return ⟨⟨proof, type, deriv⟩, params⟩

def Lemma.betaReduceType (lem : Lemma) : CoreM Lemma := do
  let ⟨⟨proof, type, deriv⟩, params⟩ := lem
  let type ← Core.betaReduce type
  return ⟨⟨proof, type, deriv⟩, params⟩

/-- Create a `Lemma` out of a constant, given the name of the constant -/
def Lemma.ofConst (name : Name) (deriv : DTr) : CoreM Lemma := do
  let .some decl := (← getEnv).find? name
    | throwError "{decl_name%} :: Unknown constant {name}"
  let type := decl.type
  let params := decl.levelParams
  return ⟨⟨.const name (params.map Level.param), type, deriv⟩, ⟨params⟩⟩

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

/- **TODO:** Determine whether this is useful -/
/- Reorder top-level `∀` so that (non-prop / dependent) ones precede other ones -/
/-
def Lemma.reorderForallInstDep (lem : Lemma) : MetaM Lemma := do
  let depargs := Std.HashSet.emptyWithCapacity.insertMany (Expr.depArgs lem.type)
  Meta.forallTelescope lem.type fun xs body => do
    let mut prec := #[]
    let mut trail := #[]
    for (fvar, i) in xs.zipIdx do
      if depargs.contains i || !(← Meta.isProp (← Meta.inferType fvar)) then
        prec := prec.push fvar
      else
        trail := trail.push fvar
    let proof := Expr.headBeta (Lean.mkAppN lem.proof xs)
    let proof ← Meta.mkLambdaFVars prec (← Meta.mkLambdaFVars trail proof)
    let type ← Meta.mkForallFVars prec (← Meta.mkForallFVars trail body)
    return ⟨⟨proof, type, lem.deriv⟩, lem.params⟩
-/

/--
  Rewrite using a universe-monomorphic rigid equality
  `rw.snd` should have the form `lhs = rhs`, where both sides are rigid
  · If `lhs` occurs in `lem.type`, perform rewrite and return result
  · If `lhs` does not occur in `lem.type`, return `.none`
-/
def Lemma.rewriteUMonoRigid? (lem : Lemma) (rw : UMonoFact) (nonDep : Bool) : MetaM (Option Lemma) := do
  let ⟨rwproof, rwtype, rwDeriv⟩ := rw
  let .some (α, lhs, rhs) ← Meta.matchEq? rwtype
    | throwError "{decl_name%} :: {rwtype} is not an equality"
  let ⟨⟨proof, e, lemDeriv⟩, params⟩ := lem
  let eAbst ← (do
    if nonDep then
      Meta.withLocalDeclD `_a α fun x => do return (← Meta.replaceNonDep e lhs x).abstract #[x]
    else Meta.kabstract e lhs)
  unless eAbst.hasLooseBVars do
    return .none
  let eNew := eAbst.instantiate1 rhs
  let motive := mkLambda `_a BinderInfo.default α eAbst
  unless (← Meta.isTypeCorrect motive) do
    throwError "{decl_name%} :: Motive {motive} is not type correct"
  let eqPrf ← Meta.mkEqNDRec motive proof rwproof
  return .some ⟨⟨eqPrf, ← Core.betaReduce eNew, .node "rw" #[lemDeriv, rwDeriv]⟩, params⟩

def checkNonRecEquality (e : Expr) : MetaM Unit := do
  let .some (_, lhs, rhs) ← Meta.matchEq? e
    | throwError "{decl_name%} :: {e} is not an equality"
  if (← Meta.kabstract rhs lhs).hasLooseBVars then
    throwError "{decl_name%} :: Right-hand side {rhs} of equality contains left-hand side {lhs}"

/--
  Exhaustively rewrite using a universe-polymorphic rigid equality
  · If there are multiple instances of `lhs` with different universe
    level instantiations, all of these instances will be replaced with `rhs`
  · `rw.snd` should have the form `lhs = rhs`, where both sides are rigid
    and `rhs` should not contain `lhs`
-/
def Lemma.rewriteUPolyRigid (lem : Lemma) (rw : Lemma) : MetaM Lemma := do
  let mut lem := lem
  let s ← saveState
  -- Test whether `rhs` contains `lhs`
  let rwty' := rw.type.instantiateLevelParamsArray
    rw.params (← rw.params.mapM (fun _ => Meta.mkFreshLevelMVar))
  checkNonRecEquality rwty'
  restoreState s
  while true do
    let umvars ← rw.params.mapM (fun _ => Meta.mkFreshLevelMVar)
    let .some urw := (rw.instantiateLevelParamsArray umvars).toUMonoFact?
      | throwError "{decl_name%} :: Unexpected error"
    let .some lem' ← Lemma.rewriteUMonoRigid? lem urw false
      | break
    let restmvars := (← umvars.mapM Level.collectLevelMVars).flatMap id
    for lmvar in restmvars do
      if !(← Meta.isLevelDefEq (.mvar lmvar) .zero) then
        break
    lem ← lem'.instantiateMVars
  restoreState s
  return ← lem.betaReduceType

/--
  Exhaustively rewrite using an array of universe-polymorphic rigid equalities
  · Only `lhs`s occurring in non-dependent positions will be replaced by `rhs`
  · If there are multiple instances of `lhs` with different universe
    level instantiations, all of these instances will be replaced with `rhs`
  · `rw.snd` should have the form `lhs = rhs`, where both sides are rigid
    and `rhs` should not contain `lhs`
-/
def Lemma.rewriteUPolyRigidNonDep (lem : Lemma) (rws : Array Lemma) : MetaM Lemma := do
  let mut lem := lem
  let s ← saveState
  -- Test whether `rhs` contains `lhs`
  for rw in rws do
    let rwty' := rw.type.instantiateLevelParamsArray
      rw.params (← rw.params.mapM (fun _ => Meta.mkFreshLevelMVar))
    checkNonRecEquality rwty'
  restoreState s
  while true do
    let lemRef := lem
    for rw in rws do
      let umvars ← rw.params.mapM (fun _ => Meta.mkFreshLevelMVar)
      let .some urw := (rw.instantiateLevelParamsArray umvars).toUMonoFact?
        | throwError "{decl_name%} :: Unexpected error"
      let .some lem' ← Lemma.rewriteUMonoRigid? lem urw true
        | continue
      let restmvars := (← umvars.mapM Level.collectLevelMVars).flatMap id
      for lmvar in restmvars do
        if !(← Meta.isLevelDefEq (.mvar lmvar) .zero) then
          break
      lem ← lem'.instantiateMVars
    if lem == lemRef then
      break
  restoreState s
  return lem

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
  let ⟨⟨proof, type, deriv⟩, params⟩ := lem
  Meta.forallTelescope type fun xs _ => do
    let proof ← Meta.mkLambdaFVars xs (mkAppN proof xs)
    let lem' : Lemma := ⟨⟨proof, type, deriv⟩, params⟩
    return ⟨lem', xs.size, xs.size⟩

/--
  Only introduce leading non-prop binders
  But, if a prop-binder is an instance binder, we still introduce it
-/
def LemmaInst.ofLemmaHOL (lem : Lemma) : MetaM LemmaInst := do
  let ⟨⟨proof, type, deriv⟩, params⟩ := lem
  Meta.forallTelescope type fun xs _ => do
    let mut xs' := #[]
    for x in xs do
      let xty ← Meta.inferType x
      if (← Meta.isProp xty) && !(← Meta.isClass? xty).isSome then
        break
      xs' := xs'.push x
    let proof ← Meta.mkLambdaFVars xs' (mkAppN proof xs')
    let lem' : Lemma := ⟨⟨proof, type, deriv⟩, params⟩
    return ⟨lem', xs'.size, xs'.size⟩

def LemmaInst.ofLemmaLeadingDepOnly (lem : Lemma) : MetaM LemmaInst := do
  let ⟨⟨proof, type, deriv⟩, params⟩ := lem
  let nld := Expr.numLeadingDepArgs type
  Meta.forallBoundedTelescope type nld fun xs _ => do
    if xs.size != nld then
      throwError "{decl_name%} :: Unexpected error"
    let proof ← Meta.mkLambdaFVars xs (mkAppN proof xs)
    let lem' : Lemma := ⟨⟨proof, type, deriv⟩, params⟩
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
    throwError "{decl_name%} :: {li₁} and {li₂} are not instance of the same lemma"
  let lem₁ := li₁.toLemma
  let lem₂ := li₂.toLemma
  let (_, _, body₂) ← Meta.lambdaMetaTelescope lem₂.proof li₂.nbinders
  let args₂ := Expr.getAppBoundedArgs li₂.nargs body₂
  if args₂.size != li₂.nargs then
    throwError "{decl_name%} :: {li₂} is expected to have {li₂.nargs} args, but actually has {args₂.size}"
  Meta.withNewMCtxDepth do
    let paramInst₁ ← lem₁.params.mapM (fun _ => Meta.mkFreshLevelMVar)
    let (_, _, body₁) ← Meta.lambdaMetaTelescope lem₁.proof li₁.nbinders
    let args₁ := Expr.getAppBoundedArgs li₁.nargs body₁
    if args₁.size != li₁.nargs then
      throwError "{decl_name%} :: {li₁} is expected to have {li₁.nargs} args, but actually has {args₁.size}"
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
  deriv     : DTr
deriving Inhabited, Hashable, BEq

instance : ToMessageData MLemmaInst where
  toMessageData mi := MessageData.compose
    m!"MLemmaInst ⦗⦗ {mi.origProof} " (.compose
      (MessageData.intercalate " " (mi.args.toList.map (fun e => m!"({e})")))
        m!" : {mi.type} ⦘⦘")

def MLemmaInst.ofLemmaInst (li : LemmaInst) : MetaM (Array Level × Array Expr × MLemmaInst) := do
  let ⟨⟨proof, type, deriv⟩, params⟩ := li.toLemma
  let lvls ← params.mapM (fun _ => Meta.mkFreshLevelMVar)
  let proof := proof.instantiateLevelParamsArray params lvls
  let type := type.instantiateLevelParamsArray params lvls
  let (mvars, _, proof) ← Meta.lambdaMetaTelescope proof li.nbinders
  let .some origProof := Expr.getAppFnN li.nargs proof
    | throwError "{decl_name%} :: Insufficient number of arguments"
  let args := Expr.getAppBoundedArgs li.nargs proof
  if args.size != li.nargs then
    throwError "{decl_name%} :: Unexpected error"
  let type ← Meta.instantiateForall type mvars
  return (lvls, mvars, ⟨origProof, args, type, deriv⟩)

def LemmaInst.ofMLemmaInst (mi : MLemmaInst) : MetaM LemmaInst := do
  let ⟨origProof, args, type, deriv⟩ := mi
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
  let lem : Lemma := ⟨⟨proof, type, deriv⟩, s.paramNames⟩
  return ⟨lem, nbinders, nargs⟩

partial def collectUniverseLevels : Expr → MetaM (Std.HashSet Level)
| .bvar _ => return Std.HashSet.emptyWithCapacity
| e@(.fvar _) => do collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
| e@(.mvar _) => do collectUniverseLevels (← instantiateMVars (← Meta.inferType e))
| .sort u => return Std.HashSet.emptyWithCapacity.insert u
| e@(.const _ us) => do
  let hus := Std.HashSet.emptyWithCapacity.insertMany us
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
| .lit _ => return Std.HashSet.emptyWithCapacity.insert (.succ .zero)
| .mdata _ e' => collectUniverseLevels e'
| .proj .. => throwError "{decl_name%} :: Please unfold projections before collecting universe levels"

def computeMaxLevel (facts : Array UMonoFact) : MetaM Level := do
  let levels ← facts.foldlM (fun hs ⟨_, ty, _⟩ => do
    let tyUs ← collectUniverseLevels ty
    return mergeHashSet tyUs hs) Std.HashSet.emptyWithCapacity
  -- Compute the universe level that we need to lift to
  -- Use `.succ` two times to reveal bugs
  let level := Level.succ (.succ (levels.fold (fun l l' => Level.max l l') Level.zero))
  let normLevel := level.normalize
  return normLevel

end Auto
