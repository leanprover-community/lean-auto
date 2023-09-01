import Lean
import Auto.Embedding.Lift
import Auto.Translation.Assumptions
import Auto.Translation.ReifM
import Auto.Lib.LevelExtra
import Auto.Lib.ExprExtra
import Auto.Lib.MonadUtils
import Auto.Lib.Containers
import Auto.Lib.MetaState
open Lean

initialize
  registerTraceClass `auto.mono
  registerTraceClass `auto.mono.printLemmaInst
  registerTraceClass `auto.mono.printConstInst

register_option auto.mono.saturationThreshold : Nat := {
  defValue := 250
  descr := "Threshold for number of potentially new lemma" ++
    " instances generated during the saturation loop of monomorphization"
}

register_option auto.mono.recordInstInst : Bool := {
  defValue := false
  descr := "Whether to record instances of constants with the `instance` attribute"
}

namespace Auto.Monomorphization
open Embedding

inductive CiHead where
  | fvar  : FVarId → CiHead
  | mvar  : MVarId → CiHead
  | const : Name → Array Level → CiHead
  deriving Inhabited, Hashable, BEq

def CiHead.ofExpr? : Expr → Option CiHead
| .fvar id => .some (.fvar id)
| .mvar id => .some (.mvar id)
| .const name lvls => .some (.const name ⟨lvls⟩)
| _ => .none

def CiHead.toExpr : CiHead → Expr
| .fvar id => .fvar id
| .mvar id => .mvar id
| .const name lvls => .const name lvls.data

-- Ignore constant's levels
def CiHead.fingerPrint : CiHead → Expr
| .fvar id => .fvar id
| .mvar id => .mvar id
| .const name _ => .const name []

def CiHead.isConst : CiHead → Bool
| .fvar _ => false
| .mvar _ => false
| .const _ _ => true

def CiHead.isNamedConst (name : Name) : CiHead → Bool
| .fvar _ => false
| .mvar _ => false
| .const name' _ => name == name'

instance : ToMessageData CiHead where
  toMessageData (ch : CiHead) := m!"{ch.toExpr}"

def CiHead.inferType (ci : CiHead) : MetaM Expr := Meta.inferType ci.toExpr

def CiHead.isInstanceQuick (ci : CiHead) : MetaM Bool := do
  if let .const name _ := ci then
    if ← Meta.isInstance name then
      return true
  if (← Meta.isClass? (← ci.inferType)).isSome then
    return true
  return false

-- **Remark**: This function assigns level mvars if necessary
def CiHead.equiv (ch₁ ch₂ : CiHead) : MetaM Bool :=
  match ch₁, ch₂ with
  | .fvar id₁, .fvar id₂ => pure (id₁ == id₂)
  | .mvar id₁, .mvar id₂ => pure (id₁ == id₂)
  | .const name₁ lvls₁, .const name₂ lvls₂ => do
    if name₁ != name₂ then
      return false
    if lvls₁.size != lvls₂.size then
      return false
    for (lvl₁, lvl₂) in lvls₁.zip lvls₂ do
      if !(← Meta.isLevelDefEq lvl₁ lvl₂) then
        return false
    return true
  | _, _ => pure false

/-
  If a constant `c` is of type `∀ (xs : αs), t`,
    then its valid instance will be `c` with all of its
    universe levels and dependent arguments instantiated.
    So, we record the instantiation of universe levels
    and dependent arguments.
  
  As to monomorphization, we will not record instances of
    · monomorphic constants
    · constants with `instance` attribute
-/
structure ConstInst where
  head       : CiHead
  argsInst   : Array Expr
  instDepArgs : Array Nat
  deriving Inhabited, Hashable, BEq

def ConstInst.fingerPrint (ci : ConstInst) := ci.head.fingerPrint

instance : ToMessageData ConstInst where
  toMessageData ci := MessageData.compose
    m!"ConstInst ⦗⦗ {ci.head}" (.compose
        m!" " (.compose
          (MessageData.intercalate " " (ci.argsInst.data.map (fun e => m!"({e})")))
            m!" ⦘⦘"))

-- **Remark**: This function assigns metavariables if necessary,
--   but its only usage in this file is under `Meta.withNewMCtxDepth`
-- Note that since `ci₁, ci₂` are both `ConstInst`, they does not
--   contain loose bound variables
def ConstInst.equiv (ci₁ ci₂ : ConstInst) : MetaM Bool := do
  let ⟨head₁, argsInst₁, idx₁⟩ := ci₁
  let ⟨head₂, argsInst₂, idx₂⟩ := ci₂
  if argsInst₁.size != argsInst₂.size || idx₁ != idx₂ then
    throwError "ConstInst.equiv :: Unexpected error"
  if !(← head₁.equiv head₂) then
    return false
  for (arg₁, arg₂) in argsInst₁.zip argsInst₂ do
    if !(← Meta.isDefEq arg₁ arg₂) then
      return false
  return true

-- **Remark**:
-- · This function assigns metavariables if necessary
-- · Runs in `MetaM`, so `e` should not have loose bound variables
def ConstInst.matchExpr (e : Expr) (ci : ConstInst) : MetaM Bool := do
  let fn := e.getAppFn
  let .some ch := CiHead.ofExpr? fn
    | return false
  if !(← ch.equiv ci.head) then
    return false
  let instDepArgs := ci.instDepArgs
  if instDepArgs.size != ci.argsInst.size then
    throwError "ConstInst.matchExpr :: Unexpected error"
  let args := e.getAppArgs
  for (idx, ciarg) in instDepArgs.zip ci.argsInst do
    let .some arg := args[idx]?
      | return false
    if !(← Meta.isDefEq arg ciarg) then
      return false
  return true

/-
  **Remark**: Runs in `MetaM`, but accepts `e` with loose bound variables.
  **TODO**: Fix this
  Given an hypothesis `t`, we will traverse the hypothesis to find
    instances of polymorphic constants
  · Binders of the hypothesis are not introduced as fvars/mvars, so
    they remain loose bound variables inside the body
  · `param` records universe level parameters of the hypothesis are
  So, the criterion that an expression `e` is a valid instance is that
  · All instDepArgs are applied
  · No loose bound variables in instDepArgs
  · The expression does not contain level parameters in `params`
-/
def ConstInst.ofExpr? (params : Array Name) (e : Expr) : MetaM (Option ConstInst) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .some head := CiHead.ofExpr? fn
    | return .none
  let paramSet := HashSet.empty.insertMany params
  -- `e` should not have bound parameters
  if let .some _ := Expr.findParam? (fun n => paramSet.contains n) e then
    return .none
  -- Do not record instances of a constant with attribute `instance`
  if (← head.isInstanceQuick) && !(auto.mono.recordInstInst.get (← getOptions)) then
    return .none
  let depargIndexes := Expr.instDepArgs (← head.inferType)
  let lastDeparg? := depargIndexes[depargIndexes.size - 1]?
  if let .some lastDeparg := lastDeparg? then
    if args.size ≤ lastDeparg then
      return none
  let mut argsInst := #[]
  for idx in depargIndexes do
    let arg := args[idx]!
    if arg.hasLooseBVars then
      return none
    argsInst := argsInst.push arg
  return some ⟨head, argsInst, depargIndexes⟩

private def ConstInst.toExprAux (args : List (Option Expr))
  (tys : List (Name × Expr × BinderInfo)) (e ty : Expr) : Option Expr :=
  match args with
  | .nil =>
    Option.some <| Prod.fst <| tys.foldl (fun (e, idx) (name, bty, bi) =>
      (Expr.lam name bty e bi, .succ idx)) (e, 0)
  | .none :: args' =>
    match ty with
    | .forallE name bty body bi =>
      let bvar := .bvar tys.length
      toExprAux args' ((name, bty, bi) :: tys) (.app e bvar) (body.instantiate1 bvar)
    | _ => .none
  | .some arg :: args' =>
    match ty with
    | .forallE _ _ body _ =>
      toExprAux args' tys (.app e arg) (body.instantiate1 arg)
    | _ => .none

def ConstInst.toExpr (ci : ConstInst) : MetaM Expr := do
  let type ← instantiateMVars (← ci.head.inferType)
  let nargs := (Nat.succ <$> ci.instDepArgs[ci.instDepArgs.size - 1]?).getD 0
  let mut args : Array (Option Expr) := (Array.mk (List.range nargs)).map (fun n => .none)
  for (arg, idx) in ci.argsInst.zip ci.instDepArgs do
    args := args.setD idx (.some arg)
  let .some ret := ConstInst.toExprAux args.data [] ci.head.toExpr type
    | throwError "ConstInst.toExpr :: Unexpected error"
  return ret

-- Precondition : `.some ci == ← ConstInst.ofExpr? e`
-- Returns the list of non-dependent arguments in `e.getAppArgs`
def ConstInst.getOtherArgs (ci : ConstInst) (e : Expr) : CoreM (Array Expr) := do
  let mut args := e.getAppArgs.map Option.some
  for idx in ci.instDepArgs do
    args := args.setD idx .none
  let mut ret := #[]
  for arg? in args do
    if let .some arg := arg? then
      ret := ret.push arg
  return ret

private partial def collectConstInsts (params : Array Name) : Expr → MetaM (Array ConstInst)
| e@(.const _ _) => processOther params e
| e@(.fvar _) => processOther params e
| e@(.mvar _) => processOther params e
| e@(.app ..) => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let insts := (← (args.push fn).mapM (collectConstInsts params)).concatMap id
  match ← ConstInst.ofExpr? params e with
  | .some ci => return insts.push ci
  | .none => return insts
| .lam _ ty body bi => do
  let insts ← collectConstInsts params body
  -- Do not look into instance binders
  if bi.isInstImplicit then
    return insts
  else
    return insts ++ (← collectConstInsts params ty)
| .forallE _ ty body bi => do
  let insts ← collectConstInsts params body
  -- Do not look into instance binders
  if bi.isInstImplicit then
    return insts
  else
    return insts ++ (← collectConstInsts params ty)
| .letE .. => throwError "collectConstInsts :: Let-expressions should have been reduced"
| .mdata .. => throwError "collectConstInsts :: mdata should have been consumed"
| .proj .. => throwError "collectConstInsts :: Projections should have been turned into ordinary expressions"
| _ => return #[]
where processOther (params : Array Name) (e : Expr) : MetaM (Array ConstInst) := do
  match ← ConstInst.ofExpr? params e with
  | .some ci => return #[ci]
  | .none => return #[]

-- Array of instances of a polymorphic constant
abbrev ConstInsts := Array ConstInst

-- Given an array `cis` and a potentially new instance `ci`
-- · If `ci` is new, add it to `ConstInsts` and return `true`
-- · If `ci` is not new, return an element of the original `ConstInsts`
--   which is definitionally equal to `ci`
def ConstInsts.canonicalize? (cis : ConstInsts) (ci : ConstInst) : MetaM (Option ConstInst) := do
  for ci' in cis do
    if ← Meta.withNewMCtxDepth (ci'.equiv ci) then
      return .some ci'
  return .none

-- Given an MLemmaInst `mi` and a subexpressions `e` of `mi.type`,
--   try to match `e` and the subexpressions of `e` against `ci`.
-- This function is used by `LemmaInst.matchConstInst` only
private partial def MLemmaInst.matchConstInst (ci : ConstInst) (mi : MLemmaInst) : Expr → MetaM (HashSet LemmaInst)
| .bvar _ => throwError "MLemmaInst.matchConstInst :: Loose bound variable"
| e@(.app ..) => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let mut ret ← MLemmaInst.matchConstInst ci mi fn
  for arg in args do
    ret := mergeHashSet ret (← MLemmaInst.matchConstInst ci mi arg)
  let s ← saveState
  if (← ci.matchExpr e) then
    ret := ret.insert (← LemmaInst.ofMLemmaInst mi)
  restoreState s
  return ret
| e@(.forallE ..) => Meta.forallTelescope e fun xs body => do
    let mut ret ← MLemmaInst.matchConstInst ci mi body
    for x in xs do
      let .fvar id := x
        | throwError "MLemmaInst.matchConstInst :: Unexpected error"
      let type ← id.getType
      ret := mergeHashSet ret (← MLemmaInst.matchConstInst ci mi type)
    return ret
| .lam name ty body bi => Meta.withLocalDecl name bi ty fun x => do
    let tyInst ← MLemmaInst.matchConstInst ci mi ty
    let bodyInst ← MLemmaInst.matchConstInst ci mi (body.instantiate1 x)
    return mergeHashSet tyInst bodyInst
| .letE .. => throwError "MLemmaInst.matchConstInst :: Let-expressions should have been reduced"
| .mdata .. => throwError "MLemmaInst.matchConstInst :: mdata should have been consumed"
| .proj .. => throwError "MLemmaInst.matchConstInst :: Projections should have been turned into ordinary expressions"
| _ => return HashSet.empty

-- Given a LemmaInst `li` and a ConstInst `ci`, try to match all subexpressions
--   of `li` against `ci`
def LemmaInst.matchConstInst (ci : ConstInst) (li : LemmaInst) : MetaM (HashSet LemmaInst) :=
  Meta.withNewMCtxDepth do
    let (_, _, mi) ← MLemmaInst.ofLemmaInst li
    MLemmaInst.matchConstInst ci mi mi.type

-- Test whether a lemma is type monomorphic && universe monomorphic
--   By universe monomorphic we mean `lem.params = #[]`
-- We also require that all instance arguments (argument whose type
--   is a class) are instantiated. If all dependent arguments are
--   instantiated, but some instance arguments are not instantiated,
--   we will try to synthesize the instance arguments
def LemmaInst.monomorphic? (li : LemmaInst) : MetaM (Option LemmaInst) := do
  if li.params.size != 0 then
    return .none
  if !(← Expr.isMonomorphicFact li.type) then
    return .none
  Meta.withNewMCtxDepth do
    let (_, mvars, mi) ← MLemmaInst.ofLemmaInst li
    for mvar in mvars do
      let mvarTy ← instantiateMVars (← Meta.inferType mvar)
      if let .some _ ← Meta.isClass? mvarTy then
        let .some inst ← Meta.trySynthInstance mvarTy
          | return .none
        match mvar with
        | .mvar id => id.assign inst
        | _ => throwError "LemmaInst.monomorphic? :: Unexpected error"
    LemmaInst.ofMLemmaInst mi

abbrev LemmaInsts := Array LemmaInst

def LemmaInsts.newInst? (lis : LemmaInsts) (li : LemmaInst) : MetaM Bool := do
  for li' in lis do
    if ← li'.equivQuick li then
      return false
  return true

/-
  Monomorphization works as follows:
  (1) Compute the number of `∀` binders for each input assumption.
      They form the initial elements of `liArr`
  (2) Scan through all assumptions to find subterms that are
      valid instances of constants (dependent arguments fully
      instantiated). They form the initial elements of `ciMap`
      and `activeCi`
  (3) Repeat:
      · Dequeue an element `(name, n)` from `activeCi`
      · For each element `ais : LemmaInsts` in `liArr`,
        for each expression `e` in `ais`, traverse `e` to
        find applications `app := name ...` of constant `name`.
        Try unifying `app` with `ciMap[name][n].snd`.
        If we get a new instance `i` of an assumption (which means
        that its `type` is not defeq to any existing ones in `ais`)
        · We add `i` to `ais`. 
        · We traverse `i` to collect instances of constants.
          If we find an instance `ci` of constant `name'`, we
          first look at `ciMap[name']` to see whether it's
          a new instance. If it's new, we add it to `ciMap`
          and `activeCi`.
-/
structure State where
  -- The `Expr` is the fingerprint of the `ConstInst`
  ciMap    : HashMap Expr ConstInsts := HashMap.empty
  -- The `Expr` is the fingerprint of the `ConstInst`
  activeCi : Std.Queue (Expr × Nat)  := Std.Queue.empty
  -- During initialization, we supply an array `lemmas` of lemmas
  --   `liArr[i]` are instances of `lemmas[i]`.
  lisArr    : Array LemmaInsts        := #[]

abbrev MonoM := StateRefT State MetaM

#genMonadState MonoM

/-
  Returns:
  1. Whether canonicalization is successful / Whether the constant is not new
  2. `(ciMap.find? ci.name).getD #[]`
  3. Canonicalized ConstInst
-/
def CiMap.canonicalize? (ciMap : HashMap Expr ConstInsts) (ci : ConstInst) :
  MetaM (Bool × ConstInsts × ConstInst) := do
  match ciMap.find? ci.fingerPrint with
  | .some insts =>
    match ← insts.canonicalize? ci with
    | .some ci' => return (true, insts, ci')
    | .none => return (false, insts, ci)
  | .none => return (false, #[], ci)

-- Process a potentially new ConstInst. If it's new, return its index
--   in the corresponding `ConstInsts` array. If it's not new, return
--   `.none`.
def processConstInst (ci : ConstInst) : MonoM Unit := do
  let (old?, insts, ci) ← CiMap.canonicalize? (← getCiMap) ci
  if old? then
    return
  trace[auto.mono.printConstInst] "New {ci}"
  setCiMap ((← getCiMap).insert ci.fingerPrint (insts.push ci))
  -- Do not match against ConstInsts that do not have instDepArgs
  if ci.instDepArgs.size == 0 then
    return
  -- Do not match against `=` and `∃`
  -- If some polymorphic argument of the a theorem only occurs
  --   as the first argument of `=` or `∃`, the theorem is probably
  --   implied by the axioms of higher order logic, e.g.
  -- `Eq.trans : ∀ {α} (x y z : α), x = y → y = z → x = z`
  if ci.head.isNamedConst ``Exists || ci.head.isNamedConst ``Eq then
    return
  -- Insert `ci` into `activeCi` so that we can later match on it
  setActiveCi ((← getActiveCi).enqueue (ci.fingerPrint, insts.size))

def initializeMonoM (lemmas : Array Lemma) : MonoM Unit := do
  let lemmaInsts ← liftM <| lemmas.mapM (fun lem => do
    let li ← LemmaInst.ofLemma lem
    trace[auto.mono.printLemmaInst] "New {li}"
    return li)
  let lemmaInsts := lemmaInsts.map (fun x => #[x])
  setLisArr lemmaInsts
  for lem in lemmas do
    let cis ← collectConstInsts lem.params lem.type
    for ci in cis do
      processConstInst ci

def dequeueActiveCi? : MonoM (Option (Expr × Nat)) := do
  match (← getActiveCi).dequeue? with
  | .some (elem, ci') =>
    setActiveCi ci'
    return .some elem
  | .none => return .none

def lookupActiveCi! (fgp : Expr) (idx : Nat) : MonoM ConstInst := do
  let .some cis := (← getCiMap).find? fgp
    | throwError "lookupActiveCi :: Unknown CiHead {fgp}"
  let .some ci := cis[idx]?
    | throwError "lookupActiveCi :: Index {idx} out of bound"
  return ci

def saturationThresholdReached? (cnt : Nat) : CoreM Bool := do
  let threshold := auto.mono.saturationThreshold.get (← getOptions)
  if cnt > threshold then
    trace[auto.mono] "Monomorphization saturation :: Threshold {threshold} reached"
    return true
  else
    return false

def saturate : MonoM Unit := do
  let mut cnt := 0
  while true do
    cnt := cnt + 1
    if (← saturationThresholdReached? cnt) then
      return
    match ← dequeueActiveCi? with
    | .some (name, cisIdx) =>
      let ci ← lookupActiveCi! name cisIdx
      let lisArr ← getLisArr
      trace[auto.mono] "Matching against {ci}"
      for (lis, idx) in lisArr.zip ⟨List.range lisArr.size⟩ do
        cnt := cnt + 1
        let mut newLis := lis
        for li in lis do
          cnt := cnt + 1
          let matchLis := (← LemmaInst.matchConstInst ci li).toArray
          for matchLi in matchLis do
            -- `matchLi` is a result of matching a subterm of `li` against `ci`
            cnt := cnt + 1
            if (← saturationThresholdReached? cnt) then
              return
            let new? ← newLis.newInst? matchLi
            -- A new instance of an assumption
            if new? then
              trace[auto.mono.printLemmaInst] "New {matchLi}"
              newLis := newLis.push matchLi
              let newCis ← collectConstInsts matchLi.params matchLi.type
              for newCi in newCis do
                processConstInst newCi
        setLisArr ((← getLisArr).set! idx newLis)
    | .none =>
      trace[auto.mono] "Monomorphization Saturated after {cnt} small steps"
      return

-- Remove non-monomorphic lemma instances
def postprocessSaturate : MonoM Unit := do
  let lisArr ← getLisArr
  let lisArr ← liftM <| lisArr.mapM (fun lis => lis.filterMapM LemmaInst.monomorphic?)
  setLisArr lisArr

namespace FVarRep
  
  structure State where
    bfvars  : Array FVarId             := #[]
    ffvars  : Array FVarId             := #[]
    exprMap : HashMap Expr FVarId      := {}
    ciMap   : HashMap Expr ConstInsts  
    ciIdMap : HashMap ConstInst FVarId := {}
  
  abbrev FVarRepM := StateRefT State MetaState.MetaStateM
  
  #genMonadState FVarRepM

  -- Similar to `Monomorphization.processConstInst`
  def processConstInst (ci : ConstInst) : FVarRepM Unit := do
    let (old?, insts, ci) ← MetaState.runMetaM <| CiMap.canonicalize? (← getCiMap) ci
    if old? then
      return
    trace[auto.mono.printConstInst] "New {ci}"
    setCiMap ((← getCiMap).insert ci.fingerPrint (insts.push ci))

  def ConstInst2FVarId (ci : ConstInst) : FVarRepM FVarId := do
    let ciMap ← FVarRep.getCiMap
    let ci ← MetaState.runMetaM (do
      match ← CiMap.canonicalize? ciMap ci with
      | (true, _, ci') => return ci'
      | _ => throwError "ConstInst2FVarId :: Cannot find canonicalized instance of {ci}")
    let ciIdMap ← FVarRep.getCiIdMap
    match ciIdMap.find? ci with
    | .some fid => return fid
    | .none => do
      let fvarId ← mkFreshFVarId
      setCiIdMap ((← getCiIdMap).insert ci fvarId)
      let userName := (`cifvar).appendIndexAfter (← getCiIdMap).size
      let cie ← MetaState.runMetaM ci.toExpr
      let city ← instantiateMVars (← MetaState.inferType cie)
      MetaState.mkLetDecl fvarId userName city cie
      setFfvars ((← getFfvars).push fvarId)
      return fvarId
  
  def UnknownExpr2FVarId (e : Expr) : FVarRepM FVarId := do
    for (e', fid) in (← getExprMap).toList do
      if ← MetaState.runMetaM (Meta.withNewMCtxDepth <| Meta.isDefEq e e') then
        return fid
    let fvarId ← mkFreshFVarId
    setExprMap ((← getExprMap).insert e fvarId)
    let userName := (`exfvar).appendIndexAfter (← getExprMap).size
    let ety ← instantiateMVars (← MetaState.inferType e)
    MetaState.mkLetDecl fvarId userName ety e
    setFfvars ((← getFfvars).push fvarId)
    return fvarId

  -- Since we're now dealing with monomorphized lemmas, there are no
  --   bound level parameters
  partial def replacePolyWithFVar : Expr → FVarRepM Expr
  | .lam name ty body binfo => do
    let fvarId ← mkFreshFVarId
    MetaState.mkLocalDecl fvarId name ty binfo
    setBfvars ((← getBfvars).push fvarId)
    let b' ← replacePolyWithFVar (body.instantiate1 (.fvar fvarId))
    MetaState.runMetaM <| Meta.mkLambdaFVars #[.fvar fvarId] b'
  -- Turns `∀` into `Embedding.forallF`, `→` into `Embedding.ImpF`
  | .forallE name ty body binfo => do
    let tysort ← MetaState.runMetaM (do normalizeType (← Meta.inferType ty))
    let .sort tylvl := tysort
      | throwError "replacePolyWithFVar :: {tysort} is not a sort"
    let fvarId ← mkFreshFVarId
    MetaState.mkLocalDecl fvarId name ty binfo
    setBfvars ((← getBfvars).push fvarId)
    let body' := body.instantiate1 (.fvar fvarId)
    let bodysort ← MetaState.runMetaM <| do normalizeType (← Meta.inferType body')
    let .sort bodylvl := bodysort
      | throwError "replacePolyWithFVars :: Unexpected error"
    let bodyrep ← replacePolyWithFVar body'
    if body.hasLooseBVar 0 ∨ !(← MetaState.isLevelDefEq tylvl .zero) ∨ !(← MetaState.isLevelDefEq bodylvl .zero) then
      let forallFun := Expr.app (.const ``forallF [tylvl, bodylvl]) ty
      addForallImpFInst forallFun
      let forallFunId ← replacePolyWithFVar forallFun
      return .app forallFunId (← MetaState.runMetaM <| Meta.mkLambdaFVars #[.fvar fvarId] bodyrep)
    else
      let impFun := Expr.const ``ImpF [.zero, .zero]
      addForallImpFInst impFun
      return .app (.app impFun (← replacePolyWithFVar ty)) bodyrep
  | e@(.app ..) => do
    -- Head is bvar
    if let .fvar id := e.getAppFn then
      if ((← getBfvars).contains id) then
        let ciArgs ← e.getAppArgs.mapM replacePolyWithFVar
        return mkAppN (.fvar id) ciArgs
    -- Head is fvar/mvar/const
    let eabst := e.abstract ((← getBfvars).map .fvar)
    if let .some ci ← MetaState.runMetaM (ConstInst.ofExpr? #[] eabst) then
      let ciId ← ConstInst2FVarId ci
      let ciArgs ← ConstInst.getOtherArgs ci e
      let ciArgs ← ciArgs.mapM replacePolyWithFVar
      return mkAppN (.fvar ciId) ciArgs
    Expr.fvar <$> UnknownExpr2FVarId e
  | e@(.sort _) => return e
  | e@(.lit _) => return e
  | e => do
    if let .fvar id := e then
      if (← getBfvars).contains id then
        return .fvar id
    if let .some ci ← MetaState.runMetaM (ConstInst.ofExpr? #[] e) then
      let ciId ← ConstInst2FVarId ci
      return .fvar ciId
    Expr.fvar <$> UnknownExpr2FVarId e
where addForallImpFInst (e : Expr) : FVarRepM Unit := do
  let eabst := e.abstract ((← getBfvars).map Expr.fvar)
  match ← MetaState.runMetaM (ConstInst.ofExpr? #[] eabst) with
  | .some ci => processConstInst ci
  | .none => trace[auto.mono] "Warning, {e} is not a valid instance of `forallF` or `ImpF`"

end FVarRep

def monomorphize (lemmas : Array Lemma) (k : Reif.State → MetaM α) : MetaM α := do
  let startTime ← IO.monoMsNow
  let monoMAction : MonoM Unit := (do
    initializeMonoM lemmas
    saturate
    postprocessSaturate
    trace[auto.mono] "Monomorphization took {(← IO.monoMsNow) - startTime}ms")
  let (_, monoSt) ← monoMAction.run {}
  let fvarRepMAction : FVarRep.FVarRepM (Array Reif.UMonoFact) := (do
    let lis := monoSt.lisArr.concatMap id
    lis.mapM (fun li => do
      return ⟨li.proof, ← FVarRep.replacePolyWithFVar li.type⟩))
  let metaStateMAction : MetaState.MetaStateM (Array FVarId × Reif.State) := (do
    let (ufacts, s) ← fvarRepMAction.run { ciMap := monoSt.ciMap }
    for (proof, ty) in ufacts do
      trace[auto.mono] "Monomorphized :: {proof} : {ty}"
    let exlis := s.exprMap.toList.map (fun (e, id) => (id, e))
    let cilis ← s.ciIdMap.toList.mapM (fun (ci, id) => do return (id, ← MetaState.runMetaM ci.toExpr))
    let polyVal := HashMap.ofList (exlis ++ cilis)
    return (s.ffvars, Reif.State.mk s.ffvars ufacts polyVal))
  MetaState.runWithIntroducedFVars metaStateMAction k

end Auto.Monomorphization