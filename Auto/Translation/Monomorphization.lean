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

register_option auto.mono.instantiateInstanceArgs : Bool := {
  defValue := true
  descr := "Whether to force instantiation of instance arguments of constants"
}

namespace Auto.Monomorphization
open Embedding

def instInst? : CoreM Bool := do return auto.mono.instantiateInstanceArgs.get (← getOptions)

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
  name       : Name
  levels     : Array Level
  argsInst   : Array Expr
  argsToInst : Array Nat
  deriving Hashable, BEq

instance : ToMessageData ConstInst where
  toMessageData ci := MessageData.compose
    m!"ConstInst ⦗⦗ {Expr.const ci.name ci.levels.data}" (.compose
        m!" " (.compose
          (MessageData.intercalate " " (ci.argsInst.data.map (fun e => m!"({e})")))
            m!" ⦘⦘"))

def ConstInst.equiv (ci₁ ci₂ : ConstInst) : MetaM Bool := Meta.withNewMCtxDepth <| do
  let ⟨name₁, levels₁, argsInst₁, idx₁⟩ := ci₁
  let ⟨name₂, levels₂, argsInst₂, idx₂⟩ := ci₂
  if name₁ != name₂ || levels₁.size != levels₂.size ||
      argsInst₁.size != argsInst₂.size || idx₁ != idx₂ then
    throwError "ConstInst.equiv :: Unexpected error"
  for (param₁, param₂) in levels₁.zip levels₂ do
    if !(← Meta.isLevelDefEq param₁ param₂) then
      return false
  for (arg₁, arg₂) in argsInst₁.zip argsInst₂ do
    if !(← Meta.isDefEq arg₁ arg₂) then
      return false
  return true

def ConstInst.matchExpr (e : Expr) (ci : ConstInst) : MetaM Bool := do
  let fn := e.getAppFn
  let .const name lvls := fn
    | return false
  if name != ci.name then
    return false
  if lvls.length != ci.levels.size then
    throwError "ConstInst.matchExpr :: Unexpected error"
  for (lvl, lvl') in lvls.zip ci.levels.data do
    if !(← Meta.isLevelDefEq lvl lvl') then
      return false
  let argsToInst := ci.argsToInst
  if argsToInst.size != ci.argsInst.size then
    throwError "ConstInst.matchExpr :: Unexpected error"
  let args := e.getAppArgs
  for (idx, ciarg) in argsToInst.zip ci.argsInst do
    let .some arg := args[idx]?
      | return false
    if !(← Meta.isDefEq arg ciarg) then
      return false
  return true

/-
  Given an hypothesis `t`, we will traverse the hypothesis to find
    instances of polymorphic constants
  · Binders of the hypothesis are not introduced as fvars/mvars, so
    they remain loose bound variables inside the body
  · `param` records universe level parameters of the hypothesis are
  So, the criterion that an expression `e` is a valid instance is that
  · All argsToInst are applied
  · No loose bound variables in argsToInst
  · The expression does not contain level parameters in `params`
-/
def ConstInst.ofExpr?Poly (params : Array Name) (e : Expr) : CoreM (Option ConstInst) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const name lvls := fn
    | return .none
  let paramSet := HashSet.empty.insertMany params
  if let .some _ := Expr.findParam? (fun n => paramSet.contains n) e then
    return .none
  -- Do not record instances of a constant with attribute `instance`
  if (← Meta.isInstance name) && !(auto.mono.recordInstInst.get (← getOptions)) then
    return .none
  -- Refer to `auto.mono.instantiateInstanceArgs`
  let depargIndexes := if (← instInst?) then (← Expr.constInstDepArgs name) else (← Expr.constDepArgs name)
  -- Do not record instances of monomorphic constants
  if depargIndexes.size == 0 && lvls.length == 0 then
    return none
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
  return some ⟨name, ⟨lvls⟩, argsInst, depargIndexes⟩

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

def ConstInst.toExpr (ci : ConstInst) : CoreM Expr := do
  let .some decl := (← getEnv).find? ci.name
    | throwError "ConstInst.toExpr :: Unknown constant {ci.name}"
  let type := decl.type
  let nargs := (Nat.succ <$> ci.argsToInst[ci.argsToInst.size - 1]?).getD 0
  let mut args : Array (Option Expr) := (Array.mk (List.range nargs)).map (fun n => .none)
  for (arg, idx) in ci.argsInst.zip ci.argsToInst do
    args := args.setD idx (.some arg)
  let .some ret := ConstInst.toExprAux args.data [] (.const ci.name ci.levels.data) type
    | throwError "ConstInst.toExpr :: Unexpected error"
  return ret

-- Precondition : `.some ci == ← ConstInst.ofExpr?Poly e`
-- Returns the list of non-dependent arguments in `e.getAppArgs`
def ConstInst.getNonargsInst (ci : ConstInst) (e : Expr) : CoreM (Array Expr) := do
  let mut args := e.getAppArgs.map Option.some
  for idx in ci.argsToInst do
    args := args.setD idx .none
  let mut ret := #[]
  for arg? in args do
    if let .some arg := arg? then
      ret := ret.push arg
  return ret

private partial def collectConstInsts (params : Array Name) : Expr → MetaM (Array ConstInst)
| e@(.const ..) => do
  match ← ConstInst.ofExpr?Poly params e with
  | .some ci => return #[ci]
  | .none => return #[]
| e@(.app ..) => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let insts := (← (args.push fn).mapM (collectConstInsts params)).concatMap id
  match ← ConstInst.ofExpr?Poly params e with
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

-- Array of instances of a polymorphic constant
abbrev ConstInsts := Array ConstInst

-- Given an array `cis` and a potentially new instance `ci`,
--   determine whether `ci` is a new instance.
-- · If `ci` is new, add it to `ConstInsts` and return `true`
-- · If `ci` is not new, return the original `ConstInsts` and `false`
def ConstInsts.newInst? (cis : ConstInsts) (ci : ConstInst) : MetaM Bool := do
  for ci' in cis do
    if ← ci'.equiv ci then
      return false
  return true

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
    let mi ← MLemmaInst.ofLemmaInst li
    MLemmaInst.matchConstInst ci mi mi.type

-- Test whether a lemma is type monomorphic && universe monomorphic
--   By universe monomorphic we mean `lem.params = #[]`
-- If `auto.mono.instantiateInstanceArgs` is set to `true`, we
--   also require that all instance arguments (argument whose type
--   is a class) are instantiated.
def LemmaInst.monomorphic (lem : LemmaInst) : MetaM Bool := do
  if lem.params.size != 0 then
    return false
  if !(← Expr.isMonomorphicFact lem.type) then
    return false
  if auto.mono.instantiateInstanceArgs.get (← getOptions) then
    (Meta.forallTelescope lem.type fun xs _ => do
      for x in xs do
        let ty ← x.fvarId!.getType
        if let .some _ ← Meta.isClass? ty then
          return false
      return true)
  else
    return true

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
  ciMap    : HashMap Name ConstInsts := HashMap.empty
  activeCi : Std.Queue (Name × Nat)  := Std.Queue.empty
  -- During initialization, we supply an array `lemmas` of lemmas
  --   `liArr[i]` are instances of `lemmas[i]`.
  lisArr    : Array LemmaInsts        := #[]

abbrev MonoM := StateRefT State MetaM

#genMonadState MonoM

-- Process a potentially new ConstInst. If it's new, return its index
--   in the corresponding `ConstInsts` array. If it's not new, return
--   `.none`.
def processConstInst (ci : ConstInst) : MonoM Unit := do
  let cont (ci : ConstInst) (insts : Array ConstInst) := (do
      trace[auto.mono.printConstInst] "New {ci}"
      setCiMap ((← getCiMap).insert ci.name (insts.push ci))
      -- Do not match against ConstInsts that are universe polymorphic
      --   but has no argsInst
      if ci.argsToInst.size == 0 then
        return
      -- Do not match against `=` and `∃`
      -- If some polymorphic argument of the a theorem only occurs
      --   as the first argument of `=` or `∃`, the theorem is probably
      --   implied by the axioms of higher order logic, e.g.
      -- `Eq.trans : ∀ {α} (x y z : α), x = y → y = z → x = z`
      if ci.name == ``Exists || ci.name == ``Eq then
        return
      -- Insert `ci` into `activeCi` so that we can later match on it
      setActiveCi ((← getActiveCi).enqueue (ci.name, insts.size))
    )
  match (← getCiMap).find? ci.name with
  | .some insts =>
    let new? ← insts.newInst? ci
    if new? then
      cont ci insts
  | .none =>
    cont ci #[]

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

def dequeueActiveCi? : MonoM (Option (Name × Nat)) := do
  match (← getActiveCi).dequeue? with
  | .some (elem, ci') =>
    setActiveCi ci'
    return .some elem
  | .none => return .none

def lookupActiveCi! (name : Name) (idx : Nat) : MonoM ConstInst := do
  let .some cis := (← getCiMap).find? name
    | throwError "lookupActiveCi :: Unknown constant name {name}"
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

-- Since we're now dealing with monomorphized lemmas, there are no
--   bound level parameters
private partial def replaceForall (lctx : Array Expr) : Expr → MonoM Expr
| .forallE name ty body binfo => do
  let tylvl := (← instantiateMVars (← Meta.inferType ty)).sortLevel!
  let (bodysort, bodyrep) ← Meta.withLocalDecl name binfo ty fun fvar => do
    let body' := body.instantiate1 fvar
    let bodysort ← Meta.inferType body'
    let bodyrep ← replaceForall (lctx.push fvar) body'
    return (bodysort, ← Meta.mkLambdaFVars #[fvar] bodyrep)
  let bodylvl := (← instantiateMVars bodysort).sortLevel!
  if body.hasLooseBVar 0 ∨ !(← Meta.isLevelDefEq tylvl .zero) ∨ !(← Meta.isLevelDefEq bodylvl .zero) then
    let forallFun := Expr.app (.const ``forallF [tylvl, bodylvl]) ty
    addForallImpFInst lctx forallFun
    return .app forallFun bodyrep
  else
    let impFun := Expr.const ``ImpF [tylvl, bodylvl]
    addForallImpFInst lctx impFun
    return .app (.app impFun (← replaceForall lctx ty)) bodyrep
| .lam name ty body binfo =>
  Meta.withLocalDecl name binfo ty fun fvar => do
    let b' ← replaceForall (lctx.push fvar) (body.instantiate1 fvar)
    Meta.mkLambdaFVars #[fvar] b'
| .app fn arg => do
  let fn' ← replaceForall lctx fn
  let arg' ← replaceForall lctx arg
  return .app fn' arg'
| e => return e
where addForallImpFInst (lctx : Array Expr) (e : Expr) : MonoM Unit := do
  let eabst := e.abstract lctx
  match ← ConstInst.ofExpr?Poly #[] eabst with
  | .some ci => processConstInst ci
  | .none => trace[auto.mono] "replaceForall :: Warning, {e} is not a valid instance of `forallF` or `ImpF`"

/-
  · Step 1 : Remove non-monomorphic lemma instances
  · Step 2 :
    · Turn `∀` into `Embedding.forallF`, `→` into `Embedding.impF`
    · Record all instances of `Embedding.impF` and `Embedding.forallF`
      into `ciMap`
-/
-- Turns `∀` into `Embedding.forallF`, `→` into `Embedding.impF`
def postprocessSaturate : MonoM Unit := do
  let lisArr ← getLisArr
  let lisArr ← liftM <| lisArr.mapM (fun lis => lis.filterM LemmaInst.monomorphic)
  let lisArr ← lisArr.mapM (fun lis => lis.mapM (fun li => do
    if li.params.size != 0 then
      throwError "postprocessSaturate :: Unexpected error"
    let type' ← replaceForall #[] li.type
    return {li with type := type'}))
  setLisArr lisArr

namespace FVarRep
  
  structure State where
    bfvars  : Array FVarId             := #[]
    ffvars  : Array FVarId             := #[]
    exprMap : HashMap Expr FVarId      := {}
    ciMap   : HashMap ConstInst FVarId := {}
  
  abbrev FVarRepM := StateRefT State MetaState.MetaStateM
  
  #genMonadState FVarRepM
  
  def ConstInst2FVarId (ci : ConstInst) : FVarRepM FVarId := do
    let ciMap ← FVarRep.getCiMap
    match ciMap.find? ci with
    | .some fid => return fid
    | .none => do
      let fvarId ← mkFreshFVarId
      setCiMap ((← getCiMap).insert ci fvarId)
      let userName := (`cifvar).appendIndexAfter (← getCiMap).size
      let cie ← ci.toExpr
      let city ← MetaState.runMetaM (Meta.inferType cie)
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
    let ety ← MetaState.runMetaM (Meta.inferType e)
    MetaState.mkLetDecl fvarId userName ety e
    setFfvars ((← getFfvars).push fvarId)
    return fvarId

  -- Auxiliary function for `replacePolyWithFVar`
  private def monoExprApp? (e : Expr) : MetaM Bool := do
    let fn := e.getAppFn
    let fnTy ← Meta.inferType fn
    let argsToInst := if (← instInst?) then Expr.instDepArgs fnTy else Expr.depArgs fnTy
    return argsToInst.size == 0

  partial def replacePolyWithFVar : Expr → FVarRepM Expr
  | .lam name ty body binfo => do
    let fvarId ← mkFreshFVarId
    MetaState.mkLocalDecl fvarId name ty binfo
    setBfvars ((← getBfvars).push fvarId)
    let b' ← replacePolyWithFVar (body.instantiate1 (.fvar fvarId))
    MetaState.runMetaM <| Meta.mkLambdaFVars #[.fvar fvarId] b'
  | e@(.fvar id) => do
    if (← getBfvars).contains id then
      return .fvar id
    else
      Expr.fvar <$> UnknownExpr2FVarId e
  | e@(.const ..) => do
    if let .some ci ← ConstInst.ofExpr?Poly #[] e then
      let ciId ← ConstInst2FVarId ci
      return .fvar ciId
    Expr.fvar <$> UnknownExpr2FVarId e
  | e@(.app ..) => do
    let eabst := e.abstract ((← getBfvars).map .fvar)
    if let .some ci ← ConstInst.ofExpr?Poly #[] eabst then
      let ciId ← ConstInst2FVarId ci
      let ciArgs ← ConstInst.getNonargsInst ci e
      let ciArgs ← ciArgs.mapM replacePolyWithFVar
      return mkAppN (.fvar ciId) ciArgs
    if ← MetaState.runMetaM (monoExprApp? e) then
      let fn ← replacePolyWithFVar e.getAppFn
      let args ← e.getAppArgs.mapM replacePolyWithFVar
      return mkAppN fn args
    Expr.fvar <$> UnknownExpr2FVarId e
  | e => Expr.fvar <$> UnknownExpr2FVarId e

end FVarRep

def monomorphize (lemmas : Array Lemma) (k : Reif.State → MetaM α) : MetaM α := do
  let startTime ← IO.monoMsNow
  let monoMAction : MonoM Unit := (do
    initializeMonoM lemmas
    saturate
    postprocessSaturate)
  trace[auto.mono] "Monomorphization took {(← IO.monoMsNow) - startTime}ms"
  let (_, monoSt) ← monoMAction.run {}
  let fvarRepMAction : FVarRep.FVarRepM (Array Reif.UMonoFact) := (do
    let lis := monoSt.lisArr.concatMap id
    lis.mapM (fun li => do
      trace[auto.mono] "6 :: Replacing {li.type}"
      return ⟨li.proof, ← FVarRep.replacePolyWithFVar li.type⟩))
  let metaStateMAction : MetaState.MetaStateM (Array FVarId × Reif.State) := (do
    let (ufacts, s) ← fvarRepMAction.run {}
    let exlis := s.exprMap.toList.map (fun (e, id) => (id, e))
    let cilis ← s.ciMap.toList.mapM (fun (ci, id) => do return (id, ← ci.toExpr))
    let polyVal := HashMap.ofList (exlis ++ cilis)
    return (s.ffvars, Reif.State.mk s.ffvars ufacts polyVal))
  MetaState.runWithIntroducedFVars metaStateMAction k

end Auto.Monomorphization