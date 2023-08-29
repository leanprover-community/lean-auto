import Lean
import Auto.Embedding.Lift
import Auto.Translation.Assumptions
import Auto.Lib.ExprExtra
import Auto.Lib.MonadUtils
import Auto.Lib.Containers
open Lean

initialize
  registerTraceClass `auto.mono
  registerTraceClass `auto.mono.printLemmaInst
  registerTraceClass `auto.mono.printConstInst

register_option auto.mono.saturationThreshold : Nat := {
  defValue := 100
  descr := "Threshold for number of potentially new lemma" ++
    " instances generated during the saturation loop of monomorphization"
}

namespace Auto.Monomorphization
open Embedding

/-
  If a constant `c` is of type `∀ (xs : αs), t`,
    then its valid instance will be `c` with all of its
    universe levels and dependent arguments instantiated.
    So, we record the instantiation of universe levels
    and dependent arguments.
  
  As to monomorphization, we will not record instances
    of monomorphic constants. We will also not record
    instances of `∃` and `Eq` because they're constructs
    in HOL.
-/
structure ConstInst where
  name    : Name
  levels  : Array Level
  depargs : Array Expr

instance : ToMessageData ConstInst where
  toMessageData ci := MessageData.compose
    m!"ConstInst ⦗⦗ {Expr.const ci.name ci.levels.data}" (.compose
        m!" " (.compose
          (MessageData.intercalate " " (ci.depargs.data.map (fun e => m!"({e})")))
            m!" ⦘⦘"))

def ConstInst.equiv (ci₁ ci₂ : ConstInst) : MetaM Bool := Meta.withNewMCtxDepth <| do
  let ⟨name₁, levels₁, depargs₁⟩ := ci₁
  let ⟨name₂, levels₂, depargs₂⟩ := ci₂
  if name₁ != name₂ || levels₁.size != levels₂.size || depargs₁.size != depargs₂.size then
    throwError "ConstInst.equiv :: Unexpected error"
  for (param₁, param₂) in levels₁.zip levels₂ do
    if !(← Meta.isLevelDefEq param₁ param₂) then
      return false
  for (arg₁, arg₂) in depargs₁.zip depargs₂ do
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
  let depargsIdx ← Expr.constDepArgs ci.name
  if depargsIdx.size != ci.depargs.size then
    throwError "ConstInst.matchExpr :: Unexpected error"
  let args := e.getAppArgs
  for (idx, ciarg) in depargsIdx.zip ci.depargs do
    let .some arg := args[idx]?
      | return false
    if !(← Meta.isDefEq arg ciarg) then
      return false
  return true

-- Given an hypothesis `t`, we will traverse the hypothesis
--   to find instances of a constant. Binders of the hypothesis
--   are not introduced as fvars/mvars, so they remain loose
--   bound variables inside the body.
-- So, the criterion that an expression `e` is a valid instance
--   is that, all dependent arguments are applied, and no
--   dependent argument contains `ExprMVar`s.
def ConstInst.ofExpr? (e : Expr) : CoreM (Option ConstInst) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const name lvls := fn
    | return .none
  -- Do not record instances of `∃` or `Eq`
  if name == ``Exists || name == ``Eq then
    return none
  -- Do not record instances of monomorphic constants
  let depargIndexes ← Expr.constDepArgs name
  if depargIndexes.size == 0 then
    return none
  let lastDeparg := depargIndexes[depargIndexes.size - 1]!
  if args.size ≤ lastDeparg then
    return none
  let mut depargs := #[]
  for idx in depargIndexes do
    let arg := args[idx]!
    if arg.hasLooseBVars then
      return none
    depargs := depargs.push arg
  return some ⟨name, ⟨lvls⟩, depargs⟩

partial def collectConstInsts : Expr → CoreM (Array ConstInst)
-- Note that we never need to inspect `.const Name (ListLevel)`,
--  because either the constant is monomorphic or it's not
--  applied (thus its dependent arguments are not instantiated)
| e@(.app ..) => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let insts := (← (args.push fn).mapM collectConstInsts).concatMap id
  match ← ConstInst.ofExpr? e with
  | .some ci => return insts.push ci
  | .none => return insts
| .lam _ ty body bi => do
  let insts ← collectConstInsts body
  -- Do not look into instance binders
  if bi.isInstImplicit then
    return insts
  else
    return insts ++ (← collectConstInsts ty)
| .forallE _ ty body bi => do
  let insts ← collectConstInsts body
  -- Do not look into instance binders
  if bi.isInstImplicit then
    return insts
  else
    return insts ++ (← collectConstInsts ty)
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
| .lam name ty body bi => Meta.withLocalDecl name bi ty fun _ => do
    let tyInst ← MLemmaInst.matchConstInst ci mi ty
    let bodyInst ← MLemmaInst.matchConstInst ci mi body
    return mergeHashSet tyInst bodyInst
| .letE .. => throwError "MLemmaInst.matchConstInst :: Let-expressions should have been reduced"
| .mdata .. => throwError "MLemmaInst.matchConstInst :: mdata should have been consumed"
| .proj .. => throwError "MLemmaInst.matchConstInst :: Projections should have been turned into ordinary expressions"
| _ => return HashSet.empty

-- Given a LemmaInst `li` and a ConstInst `ci`, try to match all subexpressions
--   of `li` against `ci`
def LemmaInst.matchConstInst (ci : ConstInst) (li : LemmaInst) : MetaM (HashSet LemmaInst) := do
  let s ← saveState
  let ret ← Meta.withNewMCtxDepth do
    let mi ← MLemmaInst.ofLemmaInst li
    MLemmaInst.matchConstInst ci mi mi.type
  restoreState s
  return ret

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
          first look at `cdepargs[name']` to see whether it's
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
  match (← getCiMap).find? ci.name with
  | .some insts =>
    let new? ← insts.newInst? ci
    if new? then
      trace[auto.mono.printConstInst] "New {ci}"
      setCiMap ((← getCiMap).insert ci.name (insts.push ci))
      setActiveCi ((← getActiveCi).enqueue (ci.name, insts.size))
  | .none =>
    trace[auto.mono.printConstInst] "New {ci}"
    setCiMap ((← getCiMap).insert ci.name #[ci])
    setActiveCi ((← getActiveCi).enqueue (ci.name, 0))

def initializeMonoM (lemmas : Array Lemma) : MonoM Unit := do
  let lemmaInsts ← liftM <| lemmas.mapM LemmaInst.ofLemma
  let lemmaInsts := lemmaInsts.map (fun x => #[x])
  setLisArr lemmaInsts
  for lem in lemmas do
    let cis ← collectConstInsts lem.type
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
              let newCis ← collectConstInsts matchLi.type
              for newCi in newCis do
                processConstInst newCi
        setLisArr ((← getLisArr).set! idx newLis)
    | .none =>
      trace[auto.mono] "Monomorphization Saturated after {cnt} small steps"
      return

def monomorphize (lemmas : Array Lemma) : MetaM State := do
  let startTime ← IO.monoMsNow
  let (_, ret) ← (do
    initializeMonoM lemmas
    saturate).run {}
  trace[auto.mono] "Monomorphization took {(← IO.monoMsNow) - startTime}ms"
  return ret

-- For test purpose
register_option testCollectPolyLog : Bool := {
  defValue := true
  descr    := "For test"
}

-- For test purpose
partial def polylogs : Expr → MetaM (HashSet Expr)
| e@(.app (.const ``Eq _) _) => return HashSet.empty.insert e
| e@(.app (.const ``Exists _) _) => return HashSet.empty.insert e
| .forallE name ty body binfo => do
  let hs' ← polylogs (.lam name ty body binfo)
  let tylvl := (← instantiateMVars (← Meta.inferType ty)).sortLevel!
  let bodysort ← Meta.withLocalDecl name binfo ty fun fvar =>
    Meta.inferType (body.instantiate1 fvar)
  let bodylvl := (← instantiateMVars bodysort).sortLevel!
  if body.hasLooseBVar 0 ∨ !(← Meta.isLevelDefEq tylvl .zero) ∨ !(← Meta.isLevelDefEq bodylvl .zero)  then
    return hs'.insert (.app (.const ``forallF [tylvl, bodylvl]) ty)
  else
    return hs'.insert (.const ``ImpF [tylvl, bodylvl])
| .lam name ty body binfo => do
  let hty ← polylogs ty
  let hbody ← Meta.withLocalDecl name binfo ty fun fvar =>
    polylogs (body.instantiate1 fvar)
  return hbody.insertMany hty
| .app fn arg => do
  let fna ← polylogs fn
  let arga ← polylogs arg
  return fna.insertMany arga
| _ => return HashSet.empty

-- For test purpose
def addpolylog (e : Expr) (cont : HashMap Expr FVarId → MetaM α)
  (hmap : HashMap Expr FVarId) : MetaM α := do
  if hmap.contains e then
    cont hmap
  else
    let fvarid ← mkFreshId
    let name := "_pl_" ++ fvarid.toString
    Meta.withLetDecl name (← Meta.inferType e) e fun fvar =>
      cont (hmap.insert e fvar.fvarId!)

-- Temporary function
private def autometafind! [Hashable α] [BEq α] (hmap : HashMap α β) (x : α) : MetaM β := do
  if let .some b := hmap.find? x then
    return b
  else
    throwError "autometafind! :: Unfindable"

-- For test purpose
partial def replacepolylog (hmap : HashMap Expr FVarId) : Expr → MetaM Expr
| e@(.app (.const ``Eq _) _) => return .fvar (← autometafind! hmap e)
| e@(.app (.const ``Exists _) _) => return .fvar (← autometafind! hmap e)
| .forallE name ty body binfo => do
  let tylvl := (← instantiateMVars (← Meta.inferType ty)).sortLevel!
  let (bodysort, rep) ← Meta.withLocalDecl name binfo ty fun fvar => do
    let body' := body.instantiate1 fvar
    let bodysort ← Meta.inferType body'
    let bodyrep ← replacepolylog hmap body'
    return (bodysort, ← Meta.mkLambdaFVars #[fvar] bodyrep)
  let bodylvl := (← instantiateMVars bodysort).sortLevel!
  if body.hasLooseBVar 0 ∨ !(← Meta.isLevelDefEq tylvl .zero) ∨ !(← Meta.isLevelDefEq bodylvl .zero) then
    let forallFun := Expr.fvar (← autometafind! hmap (.app (.const ``forallF [tylvl, bodylvl]) ty))
    return .app forallFun rep
  else
    let impFun := Expr.fvar (← autometafind! hmap (.const ``ImpF [tylvl, bodylvl]))
    return .app (.app impFun (← replacepolylog hmap ty)) (← replacepolylog hmap body)
| .lam name ty body binfo =>
  Meta.withLocalDecl name binfo ty fun fvar => do
    let b' ← replacepolylog hmap (body.instantiate1 fvar)
    Meta.mkLambdaFVars #[fvar] b'
| .app fn arg => do
  let fn' ← replacepolylog hmap fn
  let arg' ← replacepolylog hmap arg
  return .app fn' arg'
| e => return e

-- For test purpose
def collectPolyLogAux (fact : Expr × Expr) {α : Type}
  (cont : HashMap Expr FVarId → Array (Expr × Expr) → MetaM α)
  (hmap₀ : HashMap Expr FVarId) (arr : Array (Expr × Expr)) : MetaM α := do
  let (proof, ty) := fact
  let plgs ← polylogs ty
  plgs.fold (fun cont' e => addpolylog e cont') (fun hmap => do
    cont hmap (arr.push (proof, ← replacepolylog hmap ty))) hmap₀

-- For test purpose
-- This function's semantics is incorrect. A full-fleged version should run
--   in `Reif.ReifM` and modify `fvarsToAbstract` and `iPolyLog` simultaneously
def collectPolyLog (cont : HashMap Expr FVarId → Array (Expr × Expr) → MetaM α)
  (facts : Array ((Expr × Expr))) : MetaM α := do
  if testCollectPolyLog.get (← getOptions) then
    let cont' := facts.foldl (β := HashMap Expr FVarId → Array (Expr × Expr) → MetaM α)
      (fun cont' fact => collectPolyLogAux fact cont') (fun hmap mfacts => do
        for fact in mfacts do
          trace[auto.mono] "Monomorphized: {fact.fst} : {fact.snd}"
        for (expr, fvar) in hmap.toList do
          trace[auto.mono] "Expression {expr} turned into {Expr.fvar fvar}"
        cont hmap mfacts
      )
    cont' HashMap.empty #[]
  else
    cont HashMap.empty facts

end Auto.Monomorphization