import Lean
import Auto.Embedding.Lift
import Auto.Translation.Assumptions
import Auto.Translation.ReifM
import Auto.Translation.Inhabitation
import Auto.Lib.LevelExtra
import Auto.Lib.ExprExtra
import Auto.Lib.MonadUtils
import Auto.Lib.Containers
import Auto.Lib.MetaState
import Auto.Lib.MetaExtra
import Auto.Translation.SMTAttributes
open Lean

initialize
  registerTraceClass `auto.mono
  registerTraceClass `auto.mono.match
  registerTraceClass `auto.mono.match.verbose
  registerTraceClass `auto.mono.fvarRepFact
  registerTraceClass `auto.mono.printLemmaInst
  registerTraceClass `auto.mono.printConstInst
  registerTraceClass `auto.mono.printResult
  registerTraceClass `auto.mono.printInputLemmas
  registerTraceClass `auto.mono.ciInstDefEq
  registerTraceClass `auto.mono.termLikeDefEq

register_option auto.mono.saturationThreshold : Nat := {
  defValue := 1024
  descr := "Threshold for number of matches performed" ++
    " during the saturation loop of monomorphization"
}

register_option auto.mono.recordInstInst : Bool := {
  defValue := false
  descr := "Whether to record instances of constants with the `instance` attribute"
}

register_option auto.mono.ciInstDefEq.mode : Meta.TransparencyMode := {
  defValue := .default
  descr := "Transparency level used when collecting definitional equality" ++
    " arising from instance relations between `ConstInst`s"
}

register_option auto.mono.ciInstDefEq.maxHeartbeats : Nat := {
  defValue := 2048
  descr := "Heartbeats allocated to each unification of constant instance"
}

register_option auto.mono.termLikeDefEq.mode : Meta.TransparencyMode := {
  defValue := .default
  descr := "Transparency level used when collecting definitional equalities" ++
    " between term-like subterms"
}

register_option auto.mono.termLikeDefEq.maxHeartbeats : Nat := {
  defValue := 2048
  descr := "Heartbeats allocated to each unification of term-like expression"
}

namespace Auto

inductive MonoMode where
  | fol -- First-order logic
  | hol -- Monomorphic higher-order logic
deriving BEq, Hashable, Inhabited

instance : ToString MonoMode where
  toString : MonoMode → String
  | .fol => "fol"
  | .hol => "hol"

instance : Lean.KVMap.Value MonoMode where
  toDataValue n := toString n
  ofDataValue?
  | "fol" => some .fol
  | "hol" => some .hol
  | _     => none

end Auto

register_option auto.mono.mode : Auto.MonoMode := {
  defValue := Auto.MonoMode.hol
  descr := "Operation mode of monomorphization"
}

register_option auto.mono.ignoreNonQuasiHigherOrder : Bool := {
  defValue := false
  descr := "Whether to ignore non quasi-higher-order" ++
           " " ++ "monomorphization preprocessing outputs or to throw an error"
}


namespace Auto.Monomorphization
open Embedding

def getRecordInstInst : CoreM Bool := do
  return auto.mono.recordInstInst.get (← getOptions)

def getMode : CoreM MonoMode := do
  return auto.mono.mode.get (← getOptions)

def getIgnoreNonQuasiHigherOrder : CoreM Bool := do
  return auto.mono.ignoreNonQuasiHigherOrder.get (← getOptions)

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
| .const name lvls => .const name lvls.toList

/-- Ignore constant's levels -/
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

/-- **Remark**: This function assigns level mvars if necessary -/
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

/--
  If a constant `c` is of type `∀ (xs : αs), t`,
    then its valid instance will be `c` with all of its
    universe levels, dependent arguments and instance
    arguments instantiated.  So, we record the instantiation
    of universe levels and dependent arguments.

  As to monomorphization, we will not record instances of
    constants with `instance` attribute or whose type is
    a class.
-/
structure ConstInst where
  head       : CiHead
  /-
    · Instantiation of dependent arguments and instance arguments.
    · Note that the same head may have different dependent arguments
      under different circumstances. For example,
      `Funlike.coe : {F : Sort u_3} → {α : Sort u_2} → {β : (α → Sort u_1)} → [self : FunLike F α β] → F → (a : α) → β a`
      · For `β = id`, the argument `(a : α)` is a dependent argument
      · For `β = fun _ => γ`, the argument `(a : α)` is non-dependent
  -/
  argsInst   : Array Expr
  argsIdx    : Array Nat
  deriving Inhabited, Hashable, BEq

def ConstInst.fingerPrint (ci : ConstInst) := ci.head.fingerPrint

private def ConstInst.toMessageDataAux (ci : ConstInst) : MessageData :=
  let nArgsIdx := ci.argsIdx.size
  match nArgsIdx with
  | 0 => m!""
  | .succ _ =>
    let narg := ci.argsIdx[nArgsIdx - 1]?.getD 0 + 1
    let arr : Array (Option Expr) := Array.mk ((List.range narg).map (fun _ => .none))
    let arr := (ci.argsInst.zip ci.argsIdx).foldl (fun acc (arg, idx) => acc.setD idx (.some arg)) arr
    let arr := arr.map (fun e? => match e? with | .some e => m!" ({e})" | .none => m!" _")
    MessageData.intercalate "" arr.toList

instance : ToMessageData ConstInst where
  toMessageData ci := m!"ConstInst ⦗⦗ {ci.head}{ci.toMessageDataAux} ⦘⦘"

/--
  **Remark**: This function assigns metavariables if necessary,
    but its only usage in this file is under `Meta.withNewMCtxDepth`
  Note that since `ci₁, ci₂` are both `ConstInst`, they does not
    contain loose bound variables
-/
def ConstInst.equiv (ci₁ ci₂ : ConstInst) : MetaM Bool := do
  let ⟨head₁, argsInst₁, idx₁⟩ := ci₁
  let ⟨head₂, argsInst₂, idx₂⟩ := ci₂
  if head₁.fingerPrint != head₂.fingerPrint then
    throwError "{decl_name%} :: {ci₁.head} and {ci₂.head} have different fingerprints"
  if !(← head₁.equiv head₂) then
    return false
  if argsInst₁.size != argsInst₂.size || idx₁ != idx₂ then
    return false
  for (arg₁, arg₂) in argsInst₁.zip argsInst₂ do
    if !(← Meta.isDefEq arg₁ arg₂) then
      return false
  return true

/--
  **Remark**:
  · This function assigns metavariables if necessary
  · Runs in `MetaM`, so `e` should not have loose bound variables
-/
def ConstInst.matchExpr (e : Expr) (ci : ConstInst) : MetaM Bool := do
  let fn := e.getAppFn
  let .some ch := CiHead.ofExpr? fn
    | return false
  if !(← ch.equiv ci.head) then
    return false
  let argsIdx := ci.argsIdx
  if argsIdx.size != ci.argsInst.size then
    throwError "{decl_name%} :: Unexpected error"
  let args := e.getAppArgs
  for (idx, ciarg) in argsIdx.zip ci.argsInst do
    let .some arg := args[idx]?
      | return false
    if !(← Meta.isDefEq arg ciarg) then
      return false
  return true

/--
  Given an hypothesis `t`, we will traverse the hypothesis and
    call `ConstInst.ofExpr?` to find instances of polymorphic constants\
  · Binders of the hypothesis are introduced as fvars, these fvars are
    recorded in `bvars`\
  · `param` records universe level parameters of the hypothesis\
  So, the criterion that an expression `e` is a valid instance is that
  · All dependent arguments and instance arguments are present\
  · The head does not contain expressions in `bvars`\
  · Dependent arguments does not contains expressions in `bvars`\
  · The expression does not contain level parameters in `params`
-/
def ConstInst.ofExpr? (params : Array Name) (bvars : Array Expr) (e : Expr) : MetaM (Option ConstInst) := do
  let paramSet := Std.HashSet.empty.insertMany params
  let bvarSet := Std.HashSet.empty.insertMany bvars
  let fn := e.getAppFn
  -- If the head contains bound variable, then this is not
  --   a valid instance
  if let .some _ := fn.find? (fun e => bvarSet.contains e) then
    return .none
  let args := e.getAppArgs
  let .some head := CiHead.ofExpr? fn
    | return .none
  -- `e` should not have bound parameters
  if let .some _ := Expr.findParam? (fun n => paramSet.contains n) e then
    return .none
  -- Do not record instances of a constant with attribute `instance`
  if (← head.isInstanceQuick) && !(← getRecordInstInst) then
    return .none
  let mut headType ← head.inferType
  let mut argsIdx := #[]
  let mut argsInst := #[]
  -- Check that all dependent and instance arguments are instantiated
  for (arg, idx) in args.zipWithIndex do
    headType ← Core.betaReduce headType
    let .forallE _ ty body bi := headType
      | throwError "{decl_name%} :: {headType} is not a `∀`"
    if let some _ := ty.find? (fun e => bvarSet.contains e) then
      return .none
    if ← shouldInstantiate fn ty body bi then
      if let some _ := arg.find? (fun e => bvarSet.contains e) then
        return .none
      argsIdx := argsIdx.push idx
      argsInst := argsInst.push arg
    headType := body.instantiate1 arg
  headType ← Core.betaReduce headType
  if (Expr.depArgs headType).size != 0 || (Expr.instArgs headType).size != 0 then
    return .none
  return .some ⟨head, argsInst, argsIdx⟩
where
  shouldInstantiate (fn ty body : Expr) (bi : Lean.BinderInfo) : CoreM Bool := do
    let dep : Bool := body.hasLooseBVar 0
    let hol : Bool :=
      match ty with
      | .forallE _ _ body' _ => !body'.hasLooseBVar 0
      | _ => false
    let inst : Bool := (bi == .instImplicit)
    -- `fn` is `∀` or `∃`. Note that although these two
    -- are higher-order functions, they're allowed in first-order logic
    let isPolyIL : Bool :=
      match fn with
      | .const name _ => name == ``Embedding.forallF || name == ``Exists
      | _ => false
    match (← getMode) with
    | .hol => return dep || inst
    | .fol => return dep || (!isPolyIL && hol) || inst

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
  let nargs := (Nat.succ <$> ci.argsIdx[ci.argsIdx.size - 1]?).getD 0
  let mut args : Array (Option Expr) := (Array.mk (List.range nargs)).map (fun n => .none)
  for (arg, idx) in ci.argsInst.zip ci.argsIdx do
    args := args.setD idx (.some arg)
  let .some ret := ConstInst.toExprAux args.toList [] ci.head.toExpr type
    | throwError "{decl_name%} :: Unexpected error"
  return ret

/--
  Precondition : `.some ci == ← ConstInst.ofExpr? e`
  Returns the list of non-dependent arguments in `e.getAppArgs`
-/
def ConstInst.getOtherArgs (ci : ConstInst) (e : Expr) : CoreM (Array Expr) := do
  let mut args := e.getAppArgs.map Option.some
  for idx in ci.argsIdx do
    args := args.setD idx .none
  let mut ret := #[]
  for arg? in args do
    if let .some arg := arg? then
      ret := ret.push arg
  return ret

private partial def collectConstInsts (params : Array Name) (bvars : Array Expr) : Expr → MetaM (Array ConstInst)
| e@(.const _ _) => processOther params e
| e@(.fvar _) => processOther params e
| e@(.mvar _) => processOther params e
| e@(.app ..) => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let insts := (← (args.push fn).mapM (collectConstInsts params bvars)).flatMap id
  match ← ConstInst.ofExpr? params bvars e with
  | .some ci => return insts.push ci
  | .none => return insts
| .lam name ty body bi => Meta.withLocalDecl name bi ty fun x => do
  let insts ← collectConstInsts params (bvars.push x) (body.instantiate1 x)
  -- Do not look into instance binders
  if bi.isInstImplicit then
    return insts
  else
    return insts ++ (← collectConstInsts params bvars ty)
| .forallE name ty body bi => Meta.withLocalDecl name bi ty fun x => do
  let insts ← collectConstInsts params (bvars.push x) (body.instantiate1 x)
  -- Do not look into instance binders
  if bi.isInstImplicit then
    return insts
  else
    return insts ++ (← collectConstInsts params bvars ty)
| .letE .. => throwError "{decl_name%} :: Let-expressions should have been reduced"
| .mdata .. => throwError "{decl_name%} :: mdata should have been consumed"
| .proj .. => throwError "{decl_name%} :: Projections should have been turned into ordinary expressions"
| _ => return #[]
where processOther (params : Array Name) (e : Expr) : MetaM (Array ConstInst) := do
  match ← ConstInst.ofExpr? params bvars e with
  | .some ci => return #[ci]
  | .none => return #[]

/-- Array of instances of a polymorphic constant -/
abbrev ConstInsts := Array ConstInst

/--
  Given an array `cis` and a potentially new instance `ci`
  · If `ci` is new, add it to `ConstInsts` and return `true`
  · If `ci` is not new, return an element of the original `ConstInsts`
    which is definitionally equal to `ci`
-/
def ConstInsts.canonicalize? (cis : ConstInsts) (ci : ConstInst) : MetaM (Option ConstInst) := do
  for ci' in cis do
    if ← Meta.withNewMCtxDepth (ci'.equiv ci) then
      return .some ci'
  return .none

/--
  Given an MLemmaInst `mi` and a subexpressions `e` of `mi.type`,
    try to match `e` and the subexpressions of `e` against `ci`.
  This function is used by `LemmaInst.matchConstInst` only
-/
private partial def MLemmaInst.matchConstInst (ci : ConstInst) (mi : MLemmaInst) : Expr → MetaM (Std.HashSet LemmaInst)
| .bvar _ => throwError "{decl_name%} :: Loose bound variable"
| e@(.app ..) => do
  let args := e.getAppArgs
  let mut ret := Std.HashSet.empty
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
        | throwError "{decl_name%} :: Unexpected error"
      let type ← id.getType
      ret := mergeHashSet ret (← MLemmaInst.matchConstInst ci mi type)
    return ret
| .lam name ty body bi => Meta.withLocalDecl name bi ty fun x => do
    let tyInst ← MLemmaInst.matchConstInst ci mi ty
    let bodyInst ← MLemmaInst.matchConstInst ci mi (body.instantiate1 x)
    return mergeHashSet tyInst bodyInst
| .letE .. => throwError "{decl_name%} :: Let-expressions should have been reduced"
| .mdata .. => throwError "{decl_name%} :: mdata should have been consumed"
| .proj .. => throwError "{decl_name%} :: Projections should have been turned into ordinary expressions"
| _ => return Std.HashSet.empty

/-- Given a LemmaInst `li` and a ConstInst `ci`, try to match all subexpressions of `li` against `ci` -/
def LemmaInst.matchConstInst (ci : ConstInst) (li : LemmaInst) : MetaM (Std.HashSet LemmaInst) :=
  Meta.withNewMCtxDepth do
    let (lmvars, mvars, mi) ← MLemmaInst.ofLemmaInst li
    if lmvars.size == 0 && mvars.size == 0 then
      return Std.HashSet.empty
    -- Match with `b` in `∀ (x₁ : α₁) ⋯ (xₙ : αₙ). b := li.type`
    let mut ret ← MLemmaInst.matchConstInst ci mi mi.type
    -- Match with `α₁ ⋯ αₙ` in `∀ (x₁ : α₁) ⋯ (xₙ : αₙ). b := li.type`
    for mvar in mvars do
      let .mvar m := mvar
        | throwError "{decl_name%} :: Unexpected error"
      let mtype ← m.getType
      if ← Meta.isProp mtype then
        ret := mergeHashSet ret (← MLemmaInst.matchConstInst ci mi (← m.getType))
    return ret

/--
  Check whether the leading `∀` quantifiers of expression `e`
    violates the quasi-monomorphic condition
-/
partial def leadingForallQuasiMonomorphic := leadingForallQuasiMonomorphicAux #[]
where
  leadingForallQuasiMonomorphicAux (fvars : Array FVarId) (e : Expr) : MetaM Bool :=
  match e with
  | .forallE name ty body bi => Meta.withLocalDecl name bi ty fun x => do
    let Expr.fvar xid := x
      | throwError "{decl_name%} :: Unexpected error"
    let bodyi := body.instantiate1 x
    if ← Meta.isProp ty then
      if !(← Meta.isProp bodyi) then
        return false
      if body.hasLooseBVar 0 then
        return false
      return (← leadingForallQuasiMonomorphicAux fvars ty) &&
             (← leadingForallQuasiMonomorphicAux (fvars.push xid) bodyi)
    else
      let hol : Bool :=
        match ty with
        | .forallE _ _ body _ => !body.hasLooseBVar 0
        | _ => false
      if hol && (← getMode) == .fol then
        return false
      let fvarSet := Std.HashSet.empty.insertMany fvars
      if ty.hasAnyFVar fvarSet.contains then
        return false
      leadingForallQuasiMonomorphicAux (fvars.push xid)  bodyi
  | _ => return true

/--
  Test whether a lemma is type monomorphic && universe monomorphic
    By universe monomorphic we mean `lem.params = #[]`
  If all dependent arguments are instantiated, but some instance
    arguments are not instantiated, we will try to synthesize the instance arguments
-/
def LemmaInst.monomorphic? (li : LemmaInst) : MetaM (Option LemmaInst) := do
  if li.params.size != 0 then
    return .none
  -- Do not use `prepReduceExpr` because lemmas about
  --   recursors might be reduced to tautology
  let li := {li with type := ← Core.betaReduce li.type}
  if !(← leadingForallQuasiMonomorphic li.type) then
    return .none
  Meta.withNewMCtxDepth do
    let (_, mvars, mi) ← MLemmaInst.ofLemmaInst li
    for mvar in mvars do
      let mvarTy ← instantiateMVars (← Meta.inferType mvar)
      if let .some _ ← Meta.isClass? mvarTy then
        if let .some inst ← Meta.trySynthInstance mvarTy then
          match mvar with
          | .mvar id => id.assign inst
          | _ => throwError "{decl_name%} :: Unexpected error"
    LemmaInst.ofMLemmaInst mi

/--
  Monomorphization works as follows:\
  (1) Turning `Lemma`s into `LemmaInst`s, which constitutes the
      value of `lisArr` in the beginning\
  (2) Scan through all assumptions to find subterms that are
      valid instances of constants (dependent arguments fully
      instantiated). They form the initial elements of `ciMap`
      and `activeCi`\
  (3) Repeat:\
      · Dequeue an element `active`\
      · If it is a `ConstInst`, match against all existing `LemmaInst`;
        If it is a `LemmaInst`, match against all existing `ConstInst`\
      · For all the new `LemmaInst`s generated and all the `ConstInst`s
        occurring in them to `active`
-/
structure State where
  -- The `Expr` is the fingerprint of the `ConstInst`
  ciMap  : Std.HashMap Expr ConstInsts := {}
  -- During initialization, we supply an array `lemmas` of lemmas
  --   `liArr[i]` are instances of `lemmas[i]`.
  lisArr : Array LemmaInsts            := #[]
  -- Definitional equalities from instance relations between `ConstInst`s
  ciInstDefEqs : Array LemmaInst       := #[]
  -- The `Nat` in `LemmaInst × Nat` indicates the `LemmaInst`'s
  --   position in ``lisArr``
  active : Std.Queue (ConstInst ⊕ (LemmaInst × Nat)) := Std.Queue.empty

abbrev MonoM := StateRefT State MetaM

#genMonadState MonoM

/-
  Returns:
  1. Whether canonicalization is successful / Whether the constant is not new
  2. `(ciMap.find? ci.name).getD #[]`
  3. Canonicalized ConstInst
-/
def CiMap.canonicalize? (ciMap : Std.HashMap Expr ConstInsts) (ci : ConstInst) :
  MetaM (Bool × ConstInsts × ConstInst) := do
  match ciMap.get? ci.fingerPrint with
  | .some insts =>
    match ← insts.canonicalize? ci with
    | .some ci' => return (true, insts, ci')
    | .none => return (false, insts, ci)
  | .none => return (false, #[], ci)

/--
  Process a potentially new ConstInst. If it's new, return its index
    in the corresponding `ConstInsts` array. If it's not new, return `.none`.
-/
def processConstInst (ci : ConstInst) : MonoM Unit := do
  let (old?, insts, ci) ← CiMap.canonicalize? (← getCiMap) ci
  if old? then
    return
  trace[auto.mono.printConstInst] "New {ci}"
  setCiMap ((← getCiMap).insert ci.fingerPrint (insts.push ci))
  -- Insert `ci` into `activeCi` so that we can later match on it
  setActive ((← getActive).enqueue (.inl ci))

partial def termLikeSubexprs (bvars : Array Expr) : Expr → MetaM (Array Expr)
| e@(.lam _ _ _ _) =>
  Meta.lambdaBoundedTelescope e 1 fun xs b => termLikeSubexprs (bvars ++ xs) b
| e@(.forallE _ ty body _) => do
  if body.hasLooseBVar 0 then
    Meta.forallBoundedTelescope e (.some 1) fun xs b => termLikeSubexprs (bvars ++ xs) b
  else
    let mut ret ← termLikeSubexprs bvars (body.instantiate1 (.fvar ⟨`dummy⟩))
    if (← Meta.isProp ty) then
      ret := ret ++ (← termLikeSubexprs bvars ty)
    return ret
| e@(.app _ _) => do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let mut ret := #[]
  if fn.constName? == .some ``Eq then
    for arg in args[1:] do
      ret := ret ++ (← termLikeSubexprs bvars arg)
    return ret
  if fn.constName? == .some ``Not then
    if let #[body] := args then
      return ← termLikeSubexprs bvars body
  if fn.constName? == .some ``Iff || fn.constName? == .some ``And || fn.constName? == .some ``Or then
    for arg in args do
      ret := ret ++ (← termLikeSubexprs bvars arg)
    return ret
  return #[← Meta.mkLambdaFVars (usedOnly := true) bvars e]
| e => return #[← Meta.mkLambdaFVars (usedOnly := true) bvars e]

def termLikeDefEqDefEqs (lemmas : Array Lemma) : MetaM (Array Lemma) := do
  let nses := (← lemmas.mapM (fun lem => do
    let subs ← termLikeSubexprs #[] lem.type
    return subs.map (fun e => (e, lem.params)))).flatMap id
  let nses := nses.map (fun (e, params) =>
    let params := params.filter (fun n => (Std.HashSet.ofArray (collectLevelParams {} e).params).contains n)
    (e, params))
  let mut ret := #[]
  let mode := auto.mono.termLikeDefEq.mode.get (← getOptions)
  let heartbeats := auto.mono.termLikeDefEq.maxHeartbeats.get (← getOptions)
  for ((n₁, params₁), idx₁) in nses.zipWithIndex do
    if n₁.isLambda || params₁.size != 0 then continue
    for ((n₂, params₂), idx₂) in nses.zipWithIndex do
      if idx₁ >= idx₂ then continue
        let computation := Meta.withNewMCtxDepth <| Meta.withTransparency mode <| Expr.instanceOf? n₂ params₂ n₁
        let computation := Meta.runtimeExToExcept <| Meta.withMaxHeartbeats heartbeats <| computation
        if let .ok (.some (proof, eq, params)) ← computation then
          let eq := Expr.eraseMData (← Core.betaReduce eq)
          let eq ← Meta.transform eq (pre := fun e => do return .continue (← unfoldProj e))
          if ← isTrivialEq eq then
            continue
          trace[auto.mono.termLikeDefEq] "{eq}"
          ret := ret.push ⟨⟨proof, eq, .leaf "termLikeDefEq"⟩, params⟩
  return ret
where
  isTrivialEq (e : Expr) : MetaM Bool := Meta.forallTelescope e fun _ b => do
    let_expr Eq _ lhs rhs := b | return false
    return lhs == rhs

def initializeMonoM (lemmas : Array Lemma) : MonoM Unit := do
  let lemmas := lemmas ++ (← termLikeDefEqDefEqs lemmas)
  let lemmaInsts ← liftM <| lemmas.mapM (fun lem => do
    let li ← LemmaInst.ofLemmaHOL lem
    trace[auto.mono.printLemmaInst] "New {li}"
    return li)
  for (li, idx) in lemmaInsts.zipWithIndex do
    setActive ((← getActive).enqueue (.inr (li, idx)))
  let lemmaInsts := lemmaInsts.map (fun x => #[x])
  setLisArr lemmaInsts
  for lem in lemmas do
    let cis ← collectConstInsts lem.params #[] lem.type
    for ci in cis do
      processConstInst ci

def dequeueActive? : MonoM (Option (ConstInst ⊕ (LemmaInst × Nat))) := do
  match (← getActive).dequeue? with
  | .some (elem, ac') =>
    setActive ac'
    return .some elem
  | .none => return .none

def lookupActiveCi! (fgp : Expr) (idx : Nat) : MonoM ConstInst := do
  let .some cis := (← getCiMap).get? fgp
    | throwError "{decl_name%} :: Unknown CiHead {fgp}"
  let .some ci := cis[idx]?
    | throwError "{decl_name%} :: Index {idx} out of bound"
  return ci

def saturationThresholdReached? (cnt : Nat) : CoreM Bool := do
  let threshold := auto.mono.saturationThreshold.get (← getOptions)
  if cnt > threshold then
    trace[auto.mono] "Monomorphization saturation :: Threshold {threshold} reached"
    return true
  else
    return false

@[inherit_doc State]
def saturate : MonoM Unit := do
  let mut cnt := 0
  while true do
    cnt := cnt + 1
    if (← saturationThresholdReached? cnt) then
      return
    match ← dequeueActive? with
    | .some (.inl ci) =>
      generateCiInstDefEq ci
      let lisArr ← getLisArr
      trace[auto.mono.match] "Matching against {ci}"
      for (lis, idx) in lisArr.zipWithIndex do
        cnt := cnt + 1
        for li in lis do
          let newLis_cnt ← matchCiAndLi ci li idx cnt
          let newLis := newLis_cnt.fst
          setLisArr ((← getLisArr).set! idx newLis)
          cnt := newLis_cnt.snd
          if (← saturationThresholdReached? cnt) then
            return
    | .some (.inr (li, idx)) =>
      trace[auto.mono.match] "Matching against {li}"
      let cis := ((← getCiMap).toArray.map Prod.snd).flatMap id
      for ci in cis do
        cnt := cnt + 1
        let newLis_cnt ← matchCiAndLi ci li idx cnt
        let newLis := newLis_cnt.fst
        setLisArr ((← getLisArr).set! idx newLis)
        cnt := newLis_cnt.snd
        if (← saturationThresholdReached? cnt) then
          return
    | .none =>
      trace[auto.mono] "Monomorphization Saturated after {cnt} small steps"
      return
where
  matchCiAndLi (ci : ConstInst) (li : LemmaInst) (idx : Nat) (cnt : Nat) :
    MonoM (LemmaInsts × Nat) := do
    let mut cnt := cnt
    let mut newLis := (← getLisArr)[idx]!
    -- Do not match against ConstInsts that have no dependent or instance arguments
    if ci.argsIdx.size == 0 then
      return (newLis, cnt)
    -- Do not match against `=` and `∃`
    -- If some polymorphic argument of the a theorem only occurs
    --   as the first argument of `=` or `∃`, the theorem is probably
    --   implied by the axioms of higher order logic, e.g.
    -- `Eq.trans : ∀ {α} (x y z : α), x = y → y = z → x = z`
    if ci.head.isNamedConst ``Exists || ci.head.isNamedConst ``Eq then
      return (newLis, cnt)
    trace[auto.mono.match.verbose] "Matching {ci} against {li}"
    cnt := cnt + 1
    let matchLis := (← LemmaInst.matchConstInst ci li).toArray
    for matchLi in matchLis do
      -- `matchLi` is a result of matching a subterm of `li` against `ci`
      cnt := cnt + 1
      if (← saturationThresholdReached? cnt) then
        return (newLis, cnt)
      -- Attempt to instantiate instance arguments and get monomoprhic lemma instance
      let matchLi := (← LemmaInst.monomorphic? matchLi).getD matchLi
      let new? ← newLis.newInst? matchLi
      -- A new instance of an assumption
      if new? then
        trace[auto.mono.printLemmaInst] "New {matchLi}"
        newLis := newLis.push matchLi
        setActive ((← getActive).enqueue (.inr (matchLi, idx)))
        collectAndProcessConstInsts matchLi
        if let .some monoLi ← LemmaInst.monomorphic? matchLi then
          if monoLi != matchLi && (← LemmaInsts.newInst? newLis monoLi) then
            newLis := newLis.push monoLi
            setActive ((← getActive).enqueue (.inr (monoLi, idx)))
            collectAndProcessConstInsts monoLi
    return (newLis, cnt)
  /-
    This `ci` comes from `active`, so it is already canonicalized
  -/
  generateCiInstDefEq (ci : ConstInst) : MonoM Unit := do
    if isTrigger ci.head then
      return
    let cis := ((← getCiMap).toArray.map Prod.snd).flatMap id
    for (ci', _) in cis.zipWithIndex do
      if (← ci.toExpr) != (← ci'.toExpr) && !(isTrigger ci'.head) then
        if let .some (proof, eq, _) ← bidirectionalOfInstanceEq ci ci' then
          let eq := Expr.eraseMData (← Core.betaReduce eq)
          let eq ← Meta.transform eq (pre := fun e => do return .continue (← unfoldProj e))
          trace[auto.mono.ciInstDefEq] "{eq}"
          let newLi ← LemmaInst.ofLemma ⟨⟨proof, eq, .leaf "ciInstDefEq"⟩, #[]⟩
          setCiInstDefEqs ((← getCiInstDefEqs).push newLi)
          collectAndProcessConstInsts newLi
  collectAndProcessConstInsts (li : LemmaInst) : MonoM Unit := do
    let newCis ← collectConstInsts li.params #[] li.type
    for newCi in newCis do
      processConstInst newCi
  bidirectionalOfInstanceEq (ci₁ ci₂ : ConstInst) : MetaM (Option (Expr × Expr × Array Name)) := do
    let mode := auto.mono.ciInstDefEq.mode.get (← getOptions)
    let heartbeats := auto.mono.ciInstDefEq.maxHeartbeats.get (← getOptions)
    let result ← Meta.runtimeExToExcept <| Meta.withMaxHeartbeats heartbeats <| Meta.withNewMCtxDepth <| Meta.withTransparency mode <| do
      return (← Expr.instanceOf? (← ci₁.toExpr) #[] (← ci₂.toExpr)) <|>
        (← Expr.instanceOf? (← ci₂.toExpr) #[] (← ci₁.toExpr))
    match result with
    | .ok r => return r
    | .error _ => return .none
  isTrigger (cih : CiHead) :=
    match cih with
    | .const name _ => name == ``SMT.Attribute.trigger
    | _ => false

/-- Remove non-monomorphic lemma instances -/
def getAllMonoLemmaInsts : MonoM LemmaInsts := do
  let lisArr ← getLisArr
  let lisArr ← liftM <| lisArr.mapM (fun lis => lis.filterMapM LemmaInst.monomorphic?)
  let lis := lisArr.flatMap id
  return lis ++ (← getCiInstDefEqs)

/-- Collect inductive types -/
def collectMonoMutInds : MonoM (Array (Array SimpleIndVal)) := do
  let cis := (Array.mk ((← getCiMap).toList.map Prod.snd)).flatMap id
  let citys ← cis.mapM (fun ci => do
    let cie ← ci.toExpr
    let ty ← Meta.inferType cie
    return Expr.eraseMData ty)
  let minds ← collectExprsSimpleInduct citys
  let cis ← (minds.flatMap id).mapM (fun ⟨_, type, ctors, projs⟩ => do
    let cis₁ ← collectConstInsts #[] #[] type
    let cis₂ ← ctors.mapM (fun (val, ty) => do
      let cis₁ ← collectConstInsts #[] #[] val
      let cis₂ ← collectConstInsts #[] #[] ty
      return cis₁ ++ cis₂)
    let projs := (match projs with | .some projs => projs | .none => #[])
    let cis₃ ← projs.mapM (fun e => collectConstInsts #[] #[] e)
    return cis₁ ++ cis₂.flatMap id ++ cis₃.flatMap id)
  let _ ← (cis.flatMap id).mapM processConstInst
  return minds

namespace FVarRep

  structure State where
    bfvars   : Array FVarId             := #[]
    -- Free variables representing abstracted expressions
    ffvars   : Array FVarId             := #[]
    exprMap  : Std.HashMap Expr FVarId      := {}
    ciMap    : Std.HashMap Expr ConstInsts
    ciIdMap  : Std.HashMap ConstInst FVarId := {}
    -- Canonicalization map for types
    tyCanMap : Std.HashMap Expr Expr        := {}

  abbrev FVarRepM := StateRefT State MetaState.MetaStateM

  #genMonadState FVarRepM

  def getBfvarSet : FVarRepM (Std.HashSet FVarId) := do
    let bfvars ← getBfvars
    return Std.HashSet.empty.insertMany bfvars

  def getFfvarSet : FVarRepM (Std.HashSet FVarId) := do
    let ffvars ← getFfvars
    return Std.HashSet.empty.insertMany ffvars

  /-- Similar to `Monomorphization.processConstInst` -/
  def processConstInst (ci : ConstInst) : FVarRepM Unit := do
    let (old?, insts, ci) ← MetaState.runMetaM <| CiMap.canonicalize? (← getCiMap) ci
    if old? then
      return
    trace[auto.mono.printConstInst] "New {ci}"
    setCiMap ((← getCiMap).insert ci.fingerPrint (insts.push ci))

  /-- Return : (reduce(e), whether reduce(e) contain bfvars) -/
  def processType (e : Expr) : FVarRepM (Expr × Bool) := do
    let e ← MetaState.runMetaM <| prepReduceTypeForall e
    let bfvarSet ← getBfvarSet
    -- If `e` contains no bound variables
    if !e.hasAnyFVar bfvarSet.contains then
      processTypeAux e
      return (e, false)
    else
      return (e, true)
  where
    processTypeAux : Expr → FVarRepM Unit
    | e@(.forallE _ ty body _) => do
      if body.hasLooseBVar 0 then
        -- It's possible that the type can be decomposed further,
        -- but for simplicity, give up for now
        addTypeToTyCanMap e
      else
        processTypeAux ty
        processTypeAux body
    | e => addTypeToTyCanMap e
    addTypeToTyCanMap (e : Expr) : FVarRepM Unit := do
      let e := Expr.eraseMData e
      if (← getTyCanMap).contains e then
        return
      for (e', ec) in (← getTyCanMap).toList do
        let mode := auto.mono.tyDefEq.mode.get (← getOptions)
        if ← MetaState.isDefEqRigidWith e e' mode then
          setTyCanMap ((← getTyCanMap).insert e ec)
          return
      setTyCanMap ((← getTyCanMap).insert e e)

  def constInst2FVarId (ci : ConstInst) : FVarRepM FVarId := do
    let ciMap ← FVarRep.getCiMap
    let ci ← MetaState.runMetaM (do
      match ← CiMap.canonicalize? ciMap ci with
      | (true, _, ci') => return ci'
      | _ => throwError "{decl_name%} :: Cannot find canonicalized instance of {ci}")
    let ciIdMap ← FVarRep.getCiIdMap
    match ciIdMap.get? ci with
    | .some fid => return fid
    | .none => do
      let userName := (`cifvar).appendIndexAfter (← getCiIdMap).size
      let cie ← MetaState.runMetaM ci.toExpr
      let city ← instantiateMVars (← MetaState.inferType cie)
      let (city, _) ← processType city
      let fvarId ← MetaState.withLetDecl userName city cie .default
      setCiIdMap ((← getCiIdMap).insert ci fvarId)
      setFfvars ((← getFfvars).push fvarId)
      return fvarId

  def monoFailMsg (e : Expr) : MessageData :=
    let m₁ := m!"Monomorphization failed because currently the procedure cannot deal with expression `{e}`."
    let m₂ := m!"This is because it has subterms possessing at least one of the following features"
    let m₃ := m!"· Type argument with bound variables, e.g. `@Fin.add (n + 2) a b` where `n` is a bound variable"
    let m₄ := m!"· λ binders whose type contain bound variables, e.g. `fun (x : a) => x` where `a` is a bound variable"
    let m₅ := m!"· Other (TODO)"
    let m₆ := m!"`set_option auto.mono.ignoreNonQuasiHigherOrder true` will instruct Lean-auto to ignore " ++
              m!"all the `LemmaInst`s which contain expressions that cannot be handled by the current procedure"
    m₁ ++ "\n" ++ m₂ ++ "\n" ++ m₃ ++ "\n" ++ m₄ ++ "\n" ++ m₅ ++ "\n" ++ m₆

  def unknownExpr2FVar (e : Expr) : FVarRepM (Expr ⊕ MessageData) := do
    let bfvarSet ← getBfvarSet
    if e.hasAnyFVar bfvarSet.contains then
      return .inr (monoFailMsg e)
    for (e', fid) in (← getExprMap).toList do
      if ← MetaState.isDefEqRigid e e' then
        return .inl (.fvar fid)
    -- Put this trace message after the above for loop
    --   to avoid duplicated messages
    trace[auto.mono] "Don't know how to deal with expression {e}. Turning it into free variable ..."
    let userName := (`exfvar).appendIndexAfter (← getExprMap).size
    let ety ← instantiateMVars (← MetaState.inferType e)
    let (ety, _) ← processType ety
    let fvarId ← MetaState.withLetDecl userName ety e .default
    setExprMap ((← getExprMap).insert e fvarId)
    setFfvars ((← getFfvars).push fvarId)
    return .inl (.fvar fvarId)

  /--
    Attempt to abstract parts of a given expression to free variables so
    that the resulting expression is in the higher-order fragment of Lean.

    Note that it's not always possible to do this since it's possible that
    the given expression itself is polymorphic

    Since we're now dealing with monomorphized lemmas, there are no bound level parameters

    Return value:\
    · If abstraction is successful, return the abstracted expression\
    · If abstraction is not successful because the input is not a quasi higher-order\
      term of type `Prop`, return a message indicating the violation of quasi higher-order-ness
    · Throw an error message if unexpected error happens
  -/
  partial def replacePolyWithFVar : Expr → FVarRepM (Expr ⊕ MessageData)
  | .lam name ty body binfo => do
    -- Type of λ binder cannot depend on previous bound variables
    let (ty, hasBfvars) ← processType ty
    if hasBfvars then
      return .inr m!"{decl_name%} :: Type {ty} of λ binder contains bound variables"
    let fvarId ← MetaState.withLocalDecl name binfo ty .default
    setBfvars ((← getBfvars).push fvarId)
    let b' ← replacePolyWithFVar (body.instantiate1 (.fvar fvarId))
    let .inl b' := b'
      | return b'
    Sum.inl <$> (MetaState.runMetaM <| Meta.mkLambdaFVars #[.fvar fvarId] b')
  -- Turns `∀` into `Embedding.forallF`, `→` into `Embedding.ImpF`
  | e@(.forallE name ty body binfo) => do
    let tysort ← MetaState.runMetaM (do Expr.normalizeType (← Meta.inferType ty))
    let .sort tylvl := tysort
      | throwError "{decl_name%} :: Unexpected error, {tysort} is not a sort"
    let (ty, tyHasBfvars) ← processType ty
    let fvarId ← MetaState.withLocalDecl name binfo ty .default
    setBfvars ((← getBfvars).push fvarId)
    let body' := body.instantiate1 (.fvar fvarId)
    let bodysort ← MetaState.runMetaM <| do Expr.normalizeType (← Meta.inferType body')
    let .sort bodylvl := bodysort
      | throwError "{decl_name%} :: Unexpected error"
    let bodyrep ← replacePolyWithFVar body'
    let .inl bodyrep := bodyrep
      | return bodyrep
    -- Type of type of bound variable is `Prop`
    -- Requirement: Type of body is `Prop`, and the bound variable
    --   of this `∀` does not occur in the body
    if ← MetaState.isLevelDefEqRigid tylvl .zero then
      if !(← MetaState.isLevelDefEqRigid bodylvl .zero) then
        return .inr m!"{decl_name%} :: In {e}, type of ∀ bound variable is of sort `Prop`, but body isn't of sort `Prop`"
      if body.hasLooseBVar 0 then
        return .inr m!"{decl_name%} :: In {e}, type of dependent ∀ bound variable is of sort `Prop`"
      let impFun := Expr.const ``ImpF [.zero, .zero]
      addForallImpFInst impFun
      let tyrep ← replacePolyWithFVar ty
      let .inl tyrep := tyrep
        | return tyrep
      return Sum.inl <| .app (.app impFun tyrep) bodyrep
    -- Type of type of bound variable is not `Prop`
    -- Requirement: Type of bound variable does not contain
    --   bound variables
    else
      if tyHasBfvars then
        return .inr m!"{decl_name%} :: In {e}, type of ∀ bound variable is not of sort `Prop`, and depends on bound variables"
      let forallFun := Expr.app (.const ``forallF [tylvl, bodylvl]) ty
      addForallImpFInst forallFun
      let forallFunId ← replacePolyWithFVar forallFun
      let .inl forallFunId := forallFunId
        | return forallFunId
      return Sum.inl <| .app forallFunId (← MetaState.runMetaM <| Meta.mkLambdaFVars #[.fvar fvarId] bodyrep)
  | e@(.app ..) => do
    -- Head is bvar
    if let .fvar id := e.getAppFn then
      if ((← getBfvars).contains id) then
        let ciArgs? ← e.getAppArgs.mapM replacePolyWithFVar
        let mut ciArgs := #[]
        for ciArg in ciArgs? do
          let .inl ciArg := ciArg
            | return ciArg
          ciArgs := ciArgs.push ciArg
        return Sum.inl <| mkAppN (.fvar id) ciArgs
    -- Head is fvar/mvar/const
    let bfexprs := (← getBfvars).map Expr.fvar
    if let .some ci ← MetaState.runMetaM (ConstInst.ofExpr? #[] bfexprs e) then
      let ciId ← constInst2FVarId ci
      let ciArgs? ← (← ConstInst.getOtherArgs ci e).mapM replacePolyWithFVar
      let mut ciArgs := #[]
      for ciArg in ciArgs? do
        let .inl ciArg := ciArg
          | return ciArg
        ciArgs := ciArgs.push ciArg
      return Sum.inl <| mkAppN (.fvar ciId) ciArgs
    let eFn := e.getAppFn
    let eArgs? ← e.getAppArgs.mapM replacePolyWithFVar
    let mut eArgs := #[]
    for eArg in eArgs? do
      let .inl eArg := eArg
        | return eArg
      eArgs := eArgs.push eArg
    unknownExpr2FVar (Lean.mkAppN eFn eArgs)
  | e@(.sort _) => return Sum.inl e
  | e@(.lit _) => return Sum.inl e
  | e => do
    if let .fvar id := e then
      if (← getBfvars).contains id then
        return Sum.inl <| .fvar id
    let bfexprs := (← getBfvars).map Expr.fvar
    if let .some ci ← MetaState.runMetaM (ConstInst.ofExpr? #[] bfexprs e) then
      let ciId ← constInst2FVarId ci
      return Sum.inl <| .fvar ciId
    unknownExpr2FVar e
  where addForallImpFInst (e : Expr) : FVarRepM Unit := do
    let bfexprs := (← getBfvars).map Expr.fvar
    match ← MetaState.runMetaM (ConstInst.ofExpr? #[] bfexprs e) with
    | .some ci => processConstInst ci
    | .none => trace[auto.mono] "Warning, {e} is not a valid instance of `forallF` or `ImpF`"

end FVarRep

/--
  Given `mvarId : ty`, create a fresh mvar `m` of type
    `monofact₁ → monofact₂ → ⋯ → monofactₙ → ty`
  and return `(m proof₁ proof₂ ⋯ proofₙ, m)`
-/
def intromono (lemmas : Array Lemma) (mvarId : MVarId) : MetaM MVarId := do
  let startTime ← IO.monoMsNow
  let monoMAction : MonoM LemmaInsts := (do
    initializeMonoM lemmas
    saturate
    let monoLemmas ← getAllMonoLemmaInsts
    trace[auto.mono] "Monomorphization took {(← IO.monoMsNow) - startTime}ms"
    return monoLemmas)
  let (monoLemmas, _) ← monoMAction.run {}
  MetaState.runAtMetaM' (do
    let mut fids := #[]
    for ml in monoLemmas do
      let userName := (`monoLem).appendIndexAfter fids.size
      let fid ← MetaState.withLocalDecl userName .default ml.type .default
      fids := fids.push fid
    let type ← MetaState.runMetaM <| mvarId.getType
    let tag ← MetaState.runMetaM <| mvarId.getTag
    let mvar ← MetaState.runMetaM <| Meta.mkFreshExprSyntheticOpaqueMVar type.headBeta tag
    let newVal ← MetaState.runMetaM <| Meta.mkLambdaFVars (fids.map Expr.fvar) mvar
    let newVal := Lean.mkAppN newVal (monoLemmas.map (·.proof))
    mvarId.assign newVal
    return mvar.mvarId!)

def monomorphize (lemmas : Array Lemma) (inhFacts : Array Lemma) (k : Reif.State → MetaM α) : MetaM α := do
  for h in lemmas do
    trace[auto.mono.printInputLemmas] "Monomorphization got input lemma :: {h.type}"
  let ((monoLemmas, monoIndVals), monoSt) ← monoMAction.run {}
  MetaState.runWithIntroducedFVars (metaStateMAction monoLemmas monoIndVals monoSt) k
where
  /-- Instantiating quantifiers, collecting inductive types
    and filtering out non-quasi-monomorphic expressions -/
  monoMAction : MonoM (LemmaInsts × Array (Array SimpleIndVal)) := do
    let startTime ← IO.monoMsNow
    initializeMonoM lemmas
    saturate
    let monoLemmas ← getAllMonoLemmaInsts
    let monoIndVals ← collectMonoMutInds
    trace[auto.mono] "Monomorphization of lemmas took {(← IO.monoMsNow) - startTime}ms"
    return (monoLemmas, monoIndVals)
  /-- Process lemmas and inductive types, collect inhabited types -/
  metaStateMAction
    (monoLemmas : LemmaInsts)
    (monoIndVals : Array (Array SimpleIndVal))
    (monoSt : State) : MetaState.MetaStateM (Array FVarId × Reif.State) := do
    let (uvalids, s) ← (fvarRepMFactAction monoLemmas).run { ciMap := monoSt.ciMap }
    for ⟨proof, ty, _⟩ in uvalids do
      trace[auto.mono.printResult] "Monomorphized :: {proof} : {ty}"
    let tyCans := s.tyCanMap.toArray.map Prod.snd
    -- Inhabited types
    let startTime ← IO.monoMsNow
    let mut tyCanInhs := #[]
    for e in tyCans do
      if let .some inh ← MetaState.runMetaM <| Meta.withNewMCtxDepth <| Meta.trySynthInhabited e then
        tyCanInhs := tyCanInhs.push ⟨inh, e, .leaf "tyCanInh"⟩
    let inhMatches ← MetaState.runMetaM (Inhabitation.inhFactMatchAtomTys inhFacts tyCans)
    let inhs := tyCanInhs ++ inhMatches
    trace[auto.mono] "Monomorphization of inhabitation facts took {(← IO.monoMsNow) - startTime}ms"
    -- Inductive types
    let startTime ← IO.monoMsNow
    trace[auto.mono] "Monomorphization of inductive types took {(← IO.monoMsNow) - startTime}ms"
    let (monoIndVals, s) ← (fvarRepMInductAction monoIndVals).run s
    let exlis := s.exprMap.toList.map (fun (e, id) => (id, e))
    let cilis ← s.ciIdMap.toList.mapM (fun (ci, id) => do return (id, ← MetaState.runMetaM ci.toExpr))
    let polyVal := Std.HashMap.ofList (exlis ++ cilis)
    return (s.ffvars, Reif.State.mk uvalids polyVal s.tyCanMap inhs monoIndVals none)
  fvarRepMFactAction (lis : Array LemmaInst) : FVarRep.FVarRepM (Array UMonoFact) := lis.filterMapM (fun li => do
    trace[auto.mono.fvarRepFact] "{li.type}"
    let liTypeRep? ← FVarRep.replacePolyWithFVar li.type
    match liTypeRep? with
    | .inl liTypeRep => return .some ⟨li.proof, liTypeRep, li.deriv⟩
    | .inr m => if (← getIgnoreNonQuasiHigherOrder) then return .none else throwError m)
  fvarRepMInductAction (ivals : Array (Array SimpleIndVal)) : FVarRep.FVarRepM (Array (Array SimpleIndVal)) :=
    ivals.mapM (fun svals => svals.mapM (fun ⟨name, type, ctors, projs⟩ => do
      let (type, _) ← FVarRep.processType type
      let ctors ← ctors.mapM (fun (val, ty) => do
        let (ty, _) ← FVarRep.processType ty
        let valRep? ← FVarRep.replacePolyWithFVar val
        match valRep? with
        | .inl valRep => return (valRep, ty)
        -- If monomorphization fails on one constructor, fail immediately
        | .inr m => throwError m)
      let projs ← projs.mapM (fun arr => arr.mapM (fun e => do
        match ← FVarRep.replacePolyWithFVar e with
        | .inl e => return e
        -- If monomorphization fails on one projection, fail immediately
        | .inr m => throwError m))
      return ⟨name, type, ctors, projs⟩))

end Auto.Monomorphization
