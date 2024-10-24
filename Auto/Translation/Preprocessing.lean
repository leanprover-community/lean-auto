import Lean
import Auto.Lib.AbstractMVars
import Auto.Lib.MessageData
import Auto.Translation.Assumptions
import Auto.Translation.Reduction
open Lean Meta Elab Tactic

initialize
  registerTraceClass `auto.prep

namespace Auto

namespace Prep

/--
  From a user-provided term `stx`, produce a lemma
-/
def elabLemma (stx : Term) (deriv : DTr) : TacticM Lemma :=
  -- elaborate term as much as possible and abstract any remaining mvars:
  Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let abstres ← Auto.abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return Lemma.mk ⟨e, ← inferType e, deriv⟩ paramNames

def addRecAsLemma (recVal : RecursorVal) : MetaM (Array Lemma) := do
  let some (.inductInfo indVal) := (← getEnv).find? recVal.getInduct
    | throwError "Expected inductive datatype: {recVal.getInduct}"
  let expr := mkConst recVal.name (recVal.levelParams.map Level.param)
  let res ← forallBoundedTelescope (← inferType expr) recVal.getMajorIdx fun xs _ => do
    let expr := mkAppN expr xs
    let inductTyArgs : Array Expr := xs[:indVal.numParams]
    indVal.ctors.mapM fun ctorName => do
      let ctor ← mkAppOptM ctorName (inductTyArgs.map Option.some)
      let (proof, eq) ← forallTelescope (← inferType ctor) fun ys _ => do
        let ctor := mkAppN ctor ys
        let expr := mkApp expr ctor
        let some redExpr ← reduceRecMatcher? expr
          | throwError "Could not reduce recursor application: {expr}"
        let redExpr ← Core.betaReduce redExpr
        let eq ← mkEq expr redExpr
        let proof ← mkEqRefl expr
        return (← mkLambdaFVars ys proof, ← mkForallFVars ys eq)
      let proof ← instantiateMVars (← mkLambdaFVars xs proof)
      let eq ← instantiateMVars (← mkForallFVars xs eq)
      return ⟨⟨proof, eq, .leaf s!"rec {recVal.name}.{ctorName}"⟩, recVal.levelParams.toArray⟩
  for lem in res do
    let ty' ← Meta.inferType lem.proof
    if !(← Meta.isDefEq ty' lem.type) then
      throwError "addRecAsLemma :: Application type mismatch"
  return Array.mk res

def elabDefEq (name : Name) : TacticM (Array Lemma) := do
  match (← getEnv).find? name with
  | some (.recInfo val) =>
    -- Generate definitional equation for recursor
    addRecAsLemma val
  | some (.defnInfo _) =>
    -- Generate definitional equation for (possibly recursive) declaration
    match ← getEqnsFor? name with
    | some eqns => eqns.mapIdxM fun i eq =>
      do elabLemma (← `($(mkIdent eq))) (.leaf s!"defeq {i.val} {name}")
    | none => return #[]
  | some (.axiomInfo _)  => return #[]
  | some (.thmInfo _)    => return #[]
  -- If we have inductively defined propositions, we might
  --   need to add constructors as lemmas
  | some (.ctorInfo _)   => return #[]
  | some (.opaqueInfo _) => throwError "Opaque constants cannot be provided as lemmas"
  | some (.quotInfo _)   => throwError "Quotient constants cannot be provided as lemmas"
  | some (.inductInfo _) => throwError "Inductive types cannot be provided as lemmas"
  | none => throwError "Unknown constant {name}"

def isNonemptyInhabited (ty : Expr) : MetaM Bool := do
  let .some name ← Meta.isClass? ty
    | return false
  return name == ``Nonempty || name == ``Inhabited

structure ConstUnfoldInfo where
  name : Name
  val : Expr
  params : Array Name

def getConstUnfoldInfo (name : Name) : MetaM ConstUnfoldInfo := do
  let .some ci := (← getEnv).find? name
    | throwError "getConstUnfoldInfo :: Unknown declaration {name}"
  let .some val := ci.value?
    | throwError "getConstUnfoldInfo :: {name} is not a definition, thus cannot be unfolded"
  let val ← prepReduceExpr val
  let params := ci.levelParams
  return ⟨name, val, ⟨params⟩⟩

/--
  Topologically sort constant names, such that the definition body
    of previous names does not use latter ones.
  If there is cyclic dependency, `topoSortUnfolds` throws an error
-/
partial def topoSortUnfolds (unfolds : Array ConstUnfoldInfo) : MetaM (Array ConstUnfoldInfo) := do
  let mut depMap : HashMap Name (HashSet Name) := {}
  for ⟨i, val, _⟩ in unfolds do
    for ⟨j, _, _⟩ in unfolds do
      if (val.find? (fun e => e.constName? == .some j)).isSome then
        let deps := (depMap.find? i).getD {}
        depMap := depMap.insert i (deps.insert j)
  let (_, _, nameArr) ← (unfolds.mapM (fun n => go depMap {} n.name)).run ({}, #[])
  let nameMap : HashMap Name _ := HashMap.ofList (unfolds.data.map (fun ui => (ui.name, ui)))
  let mut ret := #[]
  for name in nameArr do
    let .some ui := nameMap.find? name
      | throwError "topoSortUnfolds :: Unexpected error"
    ret := ret.push ui
  return ret.reverse
where
  go (depMap : HashMap Name (HashSet Name)) (stack : HashSet Name) (n : Name) : StateRefT (HashSet Name × Array Name) MetaM Unit := do
    if stack.contains n then
      throwError "topoSortUnfolds :: Cyclic dependency"
    let (done, ret) ← get
    if done.contains n then
      return
    let deps := (depMap.find? n).getD {}
    set (done.insert n, ret)
    for dep in deps do
      go depMap (stack.insert n) dep
    let (done, ret) ← get
    set (done, ret.push n)

/--
  Unfold constants occurring in expression `e`
  `unfolds` should satisfy the following constraint:
    ∀ i j, i < j → `unfolds[j].name` does not occur in `unfolds[i].val`
-/
def unfoldConsts (unfolds : Array Prep.ConstUnfoldInfo) (e : Expr) : Expr := Id.run <| do
  let mut e := e
  for ⟨uiname, val, params⟩ in unfolds do
    e := e.replace (fun e =>
      match e with
      | .const name lvls =>
        if name == uiname then
          val.instantiateLevelParams params.data lvls
        else
          .none
      | _ => .none)
  return e

end Prep

end Auto
