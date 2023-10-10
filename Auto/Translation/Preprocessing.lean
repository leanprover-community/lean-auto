import Lean
import Auto.Lib.AbstractMVars
import Auto.Lib.MessageData
import Auto.Translation.Assumptions
open Lean Meta Elab Tactic

initialize
  registerTraceClass `auto.prep

private instance : ToString TransparencyMode where
  toString : TransparencyMode → String
  | .all       => "all"
  | .default   => "default"
  | .reducible => "reducible"
  | .instances => "instances"

private instance : Lean.KVMap.Value TransparencyMode where
  toDataValue t := toString t
  ofDataValue?
  | "all"       => some .all
  | "default"   => some .default
  | "reducible" => some .reducible
  | "instances" => some .instances
  | _           => none

register_option auto.prep.redMode : TransparencyMode := {
  defValue := .reducible
  descr := "TransparencyMode used when reducing collected facts"
}

namespace Auto

namespace Prep

def unfoldProj (e : Expr) : MetaM Expr :=
  match e with
  | .proj name idx struct => do
    let some (.inductInfo indi) := (← getEnv).find? name
      | throwError s!"unfoldProj :: {name} is not a inductive type"
    let some structInfo := getStructureInfo? (← getEnv) name
      | throwError s!"unfoldProj :: {name} is not a structure"
    let nameMap : HashMap Name StructureFieldInfo := HashMap.ofList
      (structInfo.fieldInfo.map (fun sfi => (sfi.fieldName, sfi))).data
    let sorted := structInfo.fieldNames.map (fun name => nameMap.find? name)
    let .some (.some sfi) := sorted[idx]?
      | throwError s!"unfoldProj :: Projection index out of bound"
    let nones : List (Option Expr) := (List.range indi.numParams).map (fun _ => .none)
    Meta.mkAppOptM sfi.projFn ((Array.mk nones).push struct)
  | _ => return e

/-- This function is expensive -/
partial def preprocessExpr (term : Expr) : MetaM Expr := do
  let red (e : Expr) : MetaM TransformStep := do
    let e := e.consumeMData
    let e ← Meta.whnf e
    return .continue e
  -- Reduce
  let trMode := auto.prep.redMode.get (← getOptions)
  let term ← Meta.withTransparency trMode <| Meta.transform term (pre := red) (usedLetOnly := false)
  let redProj (e : Expr) : MetaM TransformStep := do
    let e ← unfoldProj e
    return .continue e
  let term ← Meta.transform term (pre := redProj)
  return term

/--
  We assume that all defeq facts have the form
    `∀ (x₁ : ⋯) ⋯ (xₙ : ⋯), c ... = ...`
  where `c` is a constant. To avoid `whnf` from reducing
  `c ⋯` (which can happen when e.g. `c` is a recursor), we
  call `forallTelescope`, then call `Prep.preprocessExpr` on
  · All the arguments of `c`, and
  · The right-hand side of the equation
-/
def preprocessDefeq (type : Expr) : MetaM (Option Expr) := do
  let type := Expr.eraseMData type
  Meta.forallTelescope type fun xs b => do
    let .app (.app (.app (.const ``Eq lvls) ty) lhs) rhs := b
      | return .none
    let ty ← preprocessExpr ty
    let lhFn := lhs.getAppFn
    let lhArgs ← lhs.getAppArgs.mapM preprocessExpr
    let lhs := mkAppN lhFn lhArgs
    let rhs ← preprocessExpr rhs
    let eq' := Lean.mkApp3 (.const ``Eq lvls) ty lhs rhs
    return .some (← mkForallFVars xs eq')

/-- From a user-provided term `stx`, produce a lemma -/
def elabLemma (stx : Term) : TacticM Lemma :=
  -- elaborate term as much as possible and abstract any remaining mvars:
  Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let abstres ← Auto.abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return Lemma.mk e (← inferType e) paramNames

def addRecAsLemma (recVal : RecursorVal) : TacticM (Array Lemma) := do
  let some (.inductInfo indVal) := (← getEnv).find? recVal.getInduct
    | throwError "Expected inductive datatype: {recVal.getInduct}"
  let expr := mkConst recVal.name (recVal.levelParams.map Level.param)
  let res ← forallBoundedTelescope (← inferType expr) recVal.getMajorIdx fun xs _ => do
    let expr := mkAppN expr xs
    indVal.ctors.mapM fun ctorName => do
      let ctor ← mkAppOptM ctorName #[]
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
      return ⟨proof, eq, recVal.levelParams.toArray⟩
  return Array.mk res

def elabDefEq (name : Name) : TacticM (Array Lemma) := do
  match (← getEnv).find? name with
  | some (.recInfo val) =>
    -- Generate definitional equation for recursor
    addRecAsLemma val
  | some (.defnInfo _) =>
    -- Generate definitional equation for (possibly recursive) declaration
    match ← getEqnsFor? name (nonRec := true) with
    | some eqns => eqns.mapM fun eq => do elabLemma (← `($(mkIdent eq)))
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

structure ConstUnfoldInfo where
  name : Name
  val : Expr
  params : Array Name

def getConstUnfoldInfo (name : Name) : MetaM ConstUnfoldInfo := do
  let .some ci := (← getEnv).find? name
    | throwError "getConstUnfoldInfo :: Unknown declaration {name}"
  let .some val := ci.value?
    | throwError "getConstUnfoldInfo :: {name} is not a definition, thus cannot be unfolded"
  let val ← preprocessExpr val
  let params := ci.levelParams
  return ⟨name, val, ⟨params⟩⟩

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