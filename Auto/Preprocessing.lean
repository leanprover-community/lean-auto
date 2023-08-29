import Lean
import Auto.Lib.AbstractMVars
import Auto.Lib.MessageData
import Auto.Translation.Assumptions
open Lean Meta Elab Tactic

initialize
  registerTraceClass `auto.Prep

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

/-- This function is expensive and should only be used in preprocessing -/
partial def preprocessTerm (term : Expr) : MetaM Expr := do
  let red (e : Expr) : MetaM TransformStep := do
    let e := e.consumeMData
    let e ← Meta.whnf e
    return .continue e
  -- Reduce
  let term ← Meta.withTransparency .instances <| Meta.transform term (pre := red) (usedLetOnly := false)
  let redProj (e : Expr) : MetaM TransformStep := do
    let e ← unfoldProj e
    return .continue e
  let term ← Meta.withTransparency .instances <| Meta.transform term (pre := redProj)
  return term

-- **TODO**: Review
-- Advise: For each recursive function (not only recursors)
--   `f : {recty} → ...`, apply
--   `f` to each constructor of {recty} and beta reduce!
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
      let eq ← instantiateMVars (← mkLambdaFVars xs eq)
      return ⟨proof, eq, recVal.levelParams.toArray⟩
  return Array.mk res

/-- From a user-provided term `stx`, produce a lemma -/
def elabLemma (stx : Term) : TacticM (Array Lemma) := do
  match stx with
  | `($id:ident) =>
    let some expr ← Term.resolveId? id
      | throwError "Unknown identifier {id}"

    let some cstname := expr.constName?
      | return #[← lctxHyp expr]

    match (← getEnv).find? cstname with
    | some (.recInfo val) => addRecAsLemma val
    | some (.defnInfo defval) =>
      let term := defval.value
      let type ← Meta.inferType term
      let sort ← Meta.reduce (← Meta.inferType type) true true false
      -- If the type is of sort `Prop`, add itself as a type
      let mut ret := #[]
      if sort.isProp then
        ret := ret.push (← elabLemmaAux stx)
      -- Generate definitional equation for the type
      if let some eqns ← getEqnsFor? cstname (nonRec := true) then
        ret := ret.append (← eqns.mapM fun eq => do elabLemmaAux (← `($(mkIdent eq))))
      return ret
    | some (.axiomInfo _)  => return #[← elabLemmaAux stx]
    | some (.thmInfo _)    => return #[← elabLemmaAux stx]
    -- If we have inductively defined propositions, we might
    --   need to add constructors as lemmas
    | some (.ctorInfo _)   => return #[← elabLemmaAux stx]
    | some (.opaqueInfo _) => throwError "Opaque constants cannot be provided as lemmas"
    | some (.quotInfo _)   => throwError "Quotient constants cannot be provided as lemmas"
    | some (.inductInfo _) => throwError "Inductive types cannot be provided as lemmas"
    | none => throwError "Unknown constant {cstname}"
  | _ => return #[← elabLemmaAux stx]
where
  elabLemmaAux (stx : Term) : TacticM Lemma :=
    -- elaborate term as much as possible and abstract any remaining mvars:
    Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
      let e ← instantiateMVars e
      let abstres ← Auto.abstractMVars e
      let e := abstres.expr
      let paramNames := abstres.paramNames
      return Lemma.mk e (← inferType e) paramNames
  lctxHyp (e : Expr) : TacticM Lemma := do
    let some localDecl := (← getLCtx).findFVar? e
      | throwError "elabLemma :: Identifier {e} is neither a constant nor a local hypothesis"
    if ← Meta.isProp localDecl.type then
      return Lemma.mk e localDecl.type #[]
    else if localDecl.isLet then
      let proof ← mkAppM ``Eq.refl #[e]
      let type  ← mkAppM ``Eq #[e, localDecl.value]
      return Lemma.mk proof type #[]
    else
      throwError "elabLemma :: Local hypothesis {e} is neither a let declaration nor a proof of proposition"

end Prep

end Auto