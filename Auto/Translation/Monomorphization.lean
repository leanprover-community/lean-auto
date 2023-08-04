import Lean
import Auto.Embedding.Lift
open Lean

initialize
  registerTraceClass `auto.monomorphization

namespace Auto.Monomorphization
open Embedding

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
| e => return HashSet.empty

-- For test purpose
def addpolylog (e : Expr) (cont : HashMap Expr FVarId → MetaM α)
  (hmap : HashMap Expr FVarId) : MetaM α := do
  let fvarid ← mkFreshId
  let name := "_pl_" ++ fvarid.toString
  Meta.withLetDecl name (← Meta.inferType e) e fun fvar =>
    cont (hmap.insert e fvar.fvarId!)

-- For test purpose
partial def replacepolylog (hmap : HashMap Expr FVarId) : Expr → MetaM Expr
| e@(.app (.const ``Eq _) _) => return .fvar (hmap.find! e)
| e@(.app (.const ``Exists _) _) => return .fvar (hmap.find! e)
| .forallE name ty body binfo => do
  let tylvl := (← instantiateMVars (← Meta.inferType ty)).sortLevel!
  let (bodysort, rep) ← Meta.withLocalDecl name binfo ty fun fvar => do
    let body' := body.instantiate1 fvar
    let bodysort ← Meta.inferType body'
    let bodyrep ← replacepolylog hmap body'
    return (bodysort, ← Meta.mkLambdaFVars #[fvar] bodyrep)
  let bodylvl := (← instantiateMVars bodysort).sortLevel!
  if body.hasLooseBVar 0 ∨ !(← Meta.isLevelDefEq tylvl .zero) ∨ !(← Meta.isLevelDefEq bodylvl .zero) then
    let forallFun := Expr.fvar (hmap.find! (.app (.const ``forallF [tylvl, bodylvl]) ty))
    return .app forallFun rep
  else
    let impFun := Expr.fvar (hmap.find! (.const ``ImpF [tylvl, bodylvl]))
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
    let hmap' := hmap₀.toList.foldl (fun hm (key, val) => hm.insert key val) hmap
    cont hmap' (arr.push (proof, ← replacepolylog hmap ty))) HashMap.empty

-- For test purpose
-- This function's semantics is incorrect. A full-fleged version should run
--   in `Reif.ReifM` and modify `fvarsToAbstract` and `iPolyLog` simultaneously
def collectPolyLog (cont : HashMap Expr FVarId → Array (Expr × Expr) → MetaM α)
  (facts : Array ((Expr × Expr))) : MetaM α := do
  if testCollectPolyLog.get (← getOptions) then
    let cont' := facts.foldl (β := HashMap Expr FVarId → Array (Expr × Expr) → MetaM α)
      (fun cont' fact => collectPolyLogAux fact cont') (fun hmap mfacts => do
        for fact in mfacts do
          trace[auto.monomorphization] "Monomorphized: {fact.fst} : {fact.snd}"
        cont hmap mfacts
      )
    cont' HashMap.empty #[]
  else
    cont HashMap.empty facts
  

end Auto.Monomorphization