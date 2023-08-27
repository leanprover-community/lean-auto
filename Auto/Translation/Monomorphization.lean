import Lean
import Auto.Embedding.Lift
import Auto.Translation.Assumptions
import Auto.Lib.ExprExtra
open Lean

initialize
  registerTraceClass `auto.monomorphization

namespace Auto.Monomorphization
open Embedding

-- If a constant `c` is of type `∀ (xs : αs), t`,
--   then its valid instance will be `c` with all of its
--   universe levels and dependent arguments instantiated.
--   So, we record the instantiation of universe levels
--   and dependent arguments.
structure ConstInst where
  params  : Array Level
  depargs : Array Expr
  
-- Array of instances of a polymorphic constant
abbrev ConstInsts := Array ConstInst

-- Array of instances of assumption
-- If assumption `H : ∀ (xs : αs), t`, then its instance will be like
--   `⟨ys.length, fun (ys : βs) => t, (∀ (ys : βs), ty), params⟩`
abbrev AssumptionInsts := Array (Nat × Lemma)

/-
  Monomorphization works as follows:
  (1) Compute the number of `∀` binders for each input assumption.
      They form the initial elements of `asMap`
  (2) Scan through all assumptions to find subterms that are
      valid instances of constants (dependent arguments fully
      instantiated). They form the initial elements of `ciMap`
      and `activeCi`
  (3) Repeat:
      · Dequeue an element `(name, n)` from `activeCi`
      · For each element `ais : AssumptionInsts` in `asMap`,
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
  -- Dependent arguments of a constant
  cdepargs : HashMap Name (Array Nat)
  ciMap    : HashMap Name ConstInsts
  activeCi : Std.Queue (Name × Nat)
  asMap    : Array AssumptionInsts

def State.dequeueActiveCi (s : State) : Option ((Name × Nat) × State) :=
  match s.activeCi.dequeue? with
  | .some (elem, a') => .some (elem, {s with activeCi := a'})
  | .none => .none

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
          trace[auto.monomorphization] "Monomorphized: {fact.fst} : {fact.snd}"
        for (expr, fvar) in hmap.toList do
          trace[auto.monomorphization] "Expression {expr} turned into {Expr.fvar fvar}"
        cont hmap mfacts
      )
    cont' HashMap.empty #[]
  else
    cont HashMap.empty facts
  

end Auto.Monomorphization