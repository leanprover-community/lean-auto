import Lean
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
import Auto.Lib.MonadUtils
open Lean

initialize
  registerTraceClass `auto.collectInd

namespace Auto.Inductive

/--
  Test whether a given inductive type is explicitly and inductive family.
  i.e., return `false` iff `numParams` match the number of arguments of
    the type constructor 
-/
def isFamily (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "isFamily :: {tyctorname} is not a type constructor"
  return (Expr.forallBinders val.type).size != val.numParams

/--
  Whether the constructor is monomorphic after all parameters are instantiated.
-/
def isSimpleCtor (ctorname : Name) : CoreM Bool := do
  let .some (.ctorInfo val) := (← getEnv).find? ctorname
    | throwError "isSimpleCtor :: {ctorname} is not a type constructor"
  Meta.MetaM.run' <| Meta.forallBoundedTelescope val.type val.numParams fun _ body =>
    pure ((Expr.depArgs body).size == 0)

/--
  Returns true iff the inductive type is not explicitly an inductive family,
    and all constructors of this inductive type are simple (refer to `isSimpleCtor`)
-/
def isSimple (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "isSimple :: {tyctorname} is not a type constructor"
  return (← val.ctors.allM isSimpleCtor) && !(← isFamily tyctorname)

structure SimpleInductVal where
  /-- Instantiated type constructor -/
  type : Expr
  /-- Array of `(instantiated_ctor, type_of_instantiated_constructor)` -/
  ctors : Array (Expr × Expr)

/--
  For a given type constructor `tyctor`, `CollectIndState[tyctor]`
    is an array of `(instantiated_tyctor, [simpleinductval associated to tyctor])`
-/
structure State where
  recorded : HashMap Name (Array Expr)     := {}
  sis      : Array (Array SimpleInductVal) := #[]

abbrev IndCollectM := StateRefT State MetaM

#genMonadState IndCollectM

private def collectSimpleInduct
  (tyctor : Name) (lvls : List Level) (args : Array Expr) : MetaM SimpleInductVal := do
  let .some (.inductInfo val) := (← getEnv).find? tyctor
    | throwError "collectSimpleInduct :: Unexpected error"
  let ctors ← (Array.mk val.ctors).mapM (fun ctorname => do
    let instctor := mkAppN (Expr.const ctorname lvls) args
    let type ← Meta.inferType instctor
    return (instctor, type))
  return ⟨mkAppN (Expr.const tyctor lvls) args, ctors⟩

mutual

  private partial def collectAppInstSimpleInduct (e : Expr) : IndCollectM Unit := do
    let .const tyctor lvls := e.getAppFn
      | return
    let .some (.inductInfo val) := (← getEnv).find? tyctor
      | return
    if !(← isSimple tyctor) then
      trace[auto.collectInd] "Warning : {tyctor} is not a simple inductive type. Ignoring it ..."
      return
    -- Do not translate typeclasses as inductive types
    if Lean.isClass (← getEnv) tyctor then
      return
    let args := e.getAppArgs
    if args.size != val.numParams then
      trace[auto.collectInd] "Warning : Parameters of {tyctor} in {e} is not fully instantiated. Ignoring it ..."
      return
    if !(← getRecorded).contains tyctor then
      setRecorded ((← getRecorded).insert tyctor #[])
    let .some arr := (← getRecorded).find? tyctor
      | throwError "collectAppInstSimpleInduct :: Unexpected error"
    for e' in arr do
      if ← Meta.withDefault <| Meta.isDefEq e e' then
        return
    for tyctor' in val.all do
      setRecorded ((← getRecorded).insert tyctor' (arr.push (mkAppN (.const tyctor' lvls) args)))
    let mutualInductVal ← val.all.mapM (collectSimpleInduct · lvls args)
    for inductval in mutualInductVal do
      for (_, type) in inductval.ctors do
        collectExprSimpleInduct type
    setSis ((← getSis).push ⟨mutualInductVal⟩)

  partial def collectExprSimpleInduct : Expr → IndCollectM Unit
  | e@(.app ..) => do
    collectAppInstSimpleInduct e
    let _ ← e.getAppArgs.mapM collectExprSimpleInduct
  | e@(.lam ..) => do trace[auto.collectInd] "Warning : Ignoring lambda expression {e}"
  | e@(.forallE _ ty body _) => do
    if body.hasLooseBVar 0 then
      trace[auto.collectInd] "Warning : Ignoring forall expression {e}"
      return
    collectExprSimpleInduct ty
    collectExprSimpleInduct body
  | .letE .. => throwError "collectExprSimpleInduct :: Let-expressions should have been reduced"
  | .mdata .. => throwError "collectExprSimpleInduct :: mdata should have been consumed"
  | .proj .. => throwError "collectExprSimpleInduct :: Projections should have been turned into ordinary expressions"
  | e => collectAppInstSimpleInduct e

end

end Auto.Inductive

namespace Test

  def skd (e : Expr) : Elab.Term.TermElabM Unit := do
    let (_, st) ← (Auto.Inductive.collectExprSimpleInduct (Auto.Expr.eraseMData e)).run {}
    for siw in st.sis do
      IO.println "New"
      for si in siw do
        IO.println ("  " ++ si.type.dbgToString ++ " ||" ++ String.join (si.ctors.data.map (fun a => s!" ({Expr.dbgToString (Prod.fst a)}, {Expr.dbgToString (Prod.snd a)})")))
  

  #check Meta.isClass?
  #getExprAndApply[List.cons 2|skd]
  #getExprAndApply[(Array Bool × Array Nat)|skd]

  mutual
    
    inductive tree where
      | leaf : Nat → tree
      | node : treelist → tree

    inductive treelist where
      | nil : treelist
      | cons : tree → treelist → treelist

  end

  #getExprAndApply[tree|skd]

end Test
