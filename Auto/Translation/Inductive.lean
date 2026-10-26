module

public import Lean
public import Auto.Lib.ExprExtra
public import Auto.Lib.MessageData
public import Auto.Lib.MetaExtra
public import Auto.Lib.MonadUtils
public import Auto.Translation.Reduction

public section

open Lean

initialize
  registerTraceClass `auto.collectInd

namespace Auto

/--
  Test whether a given inductive type is explicitly and inductive family.
  i.e., return `false` iff `numParams` match the number of arguments of
    the type constructor
-/
def isFamily (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "{decl_name%} :: {tyctorname} is not a type constructor"
  return (Expr.forallBinders val.type).size != val.numParams

/--
  Test whether a given inductive type is an inductively defined proposition
-/
def isIndProp (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "{decl_name%} :: {tyctorname} is not a type constructor"
  (Meta.withTransparency (n := MetaM) .all <|
    Meta.forallTelescopeReducing val.type fun _ body =>
      Meta.isDefEq body (.sort .zero)).run' {}

/--
  Whether the constructor is monomorphic after all parameters are instantiated.
-/
def isSimpleCtor (ctorname : Name) : CoreM Bool := do
  let .some (.ctorInfo val) := (← getEnv).find? ctorname
    | throwError "{decl_name%} :: {ctorname} is not a type constructor"
  Meta.MetaM.run' <| Meta.forallBoundedTelescope val.type val.numParams fun _ body =>
    pure ((Expr.depArgs body).size == 0)

/--
  Returns true iff the inductive type is not explicitly an inductive family,
    and all constructors of this inductive type are simple (refer to `isSimpleCtor`)
-/
def isSimpleInductive (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "{decl_name%} :: {tyctorname} is not a type constructor"
  return (← val.ctors.allM isSimpleCtor) && !(← isFamily tyctorname)

structure SimpleIndVal where
  /-- Name of type constructor -/
  name : Name
  /-- Instantiated type constructor -/
  type : Expr
  /-- Array of `(instantiated_ctor, type_of_instantiated_constructor)` -/
  ctors : Array (Expr × Expr)
  /-- Instantiated projections -/
  projs : Option (Array Expr)

instance : ToMessageData SimpleIndVal where
  toMessageData siv :=
    m!"SimpleIndVal ⦗⦗ {siv.type}, Ctors : " ++
      MessageData.array siv.ctors (fun (e₁, e₂) => m!"{e₁} : {e₂}") ++
      (match siv.projs with
       | .some arr =>
         ", Projs : " ++ MessageData.array arr (fun e => m!"{e}")
       | .none => m!"") ++
      m!" ⦘⦘"

def SimpleIndVal.zetaReduce (si : SimpleIndVal) : MetaM SimpleIndVal := do
  let ⟨name, type, ctors, projs⟩ := si
  let ctors ← ctors.mapM (fun (val, ty) => do return (← Meta.zetaReduce val, ← Meta.zetaReduce ty))
  let projs ← projs.mapM (fun arr => arr.mapM Meta.zetaReduce)
  return ⟨name, ← Meta.zetaReduce type, ctors, projs⟩

/--
  An instantiated mutual block of simple inductive types, together with the
    types nested in the constructors of the block
-/
structure SimpleMutIndVal where
  /-- The types of the block, in the order of `InductiveVal.all` -/
  vals   : Array SimpleIndVal
  /--
    The types nested in the constructors of `vals` (e.g. `List Tr` for
      `inductive Tr | node : List Tr → Tr`), in the order of the motives of the
      recursors of `vals` (see `Lean.Elab.Structural.IndGroupInst.nestedTypeFormers`)
  -/
  nested : Array Expr

instance : ToMessageData SimpleMutIndVal where
  toMessageData smiv := m!"{smiv.vals}, Nested : {smiv.nested}"

/--
  For a given type constructor `tyctor`, `CollectIndState[tyctor]`
    is an array of `(instantiated_tyctor, [SimpleIndVal associated to tyctor])`
-/
structure CollectInduct.State where
  recorded : Std.HashMap Name (Array Expr)     := {}
  sis      : Array (Array SimpleIndVal) := #[]

abbrev IndCollectM := StateRefT CollectInduct.State MetaM

#genMonadState IndCollectM

private def collectSimpleInduct
  (tyctor : Name) (lvls : List Level) (args : Array Expr) : MetaM SimpleIndVal := do
  let .some (.inductInfo val) := (← getEnv).find? tyctor
    | throwError "{decl_name%} :: Unexpected error"
  let ctors ← (Array.mk val.ctors).mapM (fun ctorname => do
    let instctor := mkAppN (Expr.const ctorname lvls) args
    let type ← Meta.inferType instctor
    let type ← prepReduceExpr type
    return (instctor, type))
  let env ← getEnv
  let projs ← (getStructureInfo? env tyctor).mapM (fun si => do
    si.fieldNames.mapM (fun fieldName => do
      let .some projFn := getProjFnForField? env tyctor fieldName
        | throwError "{decl_name%} :: Unexpected error"
      return mkAppN (Expr.const projFn lvls) args))
  return ⟨tyctor, mkAppN (Expr.const tyctor lvls) args, ctors, projs⟩

mutual

  private partial def collectAppInstSimpleInduct (e : Expr) : IndCollectM Unit := do
    let .const tyctor lvls := e.getAppFn
      | return
    let .some (.inductInfo val) := (← getEnv).find? tyctor
      | return
    if !(← @id (CoreM _) (val.all.allM isSimpleInductive)) then
      trace[auto.collectInd] (m!"Warning : {tyctor} or some type within the " ++
        "same mutual block is not a simple inductive type. Ignoring it ...")
      return
    /-
      Do not translate typeclasses as inductive types
      Mathlib has a complex typeclass hierarchy, so translating typeclasses might make a mess
    -/
    if Lean.isClass (← getEnv) tyctor then
      return
    let args := e.getAppArgs
    if args.size != val.numParams then
      trace[auto.collectInd] "Warning : Parameters of {tyctor} in {e} is not fully instantiated. Ignoring it ..."
      return
    if !(← getRecorded).contains tyctor then
      setRecorded ((← getRecorded).insert tyctor #[])
    let .some arr := (← getRecorded).get? tyctor
      | throwError "{decl_name%} :: Unexpected error"
    for e' in arr do
      if ← Meta.isDefEq e e' then
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
  | .letE .. => throwError "{decl_name%} :: Let-expressions should have been reduced"
  | .mdata .. => throwError "{decl_name%} :: mdata should have been consumed"
  | .proj .. => throwError "{decl_name%} :: Projections should have been turned into ordinary expressions"
  | e => collectAppInstSimpleInduct e

end

/--
  The types nested in the constructors of the instantiated mutual block `vals`,
    in the order of the motives of the recursors of the block
-/
def nestedTypes (vals : Array SimpleIndVal) : MetaM (Array Expr) := do
  let .some val := vals[0]?
    | return #[]
  let .const tyctor lvls := val.type.getAppFn
    | throwError "{decl_name%} :: {val.type} is not an instantiated type constructor"
  let .inductInfo indVal ← getConstInfo tyctor
    | throwError "{decl_name%} :: {tyctor} is not a type constructor"
  let igi : Elab.Structural.IndGroupInst :=
    { Elab.Structural.IndGroupInfo.ofInductiveVal indVal with levels := lvls, params := val.type.getAppArgs }
  igi.nestedTypeFormers

/--
  Collect the instantiated mutual blocks of simple inductive types in `es`. The
    blocks that a block depends on come before it, except for the blocks of its
    nested types
-/
def collectExprsSimpleInduct (es : Array Expr) : MetaM (Array SimpleMutIndVal) := do
  let (_, st) ← (es.mapM collectExprSimpleInduct).run {}
  st.sis.mapM fun vals => do return ⟨vals, ← nestedTypes vals⟩

end Auto

/-
section Test

  private def skd (e : Expr) : Elab.Term.TermElabM Unit := do
    let (_, st) ← (Auto.collectExprSimpleInduct (Auto.Expr.eraseMData e)).run {}
    for siw in st.sis do
      for si in siw do
        logInfo m!"{si}"

  #getExprAndApply[List.cons 2|skd]
  #getExprAndApply[(Array Bool × Array Nat)|skd]

  mutual

    private inductive tree where
      | leaf : Nat → tree
      | node : treelist → tree

    private inductive treelist where
      | nil : treelist
      | cons : tree → treelist → treelist

  end

  #getExprAndApply[tree|skd]

  mutual

    private inductive Tree (α : Type u) where
      | leaf : α → Tree α
      | node : TreeList α → Tree α

    private inductive TreeList (α : Type u) where
      | nil : TreeList α
      | cons : Tree α → TreeList α → TreeList α

  end

  #getExprAndApply[Tree Int|skd]

end Test
-/
