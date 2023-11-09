import Lean
import Auto.Lib.DeCompile
open Lean Elab Command

initialize
  registerTraceClass `auto.genMonadContext
  registerTraceClass `auto.genMonadState

namespace Auto

-- Given
-- 1. structure State (param₁ ... paramₙ) where
--      <field1> : <ty1>
--      <field2> : <ty2>
--      ...
--      <field_k> : <ty_k>
--    Put free variables used by `paramᵢ` in the local context
--      using the `variable` and `universe` command
-- 2. def SomeM := StateRefT State <lowM>, or
--    def SomeM := ReaderT Context (StateRefT State <lowM>)
-- We want Lean to automatically generate the following functions:
--
--    def get<field_i> : SomeM param₁ ... paramₙ <ty_i> := do
--      return (← get).<field_i>
--
--    def set<field_i> (f : <ty_i>) : SomeM param₁ ... paramₙ Unit :=
--      modify (fun s => {s with <field_i> := f})
--
-- using the command `#genMonadState (SomeM param₁ ... paramₙ)`
-- And generate the following functions:
--
--    def get<field_i> : SomeM param₁ ... paramₙ <ty_i> := do
--      return (← read).<field_i>
--
-- using the command `#genMonadContext (SomeM param₁ ⋯ paramₙ)`
-- 3. Make sure that
--    (1) No function with conflicting name has been declared
--    (2) When invoking `#genMonadState`, Lean's kernel is able to
--        synthesize `MonadState _ (SomeM param₁ ⋯ paramₙ)`
--    (3) When invoking `#genMonadContext`, Lean's kernel is able to
--        synthesize `MonadReader _ (SomeM param₁ ⋯ paramₙ)`

syntax (name := genMonadContext) "#genMonadContext" term : command
syntax (name := genMonadState) "#genMonadState" term : command

/--
  `instStructTy`: An expression of the form `<structure> param₁ param₂ ⋯ paramₙ`
  `Name`: The name of the structure
  `Expr`: <structure>.mk with parameters instantiated
  `Array (Name × Expr)`
    `Name`: Name of the field
    `Expr`: The projection function of this field, with parameters instantiated
-/
def structureProjs (structTy : Expr) : CoreM (Name × Expr × Array (Name × Expr)) := do
  let .const structName lvls := structTy.getAppFn
    | throwError s!"structureProjs :: Head symbol of {structTy} is not a constant"
  let some structInfo := getStructureInfo? (← getEnv) structName
    | throwError s!"structureProjs :: {structName} is not a structure"
  let .some (.inductInfo structi) := (← getEnv).find? structName
    | throwError s!"structureProjs :: Unknown identifier {structName}"
  let [structDotMk] := structi.ctors
    | throwError s!"structureProjs :: {structName} is not a structure"
  let structMkExpr := mkAppN (Expr.const structDotMk lvls) structTy.getAppArgs
  let tyArgs := structTy.getAppArgs
  let nameMap : HashMap Name StructureFieldInfo := HashMap.ofList
    (structInfo.fieldInfo.map (fun sfi => (sfi.fieldName, sfi))).data
  let sorted := structInfo.fieldNames.map (fun name => nameMap.find! name)
  let fieldInfos := sorted.map (fun i =>
      -- Field name, Projection function
      (i.fieldName, mkAppN (Expr.const i.projFn lvls) tyArgs))
  return (structName, structMkExpr, fieldInfos)

private def elabStx (stx : Term) : TermElabM Expr := do
  let expr ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  let e ← instantiateMVars expr
  if e.hasMVar then
    throwError "elabStx :: {e} contains metavariables"
  return e

private def addDefnitionValFromExpr (e : Expr) (name : Name) : MetaM Unit := do
    let ty ← Meta.inferType e
    let cstVal : ConstantVal := { name := name, levelParams := [], type := ty }
    -- We supply `.opaque` to `hints` because the functions we want to define
    --   are meant to be evaluated, not reduced. Although it's unlikely that
    --   any `isDefEq` call will find that the head of one of its arguments
    --   is the function we defined.
    let dfnVal : DefinitionVal := {cstVal with value := e, hints := .opaque, safety := .safe}
    addAndCompile (.defnDecl dfnVal)

private def elabGenMonadContextAux (m : Term) (stx : Syntax) : CommandElabM Unit := runTermElabM <| fun xs => do
  let mexpr ← elabStx m
  let .const mname _ := mexpr.getAppFn
    | throwError "elabGenMonadContext :: Unknown monad"
  let .str pre _ := mname
    | throwError "elabGenMonadContext :: {mname} is not a valid constant name"
  let pureInst ← elabStx (← `(inferInstanceAs (Pure $m)))
  let mctxInst ← elabStx (← `(inferInstanceAs (MonadReader _ $m)))
  let mctxInstTy ← Meta.inferType mctxInst
  -- The type of the context of the Monad (with parameters applied)
  let ctxTy := mctxInstTy.getArg! 0
  let (_, _, ctxFieldInfos) ← structureProjs ctxTy
  genMonadGets xs ctxTy pureInst mctxInst ctxFieldInfos pre
where
  genMonadGets (xs : Array Expr) (ctxTy : Expr) (pureInst : Expr) (mctxInst : Expr)
      (fieldInfos : Array (Name × Expr)) (pre : Name) : MetaM Unit :=
    for (fieldName, projFn) in fieldInfos do
      let getFnNameStr := "get" ++ fieldName.toString.capitalize
      let getFnName := Name.str pre getFnNameStr
      let bind₁ ← Meta.mkAppOptM ``read #[none, none, mctxInst]
      let bind₂ ← Meta.withLocalDecl `st .default ctxTy fun e => do
        let field := mkApp projFn e
        let purefield ← Meta.mkAppOptM ``pure #[none, pureInst, none, field]
        Meta.mkLambdaFVars #[e] purefield
      let fnBodyPre ← Meta.mkAppM ``bind #[bind₁, bind₂]
      let fnBodyPre ← Meta.mkLambdaFVars xs fnBodyPre (usedOnly := true)
      let fnBody ← instantiateMVars fnBodyPre
      trace[auto.genMonadContext] "{getFnName}"
      Elab.addDeclarationRanges getFnName stx
      addDefnitionValFromExpr fnBody getFnName

private def elabGenMonadStateAux (m : Term) (stx : Syntax) : CommandElabM Unit := runTermElabM <| fun xs => do
  let mexpr ← elabStx m
  let .const mname _ := mexpr.getAppFn
    | throwError "elabGenMonadState :: Unknown monad"
  let .str pre _ := mname
    | throwError "elabGenMonadState :: {mname} is not a valid constant name"
  let pureInst ← elabStx (← `(inferInstanceAs (Pure $m)))
  let mstateInst ← elabStx (← `(inferInstanceAs (MonadState _ $m)))
  let mstateInstTy ← Meta.inferType mstateInst
  -- The type of the state of the Monad (with parameters applied)
  let stateTy := mstateInstTy.getArg! 0
  let (_, stateMkExpr, stateFieldInfos) ← structureProjs stateTy
  genMonadGets xs stateTy pureInst mstateInst stateFieldInfos pre
  genMonadSets xs stateTy stateMkExpr mstateInst stateFieldInfos pre
where
  genMonadGets
      (xs : Array Expr) (stateTy : Expr) (pureInst : Expr) (mstateInst : Expr)
      (fieldInfos : Array (Name × Expr)) (pre : Name) : MetaM Unit :=
    for (fieldName, projFn) in fieldInfos do
      let getFnNameStr := "get" ++ fieldName.toString.capitalize
      let getFnName := Name.str pre getFnNameStr
      let bind₁ ← Meta.mkAppOptM ``get #[none, none, mstateInst]
      let bind₂ ← Meta.withLocalDecl `st .default stateTy fun e => do
        let field := mkApp projFn e
        let purefield ← Meta.mkAppOptM ``pure #[none, pureInst, none, field]
        Meta.mkLambdaFVars #[e] purefield
      let fnBodyPre ← Meta.mkAppM ``bind #[bind₁, bind₂]
      let fnBodyPre ← Meta.mkLambdaFVars xs fnBodyPre (usedOnly := true)
      let fnBody ← instantiateMVars fnBodyPre
      trace[auto.genMonadState] "{getFnName}"
      Elab.addDeclarationRanges getFnName stx
      addDefnitionValFromExpr fnBody getFnName
  genMonadSets
      (xs : Array Expr) (stateTy : Expr) (stateMkExpr : Expr) (mstateInst : Expr)
      (fieldInfos : Array (Name × Expr)) (pre : Name) : MetaM Unit := do
    let mut fieldCnt := 0
    for (fieldName, projFn) in fieldInfos do
      let setFnNameStr := "set" ++ fieldName.toString.capitalize
      let setFnName := Name.str pre setFnNameStr
      let fieldTy ← Meta.withLocalDecl `e .default stateTy fun e => do
        let field := mkApp projFn e
        Meta.inferType field
      let fnBodyPre ← Meta.withLocalDecl `field .default fieldTy <| fun f =>
        (Meta.withLocalDecl `st .default stateTy fun e => do
          let allFields := fieldInfos.map (fun fi => mkApp fi.snd e)
          let modified := allFields.modify fieldCnt (fun _ => f)
          let insideModify ← Meta.mkLambdaFVars #[e] (mkAppN stateMkExpr modified)
          let modifyBody ← Meta.mkAppOptM ``modify #[none, none, mstateInst, insideModify]
          Meta.mkLambdaFVars #[f] modifyBody)
      let fnBody := ← instantiateMVars (← Meta.mkLambdaFVars xs fnBodyPre (usedOnly := true))
      trace[auto.genMonadState] "{setFnName}"
      Elab.addDeclarationRanges setFnName stx
      addDefnitionValFromExpr fnBody setFnName
      fieldCnt := fieldCnt + 1

@[command_elab Auto.genMonadContext]
def elabGenMonadContext : CommandElab := fun stx => withRef stx do
  match stx with
  | `(command | #genMonadContext $m:term) =>
    elabGenMonadContextAux m stx
  | _ => throwUnsupportedSyntax

@[command_elab Auto.genMonadState]
def elabGenMonadState : CommandElab := fun stx => withRef stx do
  match stx with
  | `(command | #genMonadState $m:term) =>
    elabGenMonadStateAux m stx
  | _ => throwUnsupportedSyntax

end Auto
