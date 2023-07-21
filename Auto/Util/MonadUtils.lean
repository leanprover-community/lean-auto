import Lean
import Auto.Util.DeCompile
open Lean Elab Command

namespace Auto.Util

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
-- using the command `#genMonadGetSet (SomeM param₁ ... paramₙ)`

syntax (name := genMonadGetSet) "#genMonadGetSet" term : command

private def elabGenMonadGetSetAux (m : Term) : CommandElab := fun stx => runTermElabM <| fun xs => do
  let mexpr ← elabStx m
  let .const mname _ := mexpr.getAppFn
    | throwError "elabGenMonadGetSet :: Unknown monad"
  let .str pre _ := mname
    | throwError "elabGenMonadGetSet :: {mname} is not a valid constant name"
  let mInst ← elabStx (← `(inferInstanceAs (Monad $m)))
  let pureInst ← elabStx (← `(inferInstanceAs (Pure $m)))
  let mstateInst ← elabStx (← `(inferInstanceAs (MonadState _ $m)))
  -- `instTy = MonadState <state> <monad>`
  let mstateInstTy ← Meta.inferType mstateInst
  -- The type of the state of the Monad (with parameters applied)
  let stateTy := mstateInstTy.getArg! 0
  let .const stateConst lvls := stateTy.getAppFn
    | throwError s!"elabGenMonadGetSet :: Head symbol of {stateTy} is not a constant"
  let some stateStructInfo := getStructureInfo? (← getEnv) stateConst
    | throwError s!"elabGenMonadGetSet :: {stateConst} is not a structure"
  let .some (.inductInfo statei) := (← getEnv).find? stateConst
    | throwError s!"elabGenMOnadGetSet :: Unknown identifier {stateConst}"
  let [stateDotMk] := statei.ctors
    | throwError s!"elabGenMonadGetSet :: {stateConst} is not a structure"
  let stateMkExpr := mkAppN (Expr.const stateDotMk lvls) stateTy.getAppArgs
  let tyArgs := stateTy.getAppArgs
  let fieldInfos ← (do
    let nameMap : HashMap Name StructureFieldInfo := HashMap.ofList
      (stateStructInfo.fieldInfo.map (fun sfi => (sfi.fieldName, sfi))).data
    let sorted := stateStructInfo.fieldNames.map (fun name => nameMap.find! name)
    return sorted.map (fun i =>
      -- Field name, Projection function
      (i.fieldName, mkAppN (Expr.const i.projFn lvls) tyArgs))
  )
  genMonadGets xs stateTy pureInst mstateInst fieldInfos pre
  genMonadSets xs stateTy stateMkExpr mstateInst fieldInfos pre
where
  elabStx (stx : Term) : TermElabM Expr := do
    let expr ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    let e ← instantiateMVars expr
    if e.hasMVar then
      throwError "genMonadGetSet :: {e} contains metavariables"
    return e
  -- Note that `e` might contain free variables
  addDefnitionValFromExpr (e : Expr) (name : Name) : MetaM Unit := do
    let ty ← Meta.inferType e
    let cstVal : ConstantVal := { name := name, levelParams := [], type := ty }
    -- **TODO:** What argument to supply to `.regular`?
    let dfnVal : DefinitionVal := {cstVal with value := e, hints := .opaque, safety := .safe}
    addAndCompile (.defnDecl dfnVal)
  genMonadGets
      (xs : Array Expr) (stateTy : Expr) (pureInst : Expr) (mstateInst : Expr)
      (fieldInfos : Array (Name × Expr))
      (pre : Name) : MetaM Unit :=
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
      IO.println s!"genMonadGets :: {getFnName}"
      addDefnitionValFromExpr fnBody getFnName
  genMonadSets
      (xs : Array Expr) (stateTy : Expr) (stateMkExpr : Expr) (mstateInst : Expr)
      (fieldInfos : Array (Name × Expr))
      (pre : Name) : MetaM Unit := do
    let mut fieldCnt := 0
    IO.println (fieldInfos.map (fun x => x.1))
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
      IO.println s!"getMonadSets :: {setFnName}"
      addDefnitionValFromExpr fnBody setFnName
      fieldCnt := fieldCnt + 1

@[command_elab Auto.Util.genMonadGetSet]
def elabGenMonadGetSet : CommandElab := fun stx => withRef stx do
  match stx with
  | `(command | #genMonadGetSet $m:term) =>
    elabGenMonadGetSetAux m stx
  | _ => throwUnsupportedSyntax

end Auto.Util