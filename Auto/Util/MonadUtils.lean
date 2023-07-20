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

open Parser in
private def runParserCategory (env : Environment) (catName : Name)
    (input : String) (fileName := "<input>") (pos : String.Pos) : Except String Syntax :=
  let p := andthenFn whitespace (categoryParserFnImpl catName)
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) { cache := initCacheForInput input, pos := pos }
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

private def elabGenMonadGetSetAux (m : Term) : CommandElab :=
  fun stx => do
    let (mexpr, tyInfos) ← withoutModifyingEnv <| runTermElabM <| (fun _ => do
      let mexpr ← Term.elabTerm m none
      let mexpr ← postElabTerm mexpr
      let inferInst ← Term.elabTerm (←`(inferInstanceAs (MonadState _ $m))) none
      let inst ← postElabTerm inferInst
      -- `instTy = MonadState <state> <monad>`
      let instTy ← Meta.inferType inst
      -- The type of the state of the Monad
      let stateTy := instTy.getArg! 0
      let .const stateConst lvls := stateTy.getAppFn
        | throwError s!"elabGenMonadGetSet :: Head symbol of {stateTy} is not a constant"
      let some stateInfo := (← getEnv).find? stateConst
        | throwError s!"elabGenMonadGetSet :: Unkown constant {stateConst}"
      let .inductInfo stateInfo := stateInfo
        | throwError s!"elabGenMonadGetSet :: {stateConst} is not a structure"
      let [smk] := stateInfo.ctors
        | throwError s!"elabGenMonadGetSet :: {stateConst} is not a structure"
      let smkExpr := mkAppN (.const smk lvls) stateTy.getAppArgs
      let binderInfos := Expr.binders (← Meta.inferType smkExpr)
      let mut infos := #[]
      for (fname, ty, _) in binderInfos do
        infos := infos.push (fname, ← exprDeCompile ty)
        IO.println (← exprDeCompile ty)
      return (mexpr, infos))
    let getIdent := mkIdentFrom stx "get"
    let unitIdent := mkIdentFrom stx "Unit"
    let modifyIdent := mkIdentFrom stx "modify"
    let st ← get
    let mut definedNames := #[]
    -- `fname` : Field name
    for (fname, tystr) in tyInfos do
      let .str .anonymous s := fname
        | throwError s!"elabGenMonadGetSet :: Unexpected error, field name {fname} must be atomic"
      let pos := (SourceInfo.fromRef stx).getPos?.getD 0
      let tystr := (List.range pos.byteIdx).foldl (fun s _ => s ++ " ") " " ++ tystr
      let Except.ok tyStx := runParserCategory (← getEnv) `term tystr (pos:=pos)
        | throwError s!"elabGenMonadGetSet :: Can't parse {tystr} to term"
      let tyStx : TSyntax `term := ⟨tyStx⟩
      let getDefName : String := "get" ++ s.capitalize
      let getDefIdent := mkIdentFrom stx getDefName
      let setDefName : String := "set" ++ s.capitalize
      let setDefIdent := mkIdentFrom stx setDefName
      let fnameIdent := mkIdentFrom stx fname
      let getCmd ←
       `(def $getDefIdent : $m ($tyStx) := do
          return (← $getIdent).$fnameIdent)
      elabCommand getCmd
      definedNames := definedNames.push ("genMonadGetSet :: " ++ getDefName)
      let structLVal := Syntax.node SourceInfo.none ``Parser.Term.structInstLVal
          #[mkIdentFrom stx fname, Syntax.node SourceInfo.none `null #[]]
      let structLVal := ⟨structLVal⟩
      let setCmd ← withoutModifyingEnv <| do
       `(def $setDefIdent (f : $tyStx) : $m $unitIdent :=
          $modifyIdent (fun s => {s with $structLVal := f}))
      elabCommand setCmd
      definedNames := definedNames.push ("genMonadGetSet :: " ++ setDefName)
    logInfoAt stx (String.intercalate "\n" definedNames.data)
    modify (fun s => { s with infoState := st.infoState, traceState := st.traceState })
where
  postElabTerm (expr : Expr) : TermElabM Expr := do
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    let e ← instantiateMVars expr
    if e.hasMVar then
      throwError "genMonadGetSet :: {e} contains metavariables"
    return e

@[command_elab Auto.Util.genMonadGetSet]
def elabGenMonadGetSet : CommandElab := fun stx => withRef stx do
  match stx with
  | `(command | #genMonadGetSet $m:term) =>
    elabGenMonadGetSetAux m stx
  | _ => throwUnsupportedSyntax

#genMonadGetSet CoreM

section We

  -- Type of (identifiers in higher-level logic)
  variable (ω : Type) [i1 : BEq ω] [i2 : Hashable ω]

  -- The main purpose of this state is for name generation
  --   and symbol declaration/definition, so we do not distinguish
  --   between sort identifiers, datatype identifiers
  --   and function identifiers
  structure State where
    -- Map from high-level construct to symbol
    h2lMap : HashMap ω String    := HashMap.empty
    -- Inverse of `h2lMap`
    -- Map from symbol to high-level construct
    l2hMap : HashMap String ω    := HashMap.empty
    -- State of low-level name generator
    --   To avoid collision with keywords, we only
    --   generate non-annotated identifiers `smti_<idx>`
    idx       : Nat              := 0
    -- List of commands
    commands  : Array Command    := #[]

  abbrev TransM := StateRefT (State ω) MetaM

  #genMonadGetSet (TransM ω)

end We

end Auto.Util