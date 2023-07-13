import Lean
import Auto.Util.DeCompile
open Lean Elab Command

namespace Auto.Util

-- Given
-- 1. structure State where
--      <field1> : <ty1>
--      <field2> : <ty2>
--      ...
--      <field_k> : <ty_k>
-- 2. def SomeM := StateRefT State <lowM>, or
--    def SomeM := ReaderT Context (StateRefT State <lowM>)
-- We want Lean to automatically generate the following functions:
--
--    def get<field_i> : SomeM <ty_i> := do
--      return (← get).<field_i>
--
--    def set<field_i> (f : <ty_i>) : SomeM Unit :=
--      modify (fun s => {s with <field_i> := f})

syntax (name := genMonadGetSet) "#genMonadGetSet" ident ident : command

open Parser in
def runParserCategory (env : Environment) (catName : Name)
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

@[command_elab Auto.Util.genMonadGetSet]
def elabGenMonadGetSet : CommandElab := fun stx => withRef stx do
  match stx with
  | `(command | #genMonadGetSet $m:ident $s:ident) => do
    let names ← liftTermElabM <| (do
      let some m ← Term.resolveId? m
        | throwError s!"elabGenMonadGets :: Unknown identifier {m}"
      let some mi := (← getEnv).find? m.constName!
        | throwError s!"elabGenMonadGets :: Unknown identifier {m}"
      let .defnInfo _ := mi
        | throwError s!"elabGenMonadGets :: {m} is not a monad definition"
      let some s ← Term.resolveId? s
        | throwError s!"elabGenMonadGets :: Unknown identifier {s}"
      let some si := (← getEnv).find? s.constName!
        | throwError s!"elabGenMonadGets :: Unknown identifier {s}"
      let .inductInfo sval := si
        | throwError s!"elabGenMonadGets :: {s} is not an inductive definition, thus not a structure"
      if List.length sval.ctors != 1 then
        throwError s!"elabGenMonadGets :: {s} is not a structure"
      let smk := sval.ctors[0]!
      let some smk := (← getEnv).find? smk
        | throwError s!"elabGenMonadGets :: Unexpected Error"
      let .ctorInfo smkVal := smk
        | throwError s!"elabGenMonadGets :: Unexpected Error"
      let smkTy := smkVal.type
      return Expr.binders smkTy)
    let getIdent := mkIdentFrom stx "get"
    let unitIdent := mkIdentFrom stx "Unit"
    let modifyIdent := mkIdentFrom stx "modify"
    let st ← get
    let mut definedNames := #[]
    for (fname, ty, _) in names do
      let .str .anonymous s := fname
        | throwError s!"elabGenMonadGets :: Unexpected error, field name {fname} must be atomic"
      let tys : String ← liftCoreM (exprDeCompile ty)
      let pos := (SourceInfo.fromRef stx).getPos?.getD 0
      let tys := (List.range pos.byteIdx).foldl (fun s _ => s ++ " ") " " ++ tys
      let Except.ok tyStx := runParserCategory (← getEnv) `term tys (pos:=pos)
        | throwError s!"elabGenMonadGets :: Can't parse {tys} to term"
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
  | _ => throwUnsupportedSyntax

end Auto.Util