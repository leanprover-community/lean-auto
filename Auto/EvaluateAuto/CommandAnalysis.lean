import Lean
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.Result
open Lean

register_option auto.evalAuto.ensureAesop : Bool := {
  defValue := false
  descr := "Enable/Disable enforcement of importing `aesop`"
}

namespace EvalAuto

open Elab Frontend

def processHeaderEnsuring (header : Syntax) (opts : Options) (messages : MessageLog)
    (inputCtx : Parser.InputContext) (trustLevel : UInt32 := 0) (leakEnv := false) (ensuring : Array Import := #[])
    : IO (Environment × MessageLog) := do
  try
    let env ← importModules (leakEnv := leakEnv) (headerToImports header ++ ensuring) opts trustLevel
    pure (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let spos := header.getPos?.getD 0
    let pos  := inputCtx.fileMap.toPosition spos
    pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos })

def runWithEffectOfCommandsCore
  (cnt? : Option Nat)
  (action : Context → State → State → ConstantInfo → IO (Option α)) : FrontendM (Array α) := do
  let mut done := false
  let mut ret := #[]
  let mut cnt := 0
  while !done do
    if cnt?.isSome && cnt >= cnt?.getD 0 then
      break
    let prev ← get
    done ← Frontend.processCommand
    let post ← get
    let newConsts := Environment.newLocalConstants prev.commandState.env post.commandState.env
    for newConst in newConsts do
      if let .some result ← action (← read) prev post newConst then
        cnt := cnt + 1
        ret := ret.push result
        if cnt?.isSome && cnt >= cnt?.getD 0 then
          break
  return ret

/--
  Given a Lean4 file `fileName` with content `input` consisting of
  a header and a series of commands, first parse the header. Then,
  for each command `cmd`, record the states `st₁, st₂` before and
  after executing the command, and run `action` on the `ConstantInfo`s produced
  by `cmd`, together with `st₁, st₂` and the `InputContext`.\
  An additional `cnt?` can be supplied to control termination.
  When the number of times `action` returns `.some _` reaches `cnt?`,
  the procedure is terminated.
-/
def runWithEffectOfCommands
  (input : String) (fileName : String) (opts : Options := {}) (cnt? : Option Nat)
  (action : Context → State → State → ConstantInfo → IO (Option α)) : CoreM (Array α) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let mut ensuring := #[]
  if auto.evalAuto.ensureAesop.get (← getOptions) then
    ensuring := ensuring.push { module := `Aesop }
  let (env, messages) ← processHeaderEnsuring header opts messages inputCtx (ensuring := ensuring)
  let commandState := Command.mkState env messages opts
  (runWithEffectOfCommandsCore cnt? action { inputCtx }).run'
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

open Tactic in
/--
  Use `runWithEffectOfCommands` to run tactics at the place just before
  the command that created the constant `name`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files
-/
def runTacticsAtConstantDeclaration
  (name : Name) (searchPath : SearchPath)
  (tactics : Array (ConstantInfo → TacticM Unit)) : CoreM (Array Result) := do
  if ← isInitializerExecutionEnabled then
    throwError "{decl_name%} :: Running this function with execution of `initialize` code enabled is unsafe"
  let .some modName ← Lean.findModuleOf? name
    | throwError "{decl_name%} :: Cannot find constant {name}"
  let .some uri ← Server.documentUriFromModule searchPath modName
    | throwError "{decl_name%} :: Cannot find module {modName}"
  let .some path := System.Uri.fileUriToPath? uri
    | throwError "{decl_name%} :: URI {uri} of {modName} is not a file"
  let path := path.normalize
  let inputHandle ← IO.FS.Handle.mk path .read
  let input ← inputHandle.readToEnd
  let results : Array (Array Result) ← runWithEffectOfCommands input path.toString {} (.some 1) (fun ctx st₁ st₂ ci => do
    if name != ci.name then
      return .none
    let metaAction (tactic : ConstantInfo → TacticM Unit) : MetaM Result :=
      Term.TermElabM.run' <| Result.ofTacticOnExpr ci.type (tactic ci)
    let coreAction tactic : CoreM Result := (metaAction tactic).run'
    let ioAction tactic : IO (Result × _) :=
      (coreAction tactic).toIO {fileName := path.toString, fileMap := FileMap.ofString input } { env := st₁.commandState.env }
    let resultsWithState ← tactics.mapM (fun tactic => ioAction tactic)
    return .some (resultsWithState.map Prod.fst))
  let #[result] := results
    | throwError "{decl_name%} :: Unexpected error"
  return result

open Tactic in
/--
  Effectively, `runTacticsAtConstantDeclaration` at each constant of the module `modName`\
  Note: Use `initSrcSearchPath` to get SearchPath of source files
-/
def runTacticsAtModule
  (modName : Name) (searchPath : SearchPath)
  (tactics : Array (ConstantInfo → TacticM Unit)) : CoreM (Array Result) := do
  let .some uri ← Server.documentUriFromModule searchPath modName
    | throwError "{decl_name%} :: Cannot find module {modName}"
  let .some path := System.Uri.fileUriToPath? uri
    | throwError "{decl_name%} :: URI {uri} of {modName} is not a file"
  let path := path.normalize
  let inputHandle ← IO.FS.Handle.mk path .read
  let input ← inputHandle.readToEnd
  let results : Array (Array Result) ← runWithEffectOfCommands input path.toString {} .none (fun ctx st₁ st₂ ci => do
    let metaAction (tactic : ConstantInfo → TacticM Unit) : MetaM Result :=
      Term.TermElabM.run' <| Result.ofTacticOnExpr ci.type (tactic ci)
    let coreAction tactic : CoreM Result := (metaAction tactic).run'
    let ioAction tactic : IO (Result × _) :=
      (coreAction tactic).toIO {fileName := path.toString, fileMap := FileMap.ofString input } { env := st₁.commandState.env }
    let resultsWithState ← tactics.mapM (fun tactic => ioAction tactic)
    return .some (resultsWithState.map Prod.fst))
  let #[result] := results
    | throwError "{decl_name%} :: Unexpected error"
  return result

end EvalAuto
