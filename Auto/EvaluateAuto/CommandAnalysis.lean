import Lean
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.Result
open Lean

namespace EvalAuto

open Elab Frontend
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
  (action : Context → State → State → ConstantInfo → IO (Option α)) : IO (Array α) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let commandState := Command.mkState env messages opts
  (runWithEffectOfCommandsCore cnt? action { inputCtx }).run'
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

open Elab Tactic in
/--
  Note: Use `initSrcSearchPath` to get SearchPath of Lean4's builtin source files
-/
def runTacticAtConstantDeclaration
  (name : Name) (searchPath : SearchPath)
  (tactic : ConstantInfo → TacticM Unit) : CoreM Result := do
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
  let results ← runWithEffectOfCommands input path.toString {} (.some 1) (fun ctx st₁ st₂ ci =>
    let metaAction : MetaM (Option Result) := do
      if ci.name != name then
        return .none
      let .mvar mid ← Meta.mkFreshExprMVar ci.type
        | throwError "{decl_name%} :: Unexpected error"
      let result : List MVarId ⊕ Exception ←
        tryCatchRuntimeEx
          (do let goals ← Term.TermElabM.run' (Tactic.run mid (tactic ci)) {}; return .inl goals)
          (fun e => return .inr e)
      match result with
      | .inl goals =>
        if goals.length >= 1 then
          return .some .subGoals
        let proof ← instantiateMVars (.mvar mid)
        match Kernel.check (← getEnv) {} proof with
        | Except.ok autoProofType =>
          match Kernel.isDefEq (← getEnv) {} autoProofType ci.type with
          | Except.ok true => return .some .success
          | _ => return .some .typeUnequal
        | Except.error _ => return .some .typeCheckFail
      | .inr e => return .some (.exception e)
    let coreAction : CoreM (Option Result) := metaAction.run'
    let ioAction : IO (Option Result × _) := coreAction.toIO {fileName := path.toString, fileMap := FileMap.ofString input } { env := st₁.commandState.env }
    do
      return (← ioAction).fst)
  let #[result] := results
    | throwError "{decl_name%} :: Unexpected error"
  return result

end EvalAuto
