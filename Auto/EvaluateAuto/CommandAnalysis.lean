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
  (input : String) (fileName : String) (cnt? : Option Nat)
  (action : Context → State → State → ConstantInfo → IO (Option α)) : CoreM (Array α) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let mut ensuring := #[]
  if auto.evalAuto.ensureAesop.get (← getOptions) then
    ensuring := ensuring.push { module := `Aesop }
  let (env, messages) ← processHeaderEnsuring header {} messages inputCtx (ensuring := ensuring)
  let commandState := Command.mkState env messages {}
  (runWithEffectOfCommandsCore cnt? action { inputCtx }).run'
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

end EvalAuto
