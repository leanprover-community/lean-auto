import Lean
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.Tactic

open Lean Auto

initialize
  registerTraceClass `auto.eval.printConfig
  registerTraceClass `auto.eval.printProblem
  registerTraceClass `auto.eval.printResult

namespace EvalAuto

inductive Result
  | success
  | nonProp
  | typeCheckFail
  | typeUnequal
  | autoException (e : Exception)

instance : ToMessageData Result where
  toMessageData : Result → MessageData
  | .success         => "Result.success"
  | .nonProp         => "Result.nonProp"
  | .typeCheckFail   => "Result.typeCheckFail"
  | .typeUnequal     => "Result.typeUnequal"
  | .autoException e => m!"Result.autoException ::\n{e.toMessageData}"

structure EvalConfig where
  maxHeartbeats : Nat           := 65536
  logFile       : Option String := .none

instance : ToString EvalConfig where
  toString : EvalConfig → String
  | ⟨maxHeartbeats, logFile⟩ =>
    let logFileStr :=
      match logFile with
      | .some logFile => s!", logFile := {logFile}"
      | .none => ""
    s!"\{maxHeartbeats := {maxHeartbeats}{logFileStr}}"

/--
  Run `Lean-auto` on `lem.type`, using premises collected from `lem.proof`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
private def runAutoOnAutoLemmaMeta (declName? : Option Name) (lem : Auto.Lemma) : MetaM Result := do
  if !(← Meta.isProp lem.type) then
    return .nonProp
  -- **TODO: Aux theorem like those ending in `.proof_1`**
  let usedThmNames ← (← Expr.getUsedTheorems lem.proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThms ← usedThmNames.mapM (fun n => Lemma.ofConst n (.leaf "collected by hammertest"))
  let autoProofFn : MetaM Expr := Meta.forallTelescope lem.type fun bs body => do
    let negGoal := Expr.app (.const ``Not []) body
    let negGoalImpFalse ← Meta.withLocalDeclD `negGoal negGoal fun negGoalFVar => do
      let inhLemmas ← Auto.Inhabitation.getInhFactsFromLCtx
      let lctxLemmas ← Auto.collectLctxLemmas true #[]
      let allLemmas ← (lctxLemmas ++ usedThms).mapM (Auto.unfoldConstAndPreprocessLemma #[])
      let proofOfFalse ← Auto.runAuto declName? allLemmas inhLemmas
      Meta.mkLambdaFVars #[negGoalFVar] proofOfFalse
    let goal := mkApp2 (.const ``Classical.byContradiction []) body negGoalImpFalse
    Meta.mkLambdaFVars bs goal
  let mut autoProof : Expr := Expr.sort .zero
  try
    autoProof ← autoProofFn
  catch e =>
    return .autoException e
  match Kernel.check (← getEnv) {} autoProof with
  | Except.ok autoProofType =>
    match Kernel.isDefEq (← getEnv) {} autoProofType lem.type with
    | Except.ok true => return .success
    | _ => return .typeUnequal
  | Except.error _ => return .typeCheckFail

def runAutoOnAutoLemma (declName? : Option Name) (lem : Auto.Lemma) : CoreM Result := do
  (runAutoOnAutoLemmaMeta declName? lem).run'

/--
  Run `Lean-auto` on the type of ``name``, using premises collected
    from the proof of `name`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
def runAutoOnConst (name : Name) : CoreM Result := do
  let ci ← Name.getCi name decl_name%
  let .some v := ci.value?
    | throwError "{decl_name%} :: {name} has no value"
  let lemmaPre ← Auto.Lemma.ofConst name (.leaf "ofConst")
  let lemmaV := {lemmaPre with proof := v}
  runAutoOnAutoLemma (.some name) lemmaV

def runAutoOnConsts (config : EvalConfig) (names : Array Name) : CoreM Unit := do
  let logFileHandle : Option IO.FS.Handle ← config.logFile.mapM (fun fname => IO.FS.Handle.mk fname .write)
  trace[auto.eval.printConfig] m!"Config = {config}"
  if let .some fhandle := logFileHandle then
    fhandle.putStrLn s!"Config = {config}"
  for name in names do
    let ci ← Name.getCi name decl_name%
    trace[auto.eval.printProblem] m!"Testing || {name} : {ci.type}"
    if let .some fhandle := logFileHandle then
      fhandle.putStrLn ""
      fhandle.putStrLn s!"Testing || {name} : {← (Lean.Meta.ppExpr ci.type).run'}"
    let result ←
      withReader (fun ctx => {ctx with maxHeartbeats := config.maxHeartbeats * 1000}) <|
        withCurrHeartbeats <| do
          runAutoOnConst name
    trace[auto.eval.printResult] m!"{result}"
    if let .some fhandle := logFileHandle then
      fhandle.putStrLn (toString (← MessageData.format m!"{result}"))

end EvalAuto
