import Lean
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.Tactic

open Lean

namespace Auto

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
  | .autoException e => m!"Result.autoException :: {e.toMessageData}"

/--
  Run `Lean-auto` on `lem.type`, using premises collected from `lem.proof`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
def runAutoOnAutoLemma (declName? : Option Name) (lem : Auto.Lemma) : MetaM Result := do
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
      let proofOfFalse ← Auto.runAuto declName? (lctxLemmas ++ usedThms) inhLemmas
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

/--
  Run `Lean-auto` on the type of ``name``, using premises collected
    from the proof of `name`
  Premises which only contain logic constants are filtered because they
    are assumed to be known by the prover
-/
def runAutoOnConst (name : Name) : MetaM Result := do
  let ci ← Name.getCi name decl_name%
  let .some v := ci.value?
    | throwError "{decl_name%} :: {name} has no value"
  let lemmaPre ← Auto.Lemma.ofConst name (.leaf "ofConst")
  let lemmaV := {lemmaPre with proof := v}
  runAutoOnAutoLemma (.some name) lemmaV

end Auto
