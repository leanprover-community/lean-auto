import Auto.Tactic
import Auto.EvaluateAuto.OS
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.NameArr

open Lean Auto

namespace EvalAuto

/--
  Compute the size of the problem associated with `lem`\
  The goal of the problem is `lem.type`, and the premises of the problem
  are theorems that are used in `lem.proof`
-/
def rawProblemSizeOfAutoLemma (lem : Auto.Lemma) : CoreM Nat := do
  let usedThmNames ← (← Expr.getUsedTheorems lem.proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThmTypes ← usedThmNames.mapM (fun name => do
    let .some decl := (← getEnv).find? name
      | throwError "{decl_name%} :: Unknown constant {name}"
    return decl.type)
  return Expr.sizeWithoutSharing lem.type + Array.foldl Nat.add 0 (usedThmTypes.map Expr.sizeWithoutSharing)

/--
  Compute the size of the problem associated with the constant `name`\
  The goal of the problem is the type of `name`, and the premises of the problem
  are theorems that are used in the proof of `name`
-/
def rawProblemSizeOfConst (name : Name) : CoreM Nat := do
  let ci ← Name.getCi name decl_name%
  let .some v := ci.value?
    | throwError "{decl_name%} :: {name} has no value"
  let lemmaPre ← Auto.Lemma.ofConst name (.leaf "ofConst")
  let lemmaV := {lemmaPre with proof := v}
  rawProblemSizeOfAutoLemma lemmaV

/--
  Compute the monomorphized problem associated with `lem`\
  The goal of the problem is `lem.type`, and the premises of the problem
  are theorems that are used in `lem.proof`
-/
def monomorphizedProblemOfAutoLemma (lem : Auto.Lemma) : CoreM (Option (Array Embedding.Lam.LamTerm)) := do
  let usedThmNames ← (← Expr.getUsedTheorems lem.proof).filterM (fun name =>
    return !(← Name.onlyLogicInType name))
  let usedThms ← usedThmNames.mapM (fun n => Lemma.ofConst n (.leaf "collected by hammertest"))
  let monoFn : MetaM (Array Embedding.Lam.LamTerm) := Meta.forallTelescope lem.type fun bs body => do
    let negGoal := Expr.app (.const ``Not []) body
    Meta.withLocalDeclD `negGoal negGoal fun _ => do
      let inhLemmas ← Inhabitation.getInhFactsFromLCtx
      let lctxLemmas ← Auto.collectLctxLemmas true #[]
      let lemmas ← (lctxLemmas ++ usedThms).mapM (Auto.unfoldConstAndPreprocessLemma #[])
      let lemmas ← rewriteIteCondDecide lemmas
      let (monomorphized, _) ← Monomorphization.monomorphize lemmas inhLemmas (@id (Reif.ReifM _) do
        let s ← get
        let u ← computeMaxLevel s.facts
        (LamReif.reifFacts s.facts).run' {u := u})
      return monomorphized
  let metaContext : Meta.Context := { config := Elab.Term.setElabConfig {} }
  Lean.Core.tryCatchRuntimeEx
    (do let monomorphized ← Meta.MetaM.run' monoFn (ctx := metaContext); return .some monomorphized)
    (fun _ => return .none)

/--
  Compute the monomorphized problem associated with the constant `name`\
  The goal of the problem is the type of `name`, and the premises of the problem
  are theorems that are used in the proof of `name`
-/
def monomorphizedProblemOfConst (name : Name) : CoreM (Option (Array Embedding.Lam.LamTerm)) := do
  let ci ← Name.getCi name decl_name%
  let .some v := ci.value?
    | throwError "{decl_name%} :: {name} has no value"
  let lemmaPre ← Auto.Lemma.ofConst name (.leaf "ofConst")
  let lemmaV := {lemmaPre with proof := v}
  monomorphizedProblemOfAutoLemma lemmaV

def monomorphizedProblemSizeOfConst (name : Name) : CoreM (Option Nat) := do
  match ← monomorphizedProblemOfConst name with
  | .some ls => return .some <| (ls.map Embedding.Lam.LamTerm.size).foldl Nat.add 0
  | .none => return .none

/--
  Run `Meta.reduceAll` on the type of `name` and the type of all
  theorems used in the proof of `name. Return the sum of sizes of the
  reduced theorem
-/
def testReduce (name : Name) : MetaM Nat := do
  let usedThms ← Name.getUsedTheorems name
  let allNames := usedThms ++ #[name]
  let allExprs ← allNames.mapM (fun name => do
    let .some ci := (← getEnv).find? name
      | throwError "{decl_name%} :: Cannot find {name}"
    return ci.type)
  let red (e : Expr) : MetaM TransformStep := do
    let e ← Meta.whnf e
    return .continue e
  let exprs ← allExprs.mapM (fun e => Meta.transform e (pre := red) (usedLetOnly := false))
  return Array.foldl Nat.add 0 (exprs.map Expr.sizeWithoutSharing)

def testReduceDWriteResult (path : String) (name : Name) : MetaM Unit := do
  let size ← Meta.withDefault <| testReduce name
  let handle ← IO.FS.Handle.mk path .write
  handle.putStrLn s!"{size} {Name.uniqRepr name}"

/--
  Run `testReduceDWriteResult` on each name in `names`. A new Lean 4 process
  is created for each `name` (this is because we want to pose time and memory
  limit on each of them)
-/
def evalReduceSize
  (names : Array Name) (resultFolder : String) (nprocs : Nat)
  (memoryLimitKb : Nat) (timeLimitS : Nat) : CoreM Unit := do
  if !(← System.FilePath.isDir resultFolder) then
    IO.FS.createDir resultFolder
  NameArray.save names (resultFolder ++ "/names.txt")
  let evaluateNamesHandle ← IO.FS.Handle.mk (resultFolder ++ "/evaluateNames.txt") .write
  let mut running := #[]
  for (name, idx) in names.zipWithIndex do
    let evalProc ← runFunctionOnConstsUsingNewLeanProcess
      #[name] ``testReduceDWriteResult
      #[s!"\"{resultFolder}/{idx}.result\""] memoryLimitKb timeLimitS
    running := running.push (idx, evalProc)
    while running.size >= nprocs do
      running ← tryWaitOn evaluateNamesHandle running
  while running.size != 0 do
    running ← tryWaitOn evaluateNamesHandle running
where
  tryWaitOn (evaluateNamesHandle : IO.FS.Handle) (running : Array (Nat × EvalTakenProc)) : CoreM (Array (Nat × _)) := do
    let mut running' := #[]
    for (idx, proc) in running do
      let retCode? ← proc.tryWait
      match retCode? with
      | .some retCode =>
        evaluateNamesHandle.putStrLn s!"{idx} : {retCode}"
        evaluateNamesHandle.flush
      | .none => running' := running'.push (idx, proc)
    return running'

end EvalAuto
