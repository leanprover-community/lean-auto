import Auto.Tactic
import Auto.EvaluateAuto.ConstAnalysis
open Lean Auto EvalAuto

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
