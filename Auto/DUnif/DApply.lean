import Lean
import Auto.DUnif.UnifRules
import Auto.Lib.ExprExtra
open Lean

namespace Auto.DUnif

-- Note: This is copied from standard library with some code
--       removed to make it simpler and a few lines changed to
--       allow for higher-order unification

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
  Meta.throwTacticEx `apply mvarId m!"failed to unify{indentExpr eType}\nwith{indentExpr targetType}"

/--
Close the given goal using `apply e`.
-/
def execdapply (mvarId : MVarId) (e : Expr) (nAttempt : Nat) (nUnif : Nat) (cont : Nat) (cfg : Meta.ApplyConfig := {}) : MetaM (List MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `apply
    let targetType ← mvarId.getType
    let targetMVars ← Meta.getMVarsNoDelayed targetType
    let eType      ← Meta.inferType e
    let (numArgs, hasMVarHead) ← Meta.getExpectedNumArgsAux eType
    /-
    The `apply` tactic adds `_`s to `e`, and some of these `_`s become new goals.
    When `hasMVarHead` is `false` we try different numbers, until we find a type compatible with `targetType`.
    We used to try only `numArgs-targetTypeNumArgs` when `hasMVarHead = false`, but this is not always correct.
    For example, consider the following example
    ```
    example {α β} [LE_trans β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
      apply le_trans
      assumption
      assumption
    ```
    In this example, `targetTypeNumArgs = 1` because `LE` for functions is defined as
    ```
    instance {α : Type u} {β : Type v} [LE β] : LE (α → β) where
      le f g := ∀ i, f i ≤ g i
    ```
    -/
    let rangeNumArgs ← if hasMVarHead then
      pure [numArgs : numArgs+1]
    else
      let targetTypeNumArgs ← Meta.getExpectedNumArgs targetType
      pure [numArgs - targetTypeNumArgs : numArgs+1]
    /-
    Auxiliary function for trying to add `n` underscores where `n ∈ [i: rangeNumArgs.stop)`
    See comment above
    -/
    let rec go (i : Nat) : MetaM (Array Expr × Array BinderInfo) := do
      if i < rangeNumArgs.stop then
        let s ← saveState
        let (newMVars, binderInfos, eType) ← Meta.forallMetaTelescopeReducing eType i
        if (← hounif eType targetType nAttempt nUnif cont true) then
          return (newMVars, binderInfos)
        else
          s.restore
          go (i+1)
      else
        let (_, _, eType) ← Meta.forallMetaTelescopeReducing eType (some rangeNumArgs.start)
        throwApplyError mvarId eType targetType
    let (newMVars, binderInfos) ← go rangeNumArgs.start
    Meta.postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    -- Collect other mvars
    let mut otherMVarIds ← Meta.getMVarsNoDelayed e
    for m in targetMVars do
      for mvarId in (← Meta.getMVarsNoDelayed (.mvar m)) do
        if !otherMVarIds.contains mvarId then
          otherMVarIds := otherMVarIds.push mvarId
    let newMVarIds := (newMVars.map (·.mvarId!)).data
    otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    trace[Meta.Tactic] "{result}"
    result.forM (·.headBetaType)
    return result
termination_by go i => rangeNumArgs.stop - i

syntax (name := dapply) "dapply " term " attempt " num "unifier " num "contains" num : tactic

@[tactic dapply]
def evaldapply : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| dapply $e attempt $nAttempt unifier $nunif contains $cont) => Elab.Tactic.withMainContext do
    let mut val ← instantiateMVars (← Elab.Tactic.elabTermForApply e)
    if val.consumeMData.isMVar then
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← execdapply (← Elab.Tactic.getMainGoal) val nAttempt.getNat nunif.getNat cont.getNat
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    Elab.Tactic.replaceMainGoal mvarIds'
  | _ => Elab.throwUnsupportedSyntax

end Auto.DUnif