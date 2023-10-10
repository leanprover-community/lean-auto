import Lean.Meta.Reduce
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply
import Auto.DUnif.UnifRules

open Lean Meta
namespace Auto.DUnif

/--
Close given goal using `Eq.refl`.
-/
def MVarId.refl (mvarId : MVarId) (nAttempt : Nat) (nUnif : Nat) (cont : Nat) (iterOn : Bool) : MetaM (Array MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `refl
    let targetType ← mvarId.getType'
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    let success ← hounif lhs rhs nAttempt nUnif cont iterOn
    unless success do
      throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)
    Meta.getMVarsNoDelayed (.mvar mvarId)

syntax (name := drefl) "drefl" " attempt " num "unifier " num "contains" num ("iteron")? : tactic

@[tactic drefl] def evalRefl : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| drefl attempt $nAttempt unifier $nunif contains $cont iteron) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← DUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat true
        return ids.data
  | `(tactic| drefl attempt $nAttempt unifier $nunif contains $cont) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← DUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat false
        return ids.data
  | _ => Elab.throwUnsupportedSyntax

end Auto.DUnif