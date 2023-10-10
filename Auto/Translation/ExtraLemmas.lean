import Lean
import Auto.Translation.Assumptions
open Lean

namespace Auto

theorem ite_eq_true (p : Prop) [inst : Decidable p] (a b : α) : p → ite p a b = a := by
  intro hp; dsimp [ite]; cases inst
  case isFalse hnp => apply False.elim (hnp hp)
  case isTrue _ => rfl

theorem ite_eq_false (p : Prop) [inst : Decidable p] (a b : α) : ¬ p → ite p a b = b := by
  intro hnp; dsimp [ite]; cases inst
  case isFalse _ => rfl
  case isTrue hp => apply False.elim (hnp hp)

def iteLemmas : CoreM (Array Lemma) := do
  let tl ← Lemma.ofConst ``ite_eq_true
  let fl ← Lemma.ofConst ``ite_eq_false
  return #[tl, fl]

/--
  Given an array of lemmas collected from the user input, return
    the array of lemmas that should be added in order to help
    auto solve the problem
-/
def auxLemmas (lemmas : Array Lemma) : CoreM (Array Lemma) := do
  let mut ret := #[]
  -- Add `iteLemmas`
  if lemmas.any (fun ⟨_, e, _⟩ => (e.find? (fun sub => sub.constName? = .some ``ite)).isSome) then
    ret := ret.append (← iteLemmas)
  return ret

end Auto