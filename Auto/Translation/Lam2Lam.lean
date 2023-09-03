import Lean
import Auto.Translation.LamReif

namespace Auto.Lam2Lam
open Embedding.Lam LamReif

-- We're translating `Lam` to `Lam`. We call the first `Lam`
--   the `high-level` one, and the second `Lam` the `low-level` one.

def transLamSort (ref : State) : LamSort → TransM Nat Nat LamSort
| .atom n => do
  let (val, _) ← (lookupTyVal! n).run ref
  return .atom (← transTypeAtom n val)
| .base b => return .base b
| .func arg res => .func <$> transLamSort ref arg <*> transLamSort ref res

def transLamBaseTerm (ref : State) : LamBaseTerm → TransM Nat Nat LamBaseTerm
| .eqI n => do
  let (sort, _) ← (lookupLamILTy! n).run ref
  return .eqI (← sort2LamILTyIdx sort)
| .forallEI n => do
  let (sort, _) ← (lookupLamILTy! n).run ref
  return .forallEI (← sort2LamILTyIdx sort)
| .existEI n => do
  let (sort, _) ← (lookupLamILTy! n).run ref
  return .existEI (← sort2LamILTyIdx sort)
| b => return b

def transLamTerm (ref : State) : LamTerm → TransM Nat Nat LamTerm
| .atom n => do
  let ((e, s), _) ← (lookupVarVal! n).run ref
  let s' ← transLamSort ref s
  return .atom (← transTermAtom n (e, s'))
| .base b => .base <$> transLamBaseTerm ref b
| .bvar n => return .bvar n
| .lam s t => .lam <$> transLamSort ref s <*> transLamTerm ref t
| .app s fn arg => .app <$> transLamSort ref s <*> transLamTerm ref fn <*> transLamTerm ref arg

-- Collect essential chksteps and assertions from the high-level `lam`
--   into the low-level `lam` such that the low-level `lam` proves `re`
partial def collectProofFor (ref : State) (re : REntry) : TransM Nat Nat Unit := do
  if let .some _ := (← getChkMap).find? re then
    return
  let (highLvlProof, _) ← (lookupREntryProof! re).run ref
  match highLvlProof with
  | .inl cs =>
    let posCont (n : Nat) : TransM Nat Nat Nat := (do
      let (re, _) ← (lookupRTable! n).run ref
      collectProofFor ref re
      lookupREntryPos! re)
    let cs' : ChkStep ← (do
      match cs with
      | .nop => return .nop
      | .wfOfCheck lctx t => return .wfOfCheck lctx (← transLamTerm ref t)
      | .wfOfAppend ex pos => return .wfOfAppend ex (← posCont pos)
      | .wfOfPrepend ex pos => return .wfOfPrepend ex (← posCont pos)
      | .wfOfTopBeta pos => return .wfOfTopBeta (← posCont pos)
      | .validOfTopBeta pos => return .validOfTopBeta (← posCont pos)
      | .validOfImp p₁₂ p₁ => return .validOfImp (← posCont p₁₂) (← posCont p₁)
      )
    newChkStep cs' re
  | .inr (e, t) => newAssertion e (← transLamTerm ref t)

end Auto.Lam2Lam