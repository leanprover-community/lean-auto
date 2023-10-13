import Lean
import Auto.DUnif.Utils
import Auto.DUnif.UnifProblem
import Auto.Lib.OccursCheck

open Lean

namespace Auto.DUnif

initialize
  registerTraceClass `auto.dunif.oracles

register_option auto.dunif.oracleInstOn : Bool := {
  defValue := true
  descr := "Enable/Disable instantiation oracle, which attempts to " ++
           "instantiate a side of the equation if it's a metavariable"
}

def getOracleInstOn : CoreM Bool := do
  let opts ← getOptions
  return auto.dunif.oracleInstOn.get opts

def oracleInst (p : UnifProblem) (eq : UnifEq) : MetaM (Option UnifProblem) := do
  setMCtx p.mctx
  let mut mvarId : MVarId := Inhabited.default
  if ¬ (← getOracleInstOn) then
    return none
  let mut eq := eq
  if let .some id ← metaEta eq.rhs then
    eq := eq.swapSide
    mvarId := id
  else
    if let .some id ← metaEta eq.lhs.eta then
      mvarId := id
    else
      return none
  -- We do not use Lean's occurs check here, because the occurs check
  --   does not consider metavariables in the type of metavariables
  if (← mustNotOccursCheck mvarId eq.rhs) then
    mvarId.assign eq.rhs
    return some {(← p.pushParentRuleIfDbgOn (.OracleInst eq)) with checked := false, mctx := ← getMCtx}
  else
    return none

register_option oracleOccursOn : Bool := {
  defValue := true
  descr := "Enable/Disable occurs check oracle, which is the generalization" ++
           " of first-order occurs check to dependent type theory. It only checks metavariables" ++
           " which will always be in the term even after β-reduction and further metavariable instantiations."
}

def getOracleOccursOn : CoreM Bool := do
  let opts ← getOptions
  return oracleOccursOn.get opts

-- true  : fail
-- false : not fail
def oracleOccurs (p : UnifProblem) (eq : UnifEq) : MetaM Bool := do
  setMCtx p.mctx
  if ¬ (← getOracleOccursOn) then
    return false
  if let .mvar id := eq.rhs.eta then
    mustOccursCheck id eq.lhs
  else
    if let .mvar id := eq.lhs.eta then
      mustOccursCheck id eq.rhs
    else
      return false

end Auto.DUnif