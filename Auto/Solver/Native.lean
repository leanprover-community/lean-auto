import Lean
import Auto.Lib.MetaExtra
import Auto.Lib.Rebind
import Auto.Translation.Assumptions
open Lean

register_option auto.native : Bool := {
  defValue := false
  descr := "Enable/Disable Native Solver"
}

declare_rebindable Auto.Native.solverFunc : Array Auto.Lemma → MetaM Expr

initialize
  registerTraceClass `auto.native.printFormulas
  registerTraceClass `auto.native.printProof

namespace Auto.Solver.Native

private def nativeFuncExpectedType := Array Lemma → MetaM Expr

private unsafe def queryNativeUnsafe (lemmas : Array Lemma) : MetaM Expr := do
  let nativeFuncCst ← eval_rebind% Auto.Native.solverFunc
  for lem in lemmas do
    trace[auto.native.printFormulas] "{lem.type}"
  let proof ← nativeFuncCst lemmas
  trace[auto.native.printProof] "Native prover found proof {proof}"
  return proof

@[implemented_by queryNativeUnsafe]
opaque queryNative : Array Lemma → MetaM Expr

/--
  Emulate a native prover. When given lemmas `h₁, ⋯, hₙ`, the
  prover returns `sorryAx (h₁ → ⋯ → hₙ → ⊥) Bool.false h₁ ⋯ hₙ`
-/
def emulateNative (lemmas : Array Lemma) : MetaM Expr := do
  let _ ← lemmas.mapM (fun lem => do
    if lem.params.size != 0 then
      throwError "Solver.emulateNative :: Universe levels parameters are not supported")
  let descrs := lemmas.zipWithIndex.map (fun (lem, i) => (s!"lem{i}".toName, lem.type, .default))
  let sty := Expr.mkForallFromBinderDescrs descrs (.const ``False [])
  let sorryExpr := Lean.mkApp2 (.const ``sorryAx [.zero]) sty (.const ``Bool.false [])
  return Lean.mkAppN sorryExpr (lemmas.map (fun lem => lem.proof))

end Auto.Solver.Native
