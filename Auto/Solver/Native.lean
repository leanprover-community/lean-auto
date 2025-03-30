import Lean
import Auto.Lib.MetaExtra
import Auto.Lib.Rebind
import Auto.Translation.Assumptions
open Lean

register_option auto.native : Bool := {
  defValue := false
  descr := "Enable/Disable Native Solver"
}

/-
  The first argument is for regular lemmas, and the second argument
  is for inhabitation facts
-/
declare_rebindable Auto.Native.solverFunc : Array Auto.Lemma → Array Auto.Lemma → MetaM Expr

initialize
  registerTraceClass `auto.native.printFormulas
  registerTraceClass `auto.native.printProof

namespace Auto.Solver.Native

private def nativeFuncExpectedType := Array Lemma → MetaM Expr

private unsafe def queryNativeUnsafe (lemmas : Array Lemma) (inhLemmas : Array Lemma) : MetaM Expr := do
  let nativeFuncCst ← eval_rebind% Auto.Native.solverFunc
  for lem in lemmas do
    trace[auto.native.printFormulas] "{lem.type}"
  let proof ← nativeFuncCst lemmas inhLemmas
  trace[auto.native.printProof] "Native prover found proof {proof}"
  return proof

@[implemented_by queryNativeUnsafe]
opaque queryNative : Array Lemma → Array Lemma → MetaM Expr

/--
  Emulate a native prover. When given lemmas `h₁, ⋯, hₙ`, the
  prover returns `sorryAx (h₁ → ⋯ → hₙ → ⊥) Bool.false h₁ ⋯ hₙ`
  Inhabitation lemmas are ignored
-/
def emulateNative (lemmas : Array Lemma) (_ : Array Lemma) : MetaM Expr := do
  let _ ← lemmas.mapM (fun lem => do
    if lem.params.size != 0 then
      throwError "{decl_name%} :: Universe levels parameters are not supported")
  let descrs := lemmas.zipIdx.map (fun (lem, i) => (Name.mkSimple s!"lem{i}", lem.type, .default))
  let sty := Expr.mkForallFromBinderDescrs descrs (.const ``False [])
  let sorryExpr := Lean.mkApp2 (.const ``sorryAx [.zero]) sty (.const ``Bool.false [])
  return Lean.mkAppN sorryExpr (lemmas.map (fun lem => lem.proof))

end Auto.Solver.Native
