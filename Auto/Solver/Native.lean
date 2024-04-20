import Lean
import Auto.Lib.MetaExtra
import Auto.Translation.Assumptions
open Lean

register_option auto.native : Bool := {
  defValue := false
  descr := "Enable/Disable Native Solver"
}

register_option auto.native.solver.func : String := {
  defValue := ""
  descr := "Lean name of solver function. The function must have type `Array Lemma → MetaM Expr`"
}

initialize
  registerTraceClass `auto.native.printFormulas
  registerTraceClass `auto.native.printProof

namespace Auto.Solver.Native

private def nativeFuncExpectedType := Array Lemma → MetaM Expr

private unsafe def queryNativeUnsafe (lemmas : Array Lemma) : MetaM Expr := do
  let nativeFuncStr := auto.native.solver.func.get (← getOptions)
  let nativeFunc := (nativeFuncStr.splitOn ".").foldl (fun acc s => Name.str acc s) .anonymous
  let .some (.defnInfo di) := (← getEnv).find? nativeFunc
    | throwError "queryNative :: {nativeFunc} is not a defined constant"
  if !(← Meta.isDefEqD (.const ``nativeFuncExpectedType []) di.type) then
    throwError ("queryNative :: Unexpected type of native solver function." ++
      " Expected `List (Expr × Expr × Array Name) → MetaM Expr`")
  let nativeFuncCst ← evalConst nativeFuncExpectedType nativeFunc
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
  let descrs := lemmas.zipWithIndex.map (fun (lem, i) => (s!"lem{i}", lem.type, .default))
  let sty := Expr.mkForallFromBinderDescrs descrs (.const ``False [])
  let sorryExpr := Lean.mkApp2 (.const ``sorryAx [.zero]) sty (.const ``Bool.false [])
  return Lean.mkAppN sorryExpr (lemmas.map (fun lem => lem.proof))

end Auto.Solver.Native
