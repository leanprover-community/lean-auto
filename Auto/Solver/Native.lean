module

public import Lean
public import Auto.Lib.MetaExtra
public import Auto.Lib.Rebind
public import Auto.Translation.Assumptions
public import Auto.EmbedLam.LamLaterSpec

public section

open Lean

register_option auto.native : Bool := {
  defValue := false
  descr := "Enable/Disable Native Solver"
}

namespace Auto

/-- The input of a native prover, which should prove `False` from it -/
structure NativeInterface (α : Type u) where
  /-- Regular facts -/
  valids     : Array α
  /-- Inhabitation facts -/
  nonempties : Array α
  /--
    Characterizations of the constants of later-declared types, e.g. `Real`. The ones
      of the core constants are proofs of structures, e.g. `RealInterpUnlifted.CoreSpec`
  -/
  laterSpecs : LaterSpecInterface α := {}

end Auto

declare_rebindable Auto.Native.solverFunc : Auto.NativeInterface Auto.Lemma → MetaM Expr

initialize
  registerTraceClass `auto.native.printFormulas
  registerTraceClass `auto.native.printProof

namespace Auto.Solver.Native

private def nativeFuncExpectedType := Array Lemma → MetaM Expr

private meta unsafe def queryNativeUnsafe (lemmas : NativeInterface Lemma) : MetaM Expr := do
  let nativeFuncCst ← eval_rebind% Auto.Native.solverFunc
  let ls := lemmas.laterSpecs
  -- `LaterSpecInterface.toArray`, which is not `meta`
  let specs := ls.realCore.toArray ++ ls.realExt.map Prod.snd ++ ls.complexCore.toArray ++ ls.complexExt.map Prod.snd
  for lem in lemmas.valids ++ specs do
    trace[auto.native.printFormulas] "{lem.type}"
  let proof ← nativeFuncCst lemmas
  trace[auto.native.printProof] "Native prover found proof {proof}"
  return proof

@[implemented_by queryNativeUnsafe]
meta opaque queryNative : NativeInterface Lemma → MetaM Expr

/--
  Emulate a native prover. When given lemmas `h₁, ⋯, hₙ`, the
  prover returns `sorryAx (h₁ → ⋯ → hₙ → ⊥) Bool.false h₁ ⋯ hₙ`.
  The lemmas are the regular facts and the characterizations of later-declared
  types. Inhabitation lemmas are ignored
-/
def emulateNative (lemmas : NativeInterface Lemma) : MetaM Expr := do
  let lemmas := lemmas.valids ++ lemmas.laterSpecs.toArray
  let _ ← lemmas.mapM (fun lem => do
    if lem.params.size != 0 then
      throwError "{decl_name%} :: Universe levels parameters are not supported")
  let descrs := lemmas.zipIdx.map (fun (lem, i) => (Name.mkSimple s!"lem{i}", lem.type, .default))
  let sty := Expr.mkForallFromBinderDescrs descrs (.const ``False [])
  let sorryExpr := Lean.mkApp2 (.const ``sorryAx [.zero]) sty (.const ``Bool.false [])
  return Lean.mkAppN sorryExpr (lemmas.map (fun lem => lem.proof))

end Auto.Solver.Native
