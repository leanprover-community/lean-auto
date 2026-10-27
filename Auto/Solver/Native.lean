module

public import Lean
public import Auto.Lib.MetaExtra
public import Auto.Lib.Rebind
public import Auto.Translation.Assumptions
public import Auto.EmbedLam.LamLaterSpec
public import Auto.EmbedLam.LamInductive

public section

open Lean

register_option auto.native : Bool := {
  defValue := false
  descr := "Enable/Disable Native Solver"
}

namespace Auto

/--
  The input of a native prover at various stages during translation.
  Here `α` and `β` represent the regular facts and the inhabitation facts
  (e.g. `LamTerm`s and `LamSort`s) at various stages during translation.
-/
structure NativeInterface (α : Type u) (β : Type u := α) where
  /-- Regular facts -/
  valids     : Array α
  /-- Inhabitation facts -/
  nonempties : Array β
  /--
    Characterizations of the constants of later-declared types, e.g. `Real`. The ones
      of the core constants are proofs of structures, e.g. `RealInterpUnlifted.CoreSpec`
  -/
  laterSpecs : LaterSpecInterface α := {}
  /-- Characterizations of the mutual blocks of inductive types, each split into its conjuncts -/
  indSpecs   : Array (IndBlockSpec α) := #[]

end Auto

declare_rebindable Auto.Native.solverFunc : Auto.NativeInterface Auto.Lemma → MetaM Expr

initialize
  registerTraceClass `auto.native.printFormulas
  registerTraceClass `auto.native.printProof

namespace Auto.Solver.Native

private meta unsafe def queryNativeUnsafe (lemmas : NativeInterface Lemma) : MetaM Expr := do
  let nativeFuncCst ← eval_rebind% Auto.Native.solverFunc
  let ls := lemmas.laterSpecs
  -- `LaterSpecInterface.toArray` and `IndBlockSpec.toArray`, which are not `meta`
  let specs := ls.realCore.toArray ++ ls.realExt.map Prod.snd ++ ls.complexCore.toArray ++ ls.complexExt.map Prod.snd
  let indSpecs := lemmas.indSpecs.flatMap fun bs =>
    (bs.types.flatMap fun ts => ts.distinct ++ ts.inject ++ ts.proj).push bs.induction
  for lem in lemmas.valids ++ specs ++ indSpecs do
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
  types and of inductive types. Inhabitation lemmas are ignored
-/
def emulateNative (lemmas : NativeInterface Lemma) : MetaM Expr := do
  let lemmas := lemmas.valids ++ lemmas.laterSpecs.toArray ++ lemmas.indSpecs.flatMap IndBlockSpec.toArray
  let _ ← lemmas.mapM (fun lem => do
    if lem.params.size != 0 then
      throwError "{decl_name%} :: Universe levels parameters are not supported")
  let descrs := lemmas.zipIdx.map (fun (lem, i) => (Name.mkSimple s!"lem{i}", lem.type, .default))
  let sty := Expr.mkForallFromBinderDescrs descrs (.const ``False [])
  let sorryExpr := Lean.mkApp2 (.const ``sorryAx [.zero]) sty (.const ``Bool.false [])
  return Lean.mkAppN sorryExpr (lemmas.map (fun lem => lem.proof))

end Auto.Solver.Native
