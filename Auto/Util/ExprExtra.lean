import Lean
open Lean Elab Command

namespace Auto.Util

def Expr.binders (e : Expr) : Array (Name × Expr × BinderInfo) :=
  let rec aux (e : Expr) :=
    match e with
    | .forallE n ty b bi => (n, ty, bi) :: aux b
    | _ => []
  Array.mk (aux e)

-- `ident` must be of type `Expr → TermElabM Unit`
-- Compiles `term` into `Expr`, then applies `ident` to it
syntax (name := getExprAndApply) "#getExprAndApply" "[" term "|" ident "]" : command

@[command_elab Auto.Util.getExprAndApply]
unsafe def elabGetExprAndApply : CommandElab := fun stx =>
  runTermElabM fun _ => do
    match stx with
    | `(command | #getExprAndApply[ $t:term | $i:ident ]) => do
      let some iexpr ← Term.resolveId? i
        | throwError "elabGetExprAndApply :: Unknown identifier {i}"
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      let fname := iexpr.constName!
      let Except.ok f := (← getEnv).evalConst (Expr → TermElabM Unit) (← getOptions) fname
        | throwError "elabGetExprAndApply :: Failed to evaluate {fname} to a term of type (Expr → TermElabM Unit)"
      f e
    | _ => throwUnsupportedSyntax

syntax (name := lazyReduce) "#lazyReduce" term : command

register_option lazyReduce.skipProof : Bool := {
  defValue := true
  descr    := "Whether to reduce proof when calling #lazyReduce"
}

register_option lazyReduce.skipType : Bool := {
  defValue := true
  descr    := "Whether to reduce type when calling #lazyReduce"
}

register_option lazyReduce.logInfo : Bool := {
  defValue := true
  descr    := "Whether to print result of #reduce"
}

register_option lazyReduce.printTime : Bool := {
  defValue := false
  descr    := "Whether to print result of #reduce"
}

open Meta in
@[command_elab Auto.Util.lazyReduce] def elabLazyReduce : CommandElab
  | `(#lazyReduce%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let startTime ← IO.monoMsNow
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let opts ← getOptions
    let skipProof? := lazyReduce.skipProof.get opts
    let skipType? := lazyReduce.skipType.get opts
    let logInfo? := lazyReduce.logInfo.get opts
    let printTime? := lazyReduce.printTime.get opts
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <| reduce e (skipProofs := skipProof?) (skipTypes := skipType?)
      if logInfo? then
        logInfoAt tk e
      if printTime? then
        IO.println s!"{(← IO.monoMsNow) - startTime} ms"
  | _ => throwUnsupportedSyntax
    
end Auto.Util