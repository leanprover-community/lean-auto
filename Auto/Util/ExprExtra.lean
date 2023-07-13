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
syntax (name := getExprAndApply) "#getExprAndApply[" term "|" ident "]" : command

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
    
end Auto.Util