import Lean
import Auto.Util.MonadUtils
import Auto.Util.ExprExtra
import Auto.Translation.PReif

-- D2P: Dependent type (COC) to Propositional Logic

namespace Auto

-- Open `D`
open Lean
-- Open `P`
open PReif

-- Translates an expression of type `Prop`
partial def D2P (e : Expr) : TransM Expr PropForm := do
  let ety ← Meta.inferType e
  let failureMsg := m!"D2P :: Failed to translate subexpression {e}"
  if ! (← Meta.isDefEq ety (.sort .zero)) then
    throwError m!"D2P :: Can't translate non-prop term {e}"
  match e with
  | .const .. =>
    let some name := e.constName?
      | throwError failureMsg
    match name with
    | ``True => return .trueE
    | ``False => return .falseE
    | _ => h2Atom e
  | .app .. =>
    let f := e.getAppFn
    let some name := f.constName?
      | h2Atom e
    let args := e.getAppArgs
    if args.size == 1 then
      let args ← args.mapM D2P
      match name with
      | ``Not => return .not args[0]!
      | _ => h2Atom e
    else if args.size == 2 then
      let args ← args.mapM D2P
      match name with
      | ``And => return .and args[0]! args[1]!
      | ``Or => return .or args[0]! args[1]!
      | ``Iff => return .iff args[0]! args[1]!
      | _ => h2Atom e
    else if args.size == 3 then
      match name with
      | ``Eq =>
        if ← Meta.isDefEq args[0]! (.sort .zero) then
          let args ← args[1:].toArray.mapM D2P
          return .eq args[0]! args[1]!
        else
          h2Atom e
      | _ => h2Atom e
    else
      h2Atom e
  | _ => h2Atom e

def tst (e : Expr) : Elab.Term.TermElabM Unit := do
  let es ← (D2P e).run {}
  let f := es.fst
  IO.println (repr f)

-- #getExprAndApply[True ∨ (False ↔ False) ∨ (2 = 3) ∨ (2 = 3)|tst]
-- #getExprAndApply[True ∨ (False ↔ False) ∨ ((False = True) = True)|tst]

end Auto