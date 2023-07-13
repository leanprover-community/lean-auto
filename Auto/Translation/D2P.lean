import Lean
import Auto.Util.MonadUtils
import Auto.Util.ExprExtra
open Lean

-- D2P: Dependent type to Propositional Logic

namespace Auto

namespace D2P

structure State where
  -- Map from identifier to its corresponding expression in Lean
  exprMap : HashMap Expr Nat := HashMap.empty
  -- Map from expression in Lean to its corresponding identifier
  idxMap : HashMap Nat Expr  := HashMap.empty

abbrev TransM := StateRefT State MetaM

@[always_inline]
instance : Monad TransM :=
  let i := inferInstanceAs (Monad TransM);
  { pure := i.pure, bind := i.bind }

instance : Inhabited (TransM α) where
  default := fun _ => throw default

#genMonadGetSet D2P.TransM D2P.State

inductive PropForm where
  | Atom  : Nat → PropForm
  | True  : PropForm
  | False : PropForm
  | Not   : PropForm → PropForm
  | And   : PropForm → PropForm → PropForm
  | Or    : PropForm → PropForm → PropForm
  | Iff   : PropForm → PropForm → PropForm
  | Eq    : PropForm → PropForm → PropForm
deriving Inhabited, Repr

def addAtom (e : Expr) : TransM PropForm := do
  let ⟨exprMap, idxMap⟩ ← get
  if exprMap.contains e then
    return .Atom (exprMap.find! e)
  let sz := exprMap.size
  setExprMap (exprMap.insert e sz)
  setIdxMap (idxMap.insert sz e)
  return .Atom sz

-- Translates an expression of type `Prop`
partial def translate (e : Expr) : TransM PropForm := do
  let ety ← Meta.inferType e
  let failureMsg := m!"D2P.translate :: Failed to translate subexpression {e}"
  if ! (← Meta.isDefEq ety (.sort .zero)) then
    throwError m!"D2P.translate :: Can't translate non-prop term {e}"
  match e with
  | .const .. =>
    let some name := e.constName?
      | throwError failureMsg
    match name with
    | ``True => return .True
    | ``False => return .False
    | _ => addAtom e
  | .app .. =>
    let f := e.getAppFn
    let some name := f.constName?
      | addAtom e
    let args := e.getAppArgs
    if args.size == 1 then
      let args ← args.mapM translate
      match name with
      | ``Not => return .Not args[0]!
      | _ => addAtom e
    else if args.size == 2 then
      let args ← args.mapM translate
      match name with
      | ``And => return .And args[0]! args[1]!
      | ``Or => return .Or args[0]! args[1]!
      | ``Iff => return .Iff args[0]! args[1]!
      | _ => addAtom e
    else if args.size == 3 then
      match name with
      | ``Eq =>
        if ← Meta.isDefEq args[0]! (.sort .zero) then
          let args ← args[1:].toArray.mapM translate
          return .Eq args[0]! args[1]!
        else
          addAtom e
      | _ => addAtom e
    else
      addAtom e
  | _ => addAtom e

def tst (e : Expr) : Elab.Term.TermElabM Unit := do
  let es ← (D2P.translate e).run {}
  let f := es.fst
  IO.println (repr f)

#getExprAndApply[True ∨ (False ↔ False) ∨ (2 = 3)|tst]
#getExprAndApply[True ∨ (False ↔ False) ∨ ((False = True) = True)|tst]

end D2P

end Auto