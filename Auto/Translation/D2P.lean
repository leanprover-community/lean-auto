import Lean
import Auto.Util.MonadUtils
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

def addAtom (e : Expr) : TransM Nat := do
  let ⟨exprMap, idxMap⟩ ← get
  if exprMap.contains e then
    return exprMap.find! e
  let sz := exprMap.size
  setExprMap (exprMap.insert e sz)
  setIdxMap (idxMap.insert sz e)
  return sz

inductive PropForm where
  | Atom  : Nat → PropForm
  | True  : PropForm
  | False : PropForm
  | Not   : PropForm → PropForm
  | And   : PropForm → PropForm → PropForm
  | Or    : PropForm → PropForm → PropForm
  | Iff   : PropForm → PropForm → PropForm
  | Eq    : PropForm → PropForm → PropForm
deriving Inhabited

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
    | _ => do
      let idx ← addAtom e
      return .Atom idx
  | .app .. =>
    let f := e.getAppFn
    let some name := f.constName?
      | throwError failureMsg
    let args := e.getAppArgs
    if args.size == 1 then
      let args ← args.mapM translate
      match name with
      | ``Not => return .Not args[0]!
      | _ => throwError failureMsg
    else if args.size == 2 then
      let args ← args.mapM translate
      match name with
      | ``And => return .And args[0]! args[1]!
      | ``Or => return .Or args[0]! args[1]!
      | ``Iff => return .Iff args[0]! args[1]!
      | ``Eq => return .Eq args[0]! args[1]!
      | _ => throwError failureMsg
    else
      throwError failureMsg
  | _ => do
    let idx ← addAtom e
    return .Atom idx

end D2P

end Auto