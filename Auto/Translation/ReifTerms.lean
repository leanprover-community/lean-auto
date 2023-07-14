import Lean
import Auto.Util.MonadUtils
open Lean

namespace Auto

-- Propositional reification terms
namespace ReifP

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

def reprPrecPropForm (f : PropForm) (b : Bool) :=
  let s :=
    match f with
    | .Atom n    => f!".Atom {n}"
    | .True      => f!".True"
    | .False     => f!".False"
    | .Not g     => f!".Not " ++ reprPrecPropForm g true
    | .And f1 f2 => f!".And " ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
    | .Or f1 f2  => f!".Or "  ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
    | .Iff f1 f2 => f!".Iff " ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
    | .Eq f1 f2  => f!".Eq "  ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
  if b then
    f!"(" ++ s ++ ")"
  else
    f!"Auto.D2P.PropForm" ++ s

instance : Repr PropForm where
  reprPrec f n := reprPrecPropForm f (n != 0)

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

#genMonadGetSet ReifP.TransM ReifP.State

def addAtom (e : Expr) : TransM PropForm := do
  let ⟨exprMap, idxMap⟩ ← get
  if exprMap.contains e then
    return .Atom (exprMap.find! e)
  let sz := exprMap.size
  setExprMap (exprMap.insert e sz)
  setIdxMap (idxMap.insert sz e)
  return .Atom sz

end ReifP

end Auto