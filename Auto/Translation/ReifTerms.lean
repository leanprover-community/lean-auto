-- This file contains definitions of reification terms
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

section
  
  -- Type of (terms in more expressive logic)
  variable (ω : Type) [BEq ω] [Hashable ω]
  
  -- State of TransM (from more expressive logic to propositional logic)
  -- Note that We do not have to record declarations because we only have to
  --   (declare-const x0 bool) ... (declare-const x(k-1) bool)
  --   where `k` is `h2lMap.size`
  -- We also do not need to record the state of
  --   the low-level name generator because its state is `h2lMap.size`
  structure State where
    -- Map from high-level construct to atom index
    h2lMap     : HashMap ω Nat  := HashMap.empty
    -- Inverse of `h2lMap`
    -- Map from atom index to high-level construct
    l2hMap     : HashMap Nat ω  := HashMap.empty
    -- List of assertions
    assertions : Array PropForm := #[]
  
  abbrev TransM := StateRefT (State ω) MetaM

  variable {ω : Type} [BEq ω] [Hashable ω]
  
  @[always_inline]
  instance : Monad (TransM ω) :=
    let i := inferInstanceAs (Monad (TransM ω));
    { pure := i.pure, bind := i.bind }
  
  instance : Inhabited (TransM ω α) where
    default := fun _ => throw default

  def getH2lMap : TransM ω (HashMap ω Nat) := do
    return (← get).h2lMap

  def getL2hMap : TransM ω (HashMap Nat ω) := do
    return (← get).l2hMap

  def getAssertions : TransM ω (Array PropForm) := do
    return (← get).assertions

  def setH2lMap (m : HashMap ω Nat) : TransM ω Unit :=
    modify (fun s => {s with h2lMap := m})

  def setL2hMap (m : HashMap Nat ω) : TransM ω Unit :=
    modify (fun s => {s with l2hMap := m})

  def setAssertions (a : Array PropForm) : TransM ω Unit :=
    modify (fun s => {s with assertions := a})
  
  def hIn (e : ω) : TransM ω Bool := do
    return (← getH2lMap).contains e

  def h2Atom (e : ω) : TransM ω PropForm := do
    let ⟨h2lMap, l2hMap, _⟩ ← get
    if h2lMap.contains e then
      return .Atom (h2lMap.find! e)
    let sz := h2lMap.size
    setH2lMap (h2lMap.insert e sz)
    setL2hMap (l2hMap.insert sz e)
    return .Atom sz

  def addAssertion (a : PropForm) : TransM ω Unit := do
    let assertions ← getAssertions
    setAssertions (assertions.push a)
  
end

end ReifP

end Auto