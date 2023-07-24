import Lean
import Auto.Util.MonadUtils
open Lean

-- Propositional reification terms
namespace Auto.ReifP

inductive PropForm where
  | atom   : Nat → PropForm
  | trueE  : PropForm
  | falseE : PropForm
  | not    : PropForm → PropForm
  | and    : PropForm → PropForm → PropForm
  | or     : PropForm → PropForm → PropForm
  | iff    : PropForm → PropForm → PropForm
  | eq     : PropForm → PropForm → PropForm
deriving Inhabited, Hashable, BEq

def reprPrecPropForm (f : PropForm) (n : Nat) :=
  let s :=
    match f with
    | .atom n    => f!".atom {n}"
    | .trueE     => f!".trueE"
    | .falseE    => f!".falseE"
    | .not g     => f!".not " ++ reprPrecPropForm g 1
    | .and f1 f2 => f!".and " ++ reprPrecPropForm f1 1 ++ f!" " ++ reprPrecPropForm f2 1
    | .or f1 f2  => f!".or "  ++ reprPrecPropForm f1 1 ++ f!" " ++ reprPrecPropForm f2 1
    | .iff f1 f2 => f!".iff " ++ reprPrecPropForm f1 1 ++ f!" " ++ reprPrecPropForm f2 1
    | .eq f1 f2  => f!".eq "  ++ reprPrecPropForm f1 1 ++ f!" " ++ reprPrecPropForm f2 1
  if n == 0 then
    f!"Auto.D2P.PropForm" ++ s
  else
    f!"(" ++ s ++ ")"

instance : Repr PropForm where
  reprPrec f n := reprPrecPropForm f n

def PropForm.interp (val : Nat → Prop) : PropForm → Prop
| .atom n    => val n
| .trueE     => True
| .falseE    => false
| .not f     => Not (f.interp val)
| .and f₁ f₂ => And (f₁.interp val) (f₂.interp val)
| .or f₁ f₂  => Or (f₁.interp val) (f₂.interp val)
| .iff f₁ f₂ => Iff (f₁.interp val) (f₂.interp val)
| .eq f₁ f₂  => f₁.interp val = f₂.interp val

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

  #genMonadState (TransM ω)
  
  def hIn (e : ω) : TransM ω Bool := do
    return (← getH2lMap).contains e

  def h2Atom (e : ω) : TransM ω PropForm := do
    let ⟨h2lMap, l2hMap, _⟩ ← get
    if h2lMap.contains e then
      return .atom (h2lMap.find! e)
    let sz := h2lMap.size
    setH2lMap (h2lMap.insert e sz)
    setL2hMap (l2hMap.insert sz e)
    return .atom sz

  def addAssertion (a : PropForm) : TransM ω Unit := do
    let assertions ← getAssertions
    setAssertions (assertions.push a)
  
end

end Auto.ReifP