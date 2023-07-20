-- This file contains definitions of reification terms
import Lean
import Auto.Util.MonadUtils
import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec.Defs
open Lean


namespace Auto

-- Propositional reification terms
namespace ReifP

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

def reprPrecPropForm (f : PropForm) (b : Bool) :=
  let s :=
    match f with
    | .atom n    => f!".atom {n}"
    | .trueE     => f!".trueE"
    | .falseE    => f!".falseE"
    | .not g     => f!".not " ++ reprPrecPropForm g true
    | .and f1 f2 => f!".and " ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
    | .or f1 f2  => f!".or "  ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
    | .iff f1 f2 => f!".iff " ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
    | .eq f1 f2  => f!".eq "  ++ reprPrecPropForm f1 true ++ f!" " ++ reprPrecPropForm f2 true
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
      return .atom (h2lMap.find! e)
    let sz := h2lMap.size
    setH2lMap (h2lMap.insert e sz)
    setL2hMap (l2hMap.insert sz e)
    return .atom sz

  def addAssertion (a : PropForm) : TransM ω Unit := do
    let assertions ← getAssertions
    setAssertions (assertions.push a)
  
end

end ReifP

-- Typed first-order logic without polymorphism
namespace ReifTF0

inductive TF0Sort
| atom : Nat → TF0Sort
| prop : TF0Sort             -- Lean `Prop`
| nat  : TF0Sort             -- Lean `Nat`
| real : TF0Sort             -- Mathlib `ℝ`
| bv   : (n : Nat) → TF0Sort -- Mathlib Bitvec. `n` must be a numeral
| func : Array TF0Sort → TF0Sort → TF0Sort
deriving Inhabited, Hashable, BEq

partial def TF0Sort.toExpr (interp : Nat → Expr) : TF0Sort → Expr
| .prop        => Expr.sort Level.zero
| .nat         => Expr.const ``Nat []
| .real        => Expr.const ``Real []
| .bv n        => mkApp (.const ``Bitvec []) (.lit (.natVal n))
| .atom n      => interp n
| .func ⟨bs⟩ r  => go bs (TF0Sort.toExpr interp r)
where
  go : List TF0Sort → Expr → Expr
  | [], e      => e
  | t :: ts, e => Expr.forallE `_ (TF0Sort.toExpr interp t) (go ts e) .default

inductive TF0Term : Type
| atom    : Nat → TF0Term
| natVal  : Nat → TF0Term
| trueE   : TF0Term
| falseE  : TF0Term
| not     : TF0Term → TF0Term
| and     : TF0Term → TF0Term → TF0Term
| or      : TF0Term → TF0Term → TF0Term
| iff     : TF0Term → TF0Term → TF0Term
| eq      : TF0Term → TF0Term → TF0Term
| bvar    : (idx : Nat) → TF0Term
| app     : (appFn : TF0Term) → (appArgs : Array TF0Term) → TF0Term
| forallE : (binderTy : TF0Sort) → (body : TF0Term) → TF0Term
deriving Inhabited, Hashable, BEq

structure ToExpr.Context where
  interpTy   : Nat → Expr
  interpTerm : Nat → Expr
deriving Inhabited

structure ToExpr.State where
  lctx       : Array Expr
deriving Inhabited, Hashable, BEq

abbrev ToExprM := ReaderT ToExpr.Context (StateM ToExpr.State)

partial def TF0Term.toExpr (interpTy : Nat → Expr) (interpTerm : Nat → Expr) : TF0Term → Expr
| .atom n    => interpTerm n
| .natVal n  => .lit (.natVal n)
| .trueE     => .const ``true []
| .falseE    => .const ``false []

#eval format <| TF0Sort.toExpr (fun _ => Expr.const ``Nat []) (.func #[.prop, .nat] (.atom 3))

end ReifTF0

end Auto