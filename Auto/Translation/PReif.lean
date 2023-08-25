import Lean
import Auto.Lib.MonadUtils
open Lean

-- Propositional reification terms
namespace Auto.PReif

inductive PropForm where
  | atom   : Nat → PropForm
  | trueE  : PropForm
  | falseE : PropForm
  | not    : PropForm → PropForm
  | and    : PropForm → PropForm → PropForm
  | or     : PropForm → PropForm → PropForm
  | imp    : PropForm → PropForm → PropForm
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
    | .imp f1 f2 => f!".imp " ++ reprPrecPropForm f1 1 ++ f!" " ++ reprPrecPropForm f2 1
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
| .imp f₁ f₂ => f₁.interp val → f₂.interp val
| .iff f₁ f₂ => Iff (f₁.interp val) (f₂.interp val)
| .eq f₁ f₂  => f₁.interp val = f₂.interp val

section
  
  -- Type of (terms in more expressive logic)
  variable (ω : Type) [BEq ω] [Hashable ω]
  
  -- State of ReifM (from more expressive logic to propositional logic)
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
  
  abbrev ReifM := StateRefT (State ω) MetaM

  variable {ω : Type} [BEq ω] [Hashable ω]
  
  @[always_inline]
  instance : Monad (ReifM ω) :=
    let i := inferInstanceAs (Monad (ReifM ω));
    { pure := i.pure, bind := i.bind }
  
  instance : Inhabited (ReifM ω α) where
    default := fun _ => throw default

  #genMonadState (ReifM ω)
  
  def hIn (e : ω) : ReifM ω Bool := do
    return (← getH2lMap).contains e

  def h2Atom (e : ω) : ReifM ω PropForm := do
    let ⟨h2lMap, l2hMap, _⟩ ← get
    if h2lMap.contains e then
      return .atom (h2lMap.find! e)
    let sz := h2lMap.size
    setH2lMap (h2lMap.insert e sz)
    setL2hMap (l2hMap.insert sz e)
    return .atom sz

  def addAssertion (a : PropForm) : ReifM ω Unit := do
    let assertions ← getAssertions
    setAssertions (assertions.push a)
  
end

end PReif

-- Open `D`
open Lean
-- Open `P`
open PReif

-- Translates an expression of type `Prop`
partial def D2P (e : Expr) : ReifM Expr PropForm := do
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
  | .forallE name biTy body binfo => do
    if body.hasLooseBVar 0 ∨ !(← Meta.isProp biTy) ∨ !(← Meta.isProp body) then
      h2Atom e
    else
      Meta.withLocalDecl name binfo biTy fun fvar => do
        let fnTy ← D2P biTy
        let argTy ← D2P (body.instantiate1 fvar)
        return .imp fnTy argTy
  | _ => h2Atom e

def tst (e : Expr) : Elab.Term.TermElabM Unit := do
  let es ← (D2P e).run {}
  let f := es.fst
  IO.println (repr f)

-- #getExprAndApply[True ∨ (False ↔ False) ∨ (2 = 3) ∨ (2 = 3)|tst]
-- #getExprAndApply[True ∨ (False ↔ False) ∨ ((False = True) = True)|tst]

end Auto