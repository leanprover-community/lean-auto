/-
This file provides the same structure for Real that exists for the other LamBaseSort types
It is the only file that imports Mathlib, and registers its constants through mutable references
which are used by Lean-auto to treat reals similarly to the way it handles integers.

Zero and one are handled specially because Lean represents them differently from other naturals.
sciVal is used to handle floats that are converted into reals.
-/

module

public import Lean
public import Mathlib.Data.Real.Basic
public import Auto.Translation.LamReif
public import Auto.Translation.LamUtils

@[expose] public section

namespace Auto.MathlibReal

open Lean Auto Auto.Embedding.Lam

noncomputable instance : RealTy ℝ := {}

abbrev Real.ofNat (n : Nat) : Real := (n : Real)
abbrev Real.ofInt (i : Int) := (i : Real)
abbrev Real.neg (r : Real) := -r
abbrev Real.abs (r : Real) := max r (-r)
abbrev Real.add (a b : Real) := a + b
abbrev Real.sub (a b : Real) := a - b
abbrev Real.mul (a b : Real) := a * b
noncomputable abbrev Real.div (a b : Real) := a / b
abbrev Real.le (a b : Real) : Prop := LE.le a b
abbrev Real.lt (a b : Real) : Prop := LT.lt a b
abbrev Real.ge (a b : Real) : Prop := Real.le b a
abbrev Real.gt (a b : Real) : Prop := Real.lt b a
abbrev Real.max (x y : Real) : Real := Max.max x y
abbrev Real.min (x y : Real) : Real := Min.min x y

def interpRealConstAsUnlifted : RealConst → CoreM Expr
| .sciVal n sgn exp => return ← (Lean.Meta.mkAppOptM ``OfScientific.ofScientific
  #[some (.const ``Real []), none, some (toExpr n), some (toExpr sgn), some (toExpr exp)]).run'
| .rzero => (do
  let ty := Expr.const ``Real []
  let inst ← Meta.synthInstance (← Meta.mkAppM ``Zero #[ty])
  return Lean.mkApp2 (.const ``Zero.zero [.zero]) ty inst).run'
| .rone => (do
  let ty := Expr.const ``Real []
  let inst ← Meta.synthInstance (← Meta.mkAppM ``One #[ty])
  return Lean.mkApp2 (.const ``One.one [.zero]) ty inst).run'
| .rofNat   => return .const ``Real.ofNat []
| .rofInt   => return .const ``Real.ofInt []
| .rneg     => return .const ``Real.neg []
| .rabs     => return .const ``Real.abs []
| .radd     => return .const ``Real.add []
| .rsub     => return .const ``Real.sub []
| .rmul     => return .const ``Real.mul []
| .rdiv     => return .const ``Real.div []
| .rle      => return .const ``Real.le []
| .rlt      => return .const ``Real.lt []
| .rmax     => return .const ``Real.max []
| .rmin     => return .const ``Real.min []

open Lam2D

initialize do
  realReconstructionExt.set (some {
    baseSort := .const ``Real []
    interpConst := interpRealConstAsUnlifted
  })

open LamReif

initialize do
  realReifExt.set (some {
    realTypeName := ``Real
    realTypeExpr := .const ``Real []
    arg2NoLit := [
      ((``NatCast.natCast, ``Real), (.const ``Real.ofNat [], .base .rofNat)),
      ((``IntCast.intCast, ``Real), (.const ``Real.ofInt [], .base .rofInt)),
      ((``Neg.neg,  ``Real), (.const ``Real.neg [], .base .rneg)),
      ((``LE.le,    ``Real), (.const ``Real.le [], .base .rle)),
      ((``GE.ge,    ``Real), (.const ``Real.ge [], .rge)),
      ((``LT.lt,    ``Real), (.const ``Real.lt [], .base .rlt)),
      ((``GT.gt,    ``Real), (.const ``Real.gt [], .rgt)),
      ((``Max.max,  ``Real), (.const ``Real.max [], .base .rmax)),
      ((``Min.min,  ``Real), (.const ``Real.min [], .base .rmin))
    ]
    arg4NoLit := [
      ((``HAdd.hAdd, ``Real, ``Real), (.const ``Real.add [], .base .radd)),
      ((``HSub.hSub, ``Real, ``Real), (.const ``Real.sub [], .base .rsub)),
      ((``HMul.hMul, ``Real, ``Real), (.const ``Real.mul [], .base .rmul)),
      ((``HDiv.hDiv, ``Real, ``Real), (.const ``Real.div [], .base .rdiv))
    ]
    ofNatConst := .const ``Real.ofNat []
    zeroConst  := mkApp2 (.const ``Zero.zero [.zero]) (.const ``Real []) (.const ``Real.instZero [])
    oneConst   := mkApp2 (.const ``One.one   [.zero]) (.const ``Real []) (.const ``Real.instOne [])
  })

-- Real version of tests found in Translation/LamUtils.lean
section CheckDefEq
  def realConstSimpNFList : List (Name × Expr) :=
    let realc := mkConst ``Real
    [
      (``Real.ofNat , mkApp2 (.const ``Nat.cast [.zero]) realc (mkConst ``Real.instNatCast)),
      (``Real.ofInt , mkApp2 (.const ``Int.cast [.zero]) realc (mkConst ``Real.instIntCast)),
      (``Real.neg   , mkApp2 (.const ``Neg.neg [.zero]) realc (mkConst ``Real.instNeg)),
      (``Real.add   , mkApp4
        (.const ``HAdd.hAdd [.zero, .zero, .zero]) realc realc realc
        (mkApp2 (.const ``instHAdd [.zero]) realc (mkConst ``Real.instAdd))),
      (``Real.sub   , mkApp4
        (.const ``HSub.hSub [.zero, .zero, .zero]) realc realc realc
        (mkApp2 (.const ``instHSub [.zero]) realc (mkConst ``Real.instSub))),
      (``Real.mul   , mkApp4
        (.const ``HMul.hMul [.zero, .zero, .zero]) realc realc realc
        (mkApp2 (.const ``instHMul [.zero]) realc (mkConst ``Real.instMul))),
      (``Real.div   , mkApp4
        (.const ``HDiv.hDiv [.zero, .zero, .zero]) realc realc realc
        (mkApp2 (.const ``instHDiv [.zero]) realc
        (mkApp2 (.const ``DivInvMonoid.toDiv [.zero]) realc (.const ``Real.instDivInvMonoid [])))),
      (``Real.le    , mkApp2 (.const ``LE.le [.zero]) realc (mkConst ``Real.instLE)),
      (``Real.lt    , mkApp2 (.const ``LT.lt [.zero]) realc (mkConst ``Real.instLT)),
      (``Real.max   , mkApp2 (.const ``Max.max [.zero]) realc (mkConst ``Real.instMax)),
      (``Real.min   , mkApp2 (.const ``Min.min [.zero]) realc (mkConst ``Real.instMin))
    ]

  private def checkLamBaseTermSimpNFMap : MetaM Unit :=
    for (name, e) in realConstSimpNFList do
      if !(← Meta.isTypeCorrect e) then
        throwError "{e} is not type correct"
      let e' := mkConst name
      if !(← Meta.withNewMCtxDepth (Meta.isDefEq e' e)) then
        throwError "{e'} is not definitionally equal to {e}"

  run_meta checkLamBaseTermSimpNFMap

end CheckDefEq

end Auto.MathlibReal
