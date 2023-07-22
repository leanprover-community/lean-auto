-- This file contains definitions of reification terms
import Lean
import Auto.Util.MonadUtils
import Auto.Translation.Lift
import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec.Defs
open Lean

-- Typed first-order logic without polymorphism
namespace Auto.ReifTF0

inductive TF0BaseSort
  | atom : Nat → TF0BaseSort
  | prop : TF0BaseSort             -- Lean `Prop`
  | nat  : TF0BaseSort             -- Lean `Nat`
  | real : TF0BaseSort             -- Mathlib `ℝ`
  | bv   : (n : Nat) → TF0BaseSort -- Mathlib Bitvec. `n` must be a numeral
deriving BEq, Hashable, Inhabited

structure TF0Sort where
  argTys : List TF0BaseSort
  resTy  : TF0BaseSort
deriving BEq, Hashable, Inhabited

inductive TF0Term : Type
  | natVal  : Nat → TF0Term
  | trueE   : TF0Term
  | falseE  : TF0Term
  | not     : TF0Term → TF0Term
  | and     : TF0Term → TF0Term → TF0Term
  | or      : TF0Term → TF0Term → TF0Term
  | iff     : TF0Term → TF0Term → TF0Term
  -- Supporting polymorphic `eq`
  | eq      : TF0Term → TF0Term → TF0Term
  | bvar    : (idx : Nat) → TF0Term
  | app     : (atom : Nat) → (appArgs : Array TF0Term) → TF0Term
  | forallE : (binderTy : TF0Sort) → (body : TF0Term) → TF0Term
deriving Inhabited, Hashable, BEq

section ToExpr
  
  def TF0BaseSort.toExpr (interp : Nat → Expr) : TF0BaseSort → Expr
  | .atom n => interp n
  | .prop   => Expr.sort Level.zero
  | .nat    => Expr.const ``Nat []
  | .real   => Expr.const ``Real []
  | .bv n   => mkApp (.const ``Bitvec []) (.lit (.natVal n))
  
  def TF0Sort.toExpr (interp : Nat → Expr) : TF0Sort → Expr := fun ⟨argTys, resTy⟩ =>
    go argTys resTy
  where
    go : List TF0BaseSort → TF0BaseSort → Expr
    | [], e      => e.toExpr interp
    | t :: ts, e => Expr.forallE `_ (t.toExpr interp) (go ts e) .default
  
  private structure ToExpr.Context where
    interpTy   : Nat → Expr
    interpTerm : Nat → Expr
  deriving Inhabited
  
  private structure ToExpr.State where
    lCtx       : Array Expr
  deriving Inhabited, Hashable, BEq
  
  private abbrev ToExprM := ReaderT ToExpr.Context (StateT ToExpr.State MetaM)
  
  #genMonadContext ToExprM
  #genMonadState ToExprM
  
  -- **TODO**: Eliminate `partial`
  partial def TF0Term.toExprAux : TF0Term → ToExprM Expr
  | .natVal n  => return .lit (.natVal n)
  | .trueE     => return .const ``true []
  | .falseE    => return .const ``false []
  | .not t     => do return ← Meta.mkAppM ``Not #[← toExprAux t]
  | .and t₁ t₂ => do return ← Meta.mkAppM ``And #[← toExprAux t₁, ← toExprAux t₂]
  | .or t₁ t₂  => do return ← Meta.mkAppM ``Or #[← toExprAux t₁, ← toExprAux t₂]
  | .iff t₁ t₂ => do return ← Meta.mkAppM ``Iff #[← toExprAux t₁, ← toExprAux t₂]
  | .eq t₁ t₂  => do
    let e₁ ← toExprAux t₁
    let e₂ ← toExprAux t₂
    return ← Meta.mkAppM ``Eq #[e₁, e₂]
  | .bvar i    => do
    let lctx ← ReifTF0.getLCtx
    if h : lctx.size > i then
      return lctx[lctx.size - (i + 1)]'(by
        apply Nat.sub_lt
        case a =>
          apply Nat.lt_of_le_of_lt (m:=i)
          simp; simp [h]
        case a => simp)
    else
      throwError "TF0Term.toExprAux :: Unknown bound variable {i} in local context {lctx}"
  | .app n args => do
    let fExpr := (← getInterpTerm) n
    let argsExpr ← args.mapM toExprAux
    return mkAppN fExpr argsExpr
  | .forallE ty body => do
    let tyExpr := ty.toExpr (← getInterpTy)
    Meta.withLocalDeclD (← mkFreshId) tyExpr fun e => do
      let lctx ← getLCtx
      setLCtx (lctx.push e)
      Meta.mkLambdaFVars #[e] (← body.toExprAux)
  
  -- #eval format <| TF0Sort.toExpr (fun _ => Expr.const ``Nat [])
  --  ⟨[.prop, .nat], (.atom 3)⟩
  
end ToExpr

@[reducible] def TF0BaseSort.interp.{u} (val : Nat → Type u) : TF0BaseSort → Type u
| .atom n => val n
| .prop   => GLift Prop
| .nat    => GLift Nat
| .real   => GLift Real
| .bv n   => GLift (Bitvec n)

@[reducible] def TF0Sort.interp.{u} (val : Nat → Type u) : (x : TF0Sort) → Type u :=
  fun ⟨argTys, resTy⟩ =>
    let argTys : List (Type u) := List.map (TF0BaseSort.interp val) argTys
    let resTy : Type u := resTy.interp val
    argTys.foldr (fun ty acc => ty → acc) resTy

-- Valuation
structure TF0Val.{u} where
  tyVal    : Nat → Type (u + 1)
  constVal : Nat → (s : TF0Sort) × TF0Sort.interp tyVal s

-- Judgement, `lctx ⊢ rterm ≝ mterm : ty`
structure TF0Judge.{u} where
  -- Local context, list of CIC terms
  lctx    : List ((α : Type (u + 1)) × α)
  -- A term in TF0
  rterm   : TF0Term
  -- Type of `mterm`
  ty      : Type (u + 1)
  -- The CIC term that `rterm` translates into
  mterm   : ty

inductive WF.{u} (val : TF0Val.{u}) : TF0Judge.{u} → Prop
--  | a : WF sorry sorry

end Auto.ReifTF0