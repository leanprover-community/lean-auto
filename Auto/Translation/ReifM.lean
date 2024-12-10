import Lean
import Auto.Lib.MonadUtils
import Auto.Translation.Assumptions
import Auto.Translation.Inductive
open Lean

namespace Auto.Reif

structure State where
  -- The set of facts to be processed
  --   This field changes during translation. For example,
  --   during monomorphization, the polymorphic facts
  --   will be removed from `facts` and the instantiated
  --   versions will be added to `facts`.
  facts           : Array UMonoFact     := #[]
  -- During monomorphization, constants will be turned
  --   into free variables. This map records the original expression
  --   corresponding to these free variables.
  exprFVarVal     : Std.HashMap FVarId Expr := {}
  -- Canonicalization map for types
  tyCanMap        : Std.HashMap Expr Expr   := {}
  -- Inhabited canonicalized types
  -- The second `Expr` should be of the form `ty₁ → ty₂ → ⋯ → tyₙ`,
  --   where `ty₁, ty₂, ⋯, tyₙ` are canonicalized types within `tyCanMap`
  inhTys          : Array UMonoFact     := {}
  inds            : Array (Array SimpleIndVal) := {}
  declName?       : Option Name

abbrev ReifM := StateT State MetaM

#genMonadState ReifM

/--
  Given an expression `e`, if it's a `fvar` and is in `polyVal`,
    return its value recorded in `exprFVarVal`. Otherwise return `e`
-/
@[inline] def resolveVal (e : Expr) : ReifM Expr :=
  match e with
  | .fvar id => do return ((← getExprFVarVal).get? id).getD e
  | _ => return e

@[inline] def resolveTy (e : Expr) : ReifM Expr := do
  match (← getTyCanMap).get? (Expr.eraseMData e) with
  | .some id => return id
  | .none => throwError "{decl_name%} :: Unable to resolve {e}"

def mkAuxName (suffix : Name) : ReifM Name := do
  match (← getDeclName?) with
  | none          => throwError "{decl_name%} :: auxiliary declaration cannot be created when declaration name is not available"
  | some declName => Lean.mkAuxName (declName ++ suffix) 1

end Auto.Reif
