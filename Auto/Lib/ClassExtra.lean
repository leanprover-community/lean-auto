import Lean
open Lean

namespace Auto

def showClasses (env : Environment) : Except String (Array (ConstantInfo × Array Nat)) := do
  let outParamMap := (classExtension.getState env).outParamMap
  (Array.mk outParamMap.toList).mapM (fun (name, outParams) => do
    let .some decl := env.find? name
      | throw s!"showClasses :: unknown declarationn {name}"
    return (decl, outParams))

private def instArgsAux (type : Expr) (idx : Nat) : List Nat :=
  match type with
  | .forallE _ _ body arg =>
    let trail := instArgsAux body (.succ idx)
    match arg with
    | .instImplicit => idx :: trail
    | _ => trail
  | _ => .nil

-- Given an expression `type`, which is the type of some
--   term `t`, find the arguments of `t` that are class
--   instances
def instArgs (type : Expr) : Array Nat := ⟨instArgsAux type 0⟩

end Auto