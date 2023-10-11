import Lean
import Std.Data.Array.Basic
open Lean

namespace Auto.DUnif

def metaEta (e : Expr) : MetaM (Option MVarId) := do
  let mctx ← getMCtx
  let e ← instantiateMVars e
  let result ← metaEtaAux e
  match result with
  | .some (headId, F, hmap) =>
    let headTy ← Meta.inferType (.mvar headId)
    let binding ← Meta.withDefault <| Meta.forallBoundedTelescope headTy hmap.size fun xs _ => do
      if hmap.size != xs.size then
        throwError "metaEta :: Unexpected error"
      let mut ret := F
      for argIdx in hmap do
        let .some x := xs[argIdx]?
          | throwError "metaEta :: Unexpected error"
        ret := Expr.app ret x
      Meta.mkLambdaFVars xs ret
    headId.assign binding
    let .mvar id := (← instantiateMVars F).eta
      | throwError "metaEta :: Unexpected error"
    return id
  | .none => setMCtx mctx; return none
where metaEtaAux (e : Expr) : MetaM (Option (MVarId × Expr × Array Nat)) :=
  Meta.lambdaTelescope e fun xs body => do
    let head := body.getAppFn
    let args := body.getAppArgs
    let .mvar headId := head
      | return none
    if args.size != xs.size then
      return none
    -- hmap : Map from position in `xs` to argIdx of `head`
    let xsMap := @HashMap.ofList Expr Nat inferInstance inferInstance
      xs.zipWithIndex.toList
    let mut hmap : Array Nat := ⟨List.range xs.size⟩
    let mut hset : HashSet Nat := {}
    for (arg, argIdx) in args.zipWithIndex do
      let .some xsIdx := xsMap.find? arg
        | return .none
      if hset.contains xsIdx then return .none
      hset := hset.insert xsIdx
      hmap := hmap.setD xsIdx argIdx
    let F ← Meta.mkFreshExprMVar (← Meta.inferType head)
    let F ← Meta.mkLambdaFVars xs F
    return .some (headId, F, hmap)

/-- Make the most general function type with `n` explicit binders -/
def mkGeneralFnTy (n : Nat) (resTy : Option Expr := .none) : MetaM Expr :=
  match n with
  | 0 =>
    match resTy with
    | .some resTy => return resTy
    | .none => Meta.mkFreshTypeMVar
  | n + 1 => do
    let bty ← Meta.mkFreshTypeMVar
    let userName := Name.mkStr1 s!"gen{n}"
    Meta.withLocalDeclD userName bty fun x => do
      let res ← mkGeneralFnTy n resTy
      Meta.mkForallFVars #[x] <| res

/-- Make an implication with `n` explicit binders -/
def mkImplication (n : Nat) (resTy : Option Expr := .none) : MetaM Expr := do
  let argTys_ty ← (Array.mk (List.range n)).mapM (fun _ => Meta.mkFreshLevelMVar)
  let argTys ← argTys_ty.mapM (fun e => Meta.mkFreshExprMVar (Expr.sort e))
  let declInfos := argTys.zipWithIndex.map (fun (argTy, nat) => (Name.mkStr1 s!"imp{nat}", fun _ => pure argTy))
  let resTy ← (do
    match resTy with
    | .some resTy => return resTy
    | .none => Meta.mkFreshTypeMVar)
  Meta.withLocalDeclsD declInfos fun xs => Meta.mkForallFVars xs resTy

end Auto.DUnif