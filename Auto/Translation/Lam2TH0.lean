import Auto.IR.TPTP_TH0
import Auto.Translation.LamReif

namespace Auto
open Lean Embedding.Lam Lam2TH0

def lam2TH0 (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort) (facts : Array LamTerm) : CoreM String := do
  let (typeHs, termHs, etomHs) ← LamReif.collectLamTermsAtoms lamVarTy lamEVarTy facts
  let bvHs := LamReif.collectLamTermsBitvecs facts
  let sorts :=
    bvHs.toList.map (fun l => s!"thf(sortdecl_bv{l.length}, type, s_bv{l.length}: $tType).") ++ 
    typeHs.toList.map (fun i => s!"thf(sortdecl_{i}, type, s_a{i}: $tType).")
  let types :=
    bvHs.toList.map (fun l => s!"thf(typedecl_bv{transBitvec l}, type, t_bv{transBitvec l}: s_bv{l.length}).") ++
    (← termHs.toList.mapM (fun i => do
      let .some s := lamVarTy.get? i
        | throwError "lam2TH0 :: Unexpected error"
      return s!"thf(typedecl_t_a{i}, type, t_a{i}: {transLamSort s}).")) ++
     (← etomHs.toList.mapM (fun i => do
      let .some s := lamEVarTy.get? i
        | throwError "lam2TH0 :: Unexpected error"
      return s!"thf(typedecl_t_e{i}, type, t_e{i}: {transLamSort s})."))
  let facts ← facts.zipWithIndex.mapM (fun (t, i) =>
    match transLamTerm t with
    | .ok ts => return s!"thf(fact{i}, axiom, {ts})."
    | .error e => throwError e)
  let sep := "\n"
  return s!"{String.intercalate sep sorts}\n\n{String.intercalate sep types}\n\n{String.intercalate sep facts.data}"

end Auto