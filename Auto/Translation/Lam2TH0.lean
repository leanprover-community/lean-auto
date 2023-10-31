import Auto.IR.TPTP_TH0
import Auto.Translation.LamReif

namespace Auto
open Lean Embedding.Lam Lam2TH0

def lam2TH0 (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort) (facts : Array LamTerm) : CoreM String := do
  let (typeHs, termHs, etomHs) ← LamReif.collectLamTermsAtoms lamVarTy lamEVarTy facts
  let bvHs := LamReif.collectLamTermsBitvecs facts
  let bvLengthHs := LamReif.collectLamSortsBitVecLengths (
    bvHs.toArray.map BitVecConst.lamCheck ++ lamVarTy ++ lamEVarTy)
  let ncHs := LamReif.collectLamTermsNatConsts facts
  let icHs := LamReif.collectLamTermsIntConsts facts
  let scHs := LamReif.collectLamTermsStringConsts facts
  let sorts :=
    ["thf(sortdecl_nat, type, s_nat: $tType).",
     "thf(sortdecl_int, type, s_int: $tType).",
     "thf(sortdecl_string, type, s_string: $tType).",
     "thf(sortdecl_empty, type, s_empty: $tType)."] ++
    bvLengthHs.toList.map (fun l => s!"thf(sortdecl_bv{l}, type, s_bv{l}: $tType).") ++
    typeHs.toList.map (fun i => s!"thf(sortdecl_{i}, type, s_a{i}: $tType).")
  let types :=
    ncHs.toList.map (fun nc => s!"thf(typedecl_icst_{transNatConst nc}, type, {transNatConst nc}: {transNatConstSort nc}).") ++
    icHs.toList.map (fun ic => s!"thf(typedecl_icst_{transIntConst ic}, type, {transIntConst ic}: {transIntConstSort ic}).") ++
    scHs.toList.map (fun sc => s!"thf(typedecl_icst_{transStringConst sc}, type, {transStringConst sc}: {transStringConstSort sc}).") ++
    bvHs.toList.map (fun bvc => s!"thf(typedecl_bv{transBitVecConst bvc}, type, t_bv{transBitVecConst bvc}: {transBitVecConstSort bvc}).") ++
     (← termHs.toList.mapM (fun i => do
      let .some s := lamVarTy.get? i
        | throwError "lam2TH0 :: Unexpected error"
      return s!"thf(typedecl_t_a{i}, type, t_a{i}: {transLamSort s}).")) ++
     (← etomHs.toList.mapM (fun i => do
      let .some s := lamEVarTy.get? i
        | throwError "lam2TH0 :: Unexpected error"
      return s!"thf(typedecl_t_e{i}, type, t_e{i}: {transLamSort s})."))
  -- Empty type is not inhabited
  if (lamVarTy ++ lamEVarTy).any (fun s => s == .base .empty) then
    return "thf(empty_inhabited, axiom, $false)."
  let facts ← facts.zipWithIndex.mapM (fun (t, i) =>
    match transLamTerm t with
    | .ok ts => return s!"thf(fact{i}, axiom, {ts})."
    | .error e => throwError e)
  let sep := "\n"
  return s!"{String.intercalate sep sorts}\n\n{String.intercalate sep types}\n\n{String.intercalate sep facts.data}"

end Auto
