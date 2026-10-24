module

public import Auto.IR.TPTP_TH0
public import Auto.Translation.LamUtils

public section

namespace Auto
open Lean Embedding.Lam Lam2TH0

def lam2TH0 (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort) (facts : Array LamTerm) : CoreM String := do
  let (typeHs, termHs, etomHs) ← LamExportUtils.collectLamTermsAtoms lamVarTy lamEVarTy facts
  let bvHs := LamExportUtils.collectLamTermsBitvecs facts
  let bvLengthHs := LamExportUtils.collectLamSortsBitVecLengths (
    bvHs.toArray.map BitVecConst.lamCheck ++ lamVarTy ++ lamEVarTy)
  let ncHs := LamExportUtils.collectLamTermsNatConsts facts
  let icHs := LamExportUtils.collectLamTermsIntConsts facts
  let qcHs := LamExportUtils.collectLamTermsRatConsts facts
  let scHs := LamExportUtils.collectLamTermsStringConsts facts
  let lcHs := LamExportUtils.collectLamTermsLaterConsts facts
  let sorts :=
    ["thf(sortdecl_nat, type, s_nat: $tType).",
     "thf(sortdecl_int, type, s_int: $tType).",
     "thf(sortdecl_rat, type, s_rat: $tType).",
     "thf(sortdecl_string, type, s_string: $tType).",
     "thf(sortdecl_empty, type, s_empty: $tType).",
     "thf(sortdecl_real, type, s_real: $tType).",
     "thf(sortdecl_complex, type, s_complex: $tType)."] ++
    bvLengthHs.toList.map (fun l => s!"thf(sortdecl_bv{l}, type, s_bv{l}: $tType).") ++
    typeHs.toList.map (fun i => s!"thf(sortdecl_{i}, type, s_a{i}: $tType).")
  let types :=
    ncHs.toList.map (fun nc => s!"thf(typedecl_icst_{transNatConst nc}, type, {transNatConst nc}: {transNatConstSort nc}).") ++
    icHs.toList.map (fun ic => s!"thf(typedecl_icst_{transIntConst ic}, type, {transIntConst ic}: {transIntConstSort ic}).") ++
    qcHs.toList.map (fun qc => s!"thf(typedecl_qcst_{transRatConst qc}, type, {transRatConst qc}: {transRatConstSort qc}).") ++
    scHs.toList.map (fun sc => s!"thf(typedecl_icst_{transStringConst sc}, type, {transStringConst sc}: {transStringConstSort sc}).") ++
    bvHs.toList.map (fun bvc => s!"thf(typedecl_bv{transBitVecConst bvc}, type, t_bv{transBitVecConst bvc}: {transBitVecConstSort bvc}).") ++
    lcHs.toList.map (fun lc => s!"thf(typedecl_lcst_{transLaterConst lc}, type, {transLaterConst lc}: {transLaterConstSort lc}).") ++
     (← termHs.toList.mapM (fun i => do
      let .some s := lamVarTy[i]?
        | throwError "{decl_name%} :: Unexpected error"
      return s!"thf(typedecl_t_a{i}, type, t_a{i}: {transLamSort s}).")) ++
     (← etomHs.toList.mapM (fun i => do
      let .some s := lamEVarTy[i]?
        | throwError "{decl_name%} :: Unexpected error"
      return s!"thf(typedecl_t_e{i}, type, t_e{i}: {transLamSort s})."))
  -- Empty type is not inhabited
  if (lamVarTy ++ lamEVarTy).any (fun s => s == .base .empty) then
    return "thf(empty_inhabited, axiom, $false)."
  let facts ← facts.zipIdx.mapM (fun (t, i) =>
    match transLamTerm t with
    | .ok ts => return s!"thf(fact{i}, axiom, {ts})."
    | .error e => throwError e)
  let sep := "\n"
  return s!"{String.intercalate sep sorts}\n\n{String.intercalate sep types}\n\n{String.intercalate sep facts.toList}"

end Auto
