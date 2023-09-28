import Lean
import Auto.Translation.Assumptions
import Auto.Lib.ExprExtra
open Lean

namespace Auto.Inhabitation

private def logicalConsts : HashSet Name := HashSet.empty.insertMany
  #[``Eq, ``Exists, ``And, ``Or, ``Iff, ``Not]

-- Given an expression, return the array of positions of
--   minimal non-implication subexpressions
-- e.g. for `((a → b → c) → (d → e))`, we have
--   `[(0, 0), (0, 1, 0), (0, 1, 1), (1, 0), (1, 1)]`
def getMinimalNonImpPositions (e : Expr) : Array (Array Bool) :=
  go #[] e
where go (pos : Array Bool) (e : Expr) : Array (Array Bool) :=
  match e with
  | .forallE _ ty body _ =>
    if body.hasLooseBVar 0 then
      #[pos]
    else
      let tys := go (pos.push false) ty
      let bodys := go (pos.push true) ty
      tys ++ bodys
  | _ => #[pos]

def getExprNonImpPosition (pos : Array Bool) (e : Expr) : Option Expr :=
  go pos.data e
where go (pos : List Bool) (e : Expr) : Option Expr :=
  match pos with
  | .nil => .some e
  | .cons b pos =>
    match e with
    | .forallE _ ty body _ =>
      if b then
        go pos body
      else
        go pos ty
    | _ => .none

open Meta in
def getInhFactsFromLCtx : MetaM (Array Lemma) := withNewMCtxDepth do
  let lctxDecls := (← read).lctx.fvarIdToDecl
  let mut ret : Array Lemma := #[]
  for (fid, decl) in lctxDecls.toList do
    let ty ← instantiateMVars decl.type
    if ← isDefEq (← inferType ty) (.sort .zero) then
      continue
    let quickConstCheck (e : Expr) : Bool :=
      match e with
      | .const name _ => logicalConsts.contains name
      | _ => false
    if let .some _ := Expr.find? quickConstCheck ty then
      continue
    if let .some _ := Expr.find? Expr.isForall (Expr.stripForall ty) then
      continue
    ret := ret.push ⟨.fvar fid, ty, #[]⟩
  return ret

private def inhFactMatchAtomTysAux (inhTy : Lemma) (atomTys : Array Expr) : MetaM LemmaInsts :=
  Meta.withNewMCtxDepth do
    let mips := getMinimalNonImpPositions (Expr.stripForall inhTy.type)
    let mut lis : LemmaInsts := #[← LemmaInst.ofLemma inhTy]
    for mip in mips do
      let mut newInsts : LemmaInsts := #[]
      for li in lis do
        let s ← saveState
        let (_, _, mi) ← MLemmaInst.ofLemmaInst li
        let .some e := getExprNonImpPosition mip mi.type
          | throwError "inhFactMatchAtomTys :: Unexpected error"
        for a in atomTys do
          let s' ← saveState
          if (← Meta.isDefEq e a) then
            let newli ← LemmaInst.ofMLemmaInst mi
            if ← newInsts.newInst? newli then
              newInsts := newInsts.push newli
            newInsts := newInsts.push (← LemmaInst.ofMLemmaInst mi)
          restoreState s'
        restoreState s
      lis := newInsts
    return lis

def inhFactMatchAtomTys (inhLem : Lemma) (atomTys : Array Expr) : MetaM (Array UMonoFact) := do
  let lis ← inhFactMatchAtomTysAux inhLem atomTys
  let mut ret : Array UMonoFact := #[]
  for li in lis do
    if li.params.size != 0 || li.nbinders != 0 then continue
    ret := ret.push ⟨li.proof, ← canonicalize li.type atomTys⟩
  return ret
where
  canonicalize (inhTy : Expr) (atomTys : Array Expr) : MetaM Expr :=
    match inhTy with
    | .forallE name ty body bi => do
      if body.hasLooseBVar 0 then
        canonicalizeAtomic inhTy atomTys
      else
        return .forallE name (← canonicalize ty atomTys) (← canonicalize body atomTys) bi
    | _ => canonicalizeAtomic inhTy atomTys
  canonicalizeAtomic (inhTy : Expr) (atomTys : Array Expr) : MetaM Expr := do
    for a in atomTys do
      if (← Meta.withNewMCtxDepth (Meta.isDefEq inhTy a)) then
        return inhTy
    throwError "inhFactMatchAtomTys :: Unable to canonicalize {inhTy}"

end Auto.Inhabitation