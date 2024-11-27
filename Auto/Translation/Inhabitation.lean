import Lean
import Auto.Translation.Assumptions
import Auto.Lib.ExprExtra
open Lean

namespace Auto.Inhabitation

private def logicalConsts : Std.HashSet Name := Std.HashSet.empty.insertMany
  #[``Eq, ``Exists, ``And, ``Or, ``Iff, ``Not]

/--
  Given an expression, return the array of positions of
    minimal non-implication subexpressions
  e.g. for `((a → b → c) → (d → e))`, we have
    `[(0, 0), (0, 1, 0), (0, 1, 1), (1, 0), (1, 1)]`
-/
def getMinimalNonImpPositions (e : Expr) : Array (Array Bool) :=
  go #[] e
where go (pos : Array Bool) (e : Expr) : Array (Array Bool) :=
  match e with
  | .forallE _ ty body _ =>
    if body.hasLooseBVar 0 then
      #[pos]
    else
      let tys := go (pos.push false) ty
      let bodys := go (pos.push true) body
      tys ++ bodys
  | _ => #[pos]

def getExprNonImpPosition (pos : Array Bool) (e : Expr) : Option Expr :=
  go pos.toList e
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
    let mut ty ← instantiateMVars decl.type
    let mut proof := Expr.fvar fid
    let quickConstCheck (e : Expr) : Bool :=
      match e with
      | .const name _ => logicalConsts.contains name
      | _ => false
    -- Ignore variables whose type contains logical constants
    if let .some _ := Expr.find? quickConstCheck ty then
      continue
    -- Ignore variables whose type is a dependent forall
    if let .some _ := Expr.find? Expr.isDepForall (Expr.stripLeadingDepForall ty) then
      continue
    -- Process `Nonempty` and `Inhabited`
    if let .some name ← Meta.isClass? ty then
      if name == ``Nonempty then
        let ty' ← Meta.mkFreshTypeMVar
        if ← Meta.isDefEq ty (← Meta.mkAppM ``Nonempty #[ty']) then
          ty ← instantiateMVars ty'
          proof ← Meta.mkAppM ``Classical.choice #[proof]
      if name == ``Inhabited then
        let ty' ← Meta.mkFreshTypeMVar
        if ← Meta.isDefEq ty (← Meta.mkAppM ``Inhabited #[ty']) then
          ty ← instantiateMVars ty'
          proof ← Meta.mkAppOptM ``Inhabited.default #[.none, proof]
    -- Ignore `Prop`s
    if ← isDefEq (← inferType ty) (.sort .zero) then
      continue
    let mut new := true
    for lem in ret do
      if lem.type == ty then
        new := false; break
    if !new then continue
    for lem in ret do
      if ← isDefEq lem.type ty then
        new := false; break
    if !new then continue
    let name ← fid.getUserName
    ret := ret.push ⟨⟨proof, ty, .leaf s!"lctxInh {name}"⟩, #[]⟩
  return ret

private def inhFactMatchAtomTysAux (inhTy : Lemma) (atomTys : Array Expr) : MetaM LemmaInsts :=
  Meta.withNewMCtxDepth do
    let mips := getMinimalNonImpPositions (Expr.stripLeadingDepForall inhTy.type)
    let mut lis : LemmaInsts := #[← LemmaInst.ofLemmaLeadingDepOnly inhTy]
    for mip in mips do
      let mut newInsts : LemmaInsts := #[]
      for li in lis do
        let s ← saveState
        let (_, _, mi) ← MLemmaInst.ofLemmaInst li
        let .some e := getExprNonImpPosition mip mi.type
          | throwError "{decl_name%} :: Unexpected error, cannot get position {mip} from {mi.type}"
        for a in atomTys do
          let s' ← saveState
          if (← Meta.isDefEq e a) then
            let newli ← LemmaInst.ofMLemmaInst mi
            if ← newInsts.newInst? newli then
              newInsts := newInsts.push newli
          restoreState s'
        restoreState s
      lis := newInsts
    return lis

def inhFactMatchAtomTys (inhTys : Array Lemma) (atomTys : Array Expr) : MetaM (Array UMonoFact) := do
  let liss ← inhTys.mapM (fun inhTy => inhFactMatchAtomTysAux inhTy atomTys)
  let mut ret : Array UMonoFact := #[]
  for li in liss.concatMap id do
    if li.params.size != 0 || li.nbinders != 0 then continue
    let mut new? := true
    let canTy ← canonicalize li.type atomTys
    for ⟨_, ty, _⟩ in ret do
      if canTy == ty then
        new? := false
    if !new? then continue
    ret := ret.push ⟨li.proof, canTy, li.deriv⟩
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
    throwError "{decl_name%} :: Unable to canonicalize {inhTy}"

end Auto.Inhabitation
