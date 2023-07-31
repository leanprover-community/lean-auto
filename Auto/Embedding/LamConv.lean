import Auto.Embedding.LamBase

namespace Auto.Embedding.Lam

-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (Nat.succ ?n)`
def LamTerm.bvarLiftIdx (idx : Nat) : LamTerm → LamTerm
| .atom n     => .atom n
| .base b     => .base b
| .bvar n     => .bvar (popLCtxAt id idx n)
| .lam s t    => .lam s (t.bvarLiftIdx (Nat.succ idx))
| .app fn arg => .app (fn.bvarLiftIdx idx) (arg.bvarLiftIdx idx)

def LamTerm.bvarLift : LamTerm → LamTerm := LamTerm.bvarLiftIdx 0

def LamTerm.bvarLifts (t : LamTerm) : (lvl : Nat) → LamTerm
| 0 => t
| lvl' + 1 => (t.bvarLifts lvl').bvarLift

def LamTerm.bvarLifts_cast₁ {lvl : Nat} {rterm : LamTerm} (f : LamTerm → Sort u)
  (H : f (LamTerm.bvarLifts (LamTerm.bvarLift rterm) lvl)) :
  f (LamTerm.bvarLifts rterm (Nat.succ lvl)) :=
  match lvl with
  | 0 => H
  | lvl' + 1 => LamTerm.bvarLifts_cast₁ (rterm:=rterm) (f := fun t => f (t.bvarLift)) H

def LamTerm.bvarLifts_cast₂ {lvl : Nat} {rterm : LamTerm} (f : LamTerm → Sort u)
  (H : f (LamTerm.bvarLifts rterm (Nat.succ lvl))) :
  f (LamTerm.bvarLifts (LamTerm.bvarLift rterm) lvl) :=
  match lvl with
  | 0 => H
  | lvl' + 1 => LamTerm.bvarLifts_cast₂ (rterm:=rterm) (f := fun t => f (t.bvarLift)) H

def LamWF.ofBVarLiftIdx {lamVarTy lctx} (idx : Nat) (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨popLCtxAt lctx idx, rterm, rTy⟩) →
  LamWF lamVarTy ⟨lctx, rterm.bvarLiftIdx idx, rTy⟩
| .ofAtom n => .ofAtom n
| .ofBase b => .ofBase b
| .ofBVar n =>
  let H := @LamWF.ofBVar lamVarTy lctx (popLCtxAt id idx n)
  let castHg := fun i => LamWF lamVarTy ⟨lctx, LamTerm.bvar (popLCtxAt id idx n), i⟩
  popLCtxAt.comm_cast₁ id lctx castHg idx n H
| .ofLam (argTy:=argTy) (body:=body) bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (body:=body.bvarLiftIdx (Nat.succ idx))
    (LamWF.ofBVarLiftIdx (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.ofBVarLiftIdx idx _ HFn
  let IHArg := LamWF.ofBVarLiftIdx idx _ HArg
  .ofApp argTy' IHFn IHArg

def LamWF.ofBVarLift {lamVarTy lctx} (rterm : LamTerm) 
  (HWF : LamWF lamVarTy ⟨popLCtx lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm.bvarLift, rTy⟩ :=
  LamWF.ofBVarLiftIdx 0 rterm HWF

def LamWF.ofBVarLifts {lamVarTy lctx} (rterm : LamTerm) (lvl : Nat)
  (HWF : LamWF lamVarTy ⟨popLCtxs lctx lvl, rterm, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm.bvarLifts lvl, rTy⟩ :=
  match lvl with
  | 0 => HWF
  | lvl' + 1 =>
    let HWF' := LamWF.ofBVarLift rterm HWF
    let IH := LamWF.ofBVarLifts (LamTerm.bvarLift rterm) lvl' HWF'
    let castIH := fun t => LamWF lamVarTy ⟨lctx, t, rTy⟩
    LamTerm.bvarLifts_cast₁ castIH IH

def LamWF.fromBVarLiftIdx {lamVarTy} (idx : Nat) : {rTy : LamSort} →
  (rterm : LamTerm) → (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLiftIdx idx, rTy⟩) →
  LamWF lamVarTy ⟨popLCtxAt lctx idx, rterm, rTy⟩
| _, .atom n, .ofAtom _ => .ofAtom n
| _, .base _, .ofBase H => .ofBase H
| _, .bvar n, .ofBVar _ =>
  let H := @LamWF.ofBVar lamVarTy (popLCtxAt lctx idx) n
  let castHg := fun i => LamWF lamVarTy ⟨popLCtxAt lctx idx, LamTerm.bvar n, i⟩
  popLCtxAt.comm_cast₂ id lctx castHg idx n H
| _, .lam argTy body, .ofLam bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (LamWF.fromBVarLiftIdx (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| _, .app fn arg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.fromBVarLiftIdx idx _ HFn
  let IHArg := LamWF.fromBVarLiftIdx idx _ HArg
  .ofApp argTy' IHFn IHArg

def LamWF.fromBVarLift {lamVarTy} {rty : LamSort}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLift, rty⟩) :
  LamWF lamVarTy ⟨popLCtx lctx, rterm, rty⟩ :=
  LamWF.fromBVarLiftIdx 0 rterm HWF

def LamWF.fromBVarLifts {lamVarTy lctx} (rterm : LamTerm) (lvl : Nat)
  (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLifts lvl, argTy⟩) :
  LamWF lamVarTy ⟨popLCtxs lctx lvl, rterm, argTy⟩ :=
  match lvl with
  | 0 => HWF
  | lvl' + 1 =>
    let HWF' := LamWF.fromBVarLift (LamTerm.bvarLifts rterm lvl') HWF
    let IH := LamWF.fromBVarLifts _ _ HWF'
    let castIH := fun f =>
      LamWF lamVarTy ⟨f, rterm, argTy⟩
    popLCtx.succ_cast₁ _ castIH _ IH

-- **Note**: This is the `.bvar` case for the following `LamWF.subst`
-- The `LamWF` of the `ofBVar` we've just destructed is equivalent to
--   `argTy::(idx)→lctx ⊢ (.bvar n) : (argTy::(idx)→lctx)[n]`
-- The `wfArg` is equivalent to saying
--  `lctx[idx:] ⊢ arg : argTy`
-- Which can be turned into
--  `lctx ⊢ (bVarLifts arg idx) : (argTy::(idx)→lctx)[idx]`
-- What we want is
--   1. n < idx : `lctx ⊢ (.bvar n) : lctx[n]`
--   2. n = idx : `lctx ⊢ (bVarLifts arg idx) : argTy`
--   3. n = n' + 1 > idx : `lctx ⊢ (.bvar n') : lctx[n']`
-- It helps to think of `lctx ⊢ (.bvar n) : lctx[n]` as being bvar lifted
--   from `lctx ⊢ (.bvar 0) : lctx[0]`
-- The required type is
--   `lctx ⊢ substed : (argTy::(idx)→lctx)[n]`
-- The required definitional equalities are
--   1. n < idx          ::   lctx[n]  == (argTy::(idx)→lctx)[n]
--   2. n = idx          ::   argTy    == (argTy::(idx)→lctx)[n]
--   3. n = n' + 1 > idx ::   lctx[n'] == (argTy::(idx)→lctx)[n]
-- The term will be defined recursively. So we will have the following situation:
-- 1. n >= idx, requires
--    `lctx ⊢ substed : (argTy::(2)→lctx)[4]`     (idx, n, lctx) := (2, 4, pop 0)
--    given `LamWF.ofBVarLifts wfArg ::: lctx ⊢ (bVarLifts arg 2) : (argTy::(2)→lctx)[4]`
--  i.e.
--    `lctx ⊢ substed : (lctx[0]::lctx[1]::argTy::lctx[2:])[4]`  := (2, 4, pop 0)
--    given `_ ::: lctx ⊢ (bVarLifts arg 2) : (lctx[0]::lctx[1]::argTy::lctx[2:])[4]`
--  This can be bvar lifted from
--    `lctx[1:] ⊢ substed : (lctx[1]::argTy::lctx[2:])[3]`       := (1, 3, pop 1)
--    given `_ ::: lctx[1:] ⊢ (bVarLifts arg 1) : (lctx[1]::argTy::lctx[2:])[3]`
--  This can in turn be bvar lifted from
--    `lctx[2:] ⊢ substed : (argTy::lctx[2:])[2]`                := (0, `n` = 2, pop 2)
--    given `_ ::: lctx[2:] ⊢ arg : (argTy::lctx[2:])[2]`
--  At this point, we should do `cases` on `n`.
--    (1). If `n = 0`, we should use `substed := arg`
--    (2). if `n = n' + 1`, we should use `substed := (.bvar n')`
-- 2. n < idx, requires
--    `lctx ⊢ substed : (argTy::(4)→lctx)[2]`     (idx, n, lctx) := (4, 2, pop 0)
--  i.e                                                          := (4, 2, pop 0)
--    `lctx ⊢ substed : (lctx[0]::lctx[1]::lctx[2]::lctx[3]::argTy::lctx[4:])[2]`
--  This can be bvar lifted from                                 := (3, 1, pop 1)
--    `lctx[1:] ⊢ substed : (lctx[1]::lctx[2]::lctx[3]::argTy::lctx[4:])[1]`
--  This can in turn be bvar lifted from                         := (`idx'` = 2, 0, pop 2)
--    `lctx[2:] ⊢ substed : (lctx[2]::lctx[3]::argTy::lctx[4])[0]`
--  At this point, it's clear that `substed := (.bvar 0)`
-- **TODO**: Can this function be represented by `pushLCtxDep`?
--           Furthermore, can other functions be represented by `pushLCtxDep`?
private def LamWF.subst_bvarAux
  {ltv : LamTyVal} {lctx : Nat → LamSort} {argTy : LamSort}
  (arg : LamTerm) (pops : Nat) : (idx : Nat) → (n : Nat) →
  (wfArg : LamWF ltv ⟨popLCtxs lctx pops, arg.bvarLifts idx, argTy⟩) → 
  (substed : LamTerm) × LamWF ltv ⟨(popLCtxs lctx pops), substed, pushLCtxAt (popLCtxs lctx pops) argTy idx n⟩
  | 0 => fun n =>
    match n with
    | 0 => fun wfArg =>
      ⟨arg, wfArg⟩
    | n' + 1 => fun wfArg =>
      ⟨.bvar n', .ofBVar _⟩
  | idx' + 1 => fun n =>
    match n with
    | 0 => fun wfArg =>
      ⟨.bvar 0, .ofBVar _⟩
    | n' + 1 => fun wfArg =>
      let wfArg' : LamWF ltv _ :=
        LamWF.fromBVarLift (lctx:=popLCtxs lctx pops) _ wfArg
      let IH := LamWF.subst_bvarAux arg (Nat.succ pops) idx' n' wfArg'
      ⟨IH.fst.bvarLift, LamWF.ofBVarLift _ IH.snd⟩

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we beta-reduce the whole term
-- `bj` is the judgement related to the body, i.e. `lctx ⊢ body : ty`. It's
--   easy to see that the `lctx` which `arg` resides in is `popLCtxs lctx (idx + 1)`
--   and the type of `arg` is `lctx idx`
def LamWF.subst (ltv : LamTyVal) (idx : Nat)
  (arg : LamTerm) (argTy : LamSort)
  (body : LamTerm) (bodyTy : LamSort) :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF ltv ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩) →
  (wfBody : LamWF ltv ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) →
  (substed : LamTerm) × LamWF ltv ⟨lctx, substed, bodyTy⟩
| lctx, _,     .ofAtom n => ⟨.atom n, .ofAtom _⟩
| lctx, _,     .ofBase (b:=b) H => ⟨.base b, .ofBase H⟩
| lctx, wfArg, .ofBVar n => LamWF.subst_bvarAux arg 0 idx n wfArg
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLift (lctx:=pushLCtx lctx argTy') _ wfArg
  let IHArg := LamWF.subst ltv (Nat.succ idx) _ _ _ _ _ wfArg' H
  ⟨.lam argTy' IHArg.fst, .ofLam _ IHArg.snd⟩
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.subst ltv idx _ _ _ _ _ wfArg HFn
  let IHArg := LamWF.subst ltv idx _ _ _ _ _ wfArg HArg
  ⟨.app IHFn.fst IHArg.fst, .ofApp argTy' IHFn.snd IHArg.snd⟩

def LamWF.subst_correct.{u} (lval : LamValuation.{u})
  (arg : LamTerm) (argTy : LamSort)
  (body : LamTerm) (bodyTy : LamSort) (idx : Nat) :
  (lctxTy : Nat → LamSort) →
  (lctxTerm : ∀ n, (lctxTy n).interp lval.ilVal.tyVal) →
  (wfArg : LamWF lval.ilVal.toLamTyVal ⟨lctxTy, LamTerm.bvarLifts arg idx, argTy⟩) →
  (wfBody : LamWF lval.ilVal.toLamTyVal ⟨pushLCtxAt lctxTy argTy idx, body, bodyTy⟩) →
  let wfSubst := LamWF.subst lval.ilVal.toLamTyVal idx arg argTy body bodyTy lctxTy wfArg wfBody
  (LamTerm.interp lval (pushLCtxAt lctxTy argTy idx)
    (pushLCtxAtDep lctxTerm (LamTerm.interp lval lctxTy lctxTerm wfArg) idx) wfBody
  = LamTerm.interp lval lctxTy lctxTerm wfSubst.snd)
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBase b => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n => by simp [subst, LamTerm.interp]; sorry
  -- This seems to be implying that
  -- 1. We should state a commutativity theorem about `pushLCtxAtDep`
  -- 1. `LamWF.subst_bvarAux` should be expressed by `pushLCtxAtDep`
| lctxTy, lctxTerm, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  sorry
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  sorry

end Auto.Embedding.Lam