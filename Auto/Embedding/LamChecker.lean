import Auto.Embedding.LamConv
import Auto.Lib.BinTree

namespace Auto.Embedding.Lam

-- Table of valid propositions and well-formed formulas
-- Note that `Auto.BinList α` is equivalent to `Nat → Option α`,
--   which means that `.some` entries may be interspersed
--   with `.none` entries
structure RTable where
  -- Well-formed formulas, with types
  -- We do not import well-formedness facts because
  --   we have `LamWF.ofLamCheck?`
  wf    : Auto.BinList (List LamSort × LamSort × LamTerm)
  -- Valid propositions
  -- The initial formulas in the `valid` table will be
  --   imported from `ImportTable`
  valid : Auto.BinList (List LamSort × LamTerm)

-- An entry of RTable
inductive REntry where
  | none    : REntry
  | wf      : List LamSort → LamSort → LamTerm → REntry
  | valid   : List LamSort → LamTerm → REntry

def REntry.correct (lval : LamValuation.{u}) : REntry → Prop
| .none => True
| .wf lctx s t => LamThmWFP lval lctx s t
| .valid lctx t => LamThmValid lval lctx t

def RTable.addEntry (r : RTable) (n : Nat) : REntry → RTable
| .none         => r
| .wf lctx s t  => ⟨r.wf.insert n ⟨lctx, s, t⟩, r.valid⟩
| .valid lctx t => ⟨r.wf, r.valid.insert n ⟨lctx, t⟩⟩

-- Invariant of `wf`
def RTable.wfInv
  (lval : LamValuation.{u})
  (wf : BinList (List LamSort × LamSort × LamTerm)) :=
  wf.allp (fun ⟨lctx, rty, t⟩ => LamThmWFP lval lctx rty t)

theorem RTable.wfInv_get
  {wf : BinList _} (inv : RTable.wfInv lval wf)
  (h : BinList.get? wf n = Option.some val) :
  LamThmWF lval val.fst val.snd.fst val.snd.snd := by
  have inv' := inv n; rw [h] at inv'; exact LamThmWF.ofLamThmWFP inv'

-- Invariant of `valid
def RTable.validInv
  (lval : LamValuation.{u})
  (valid : Auto.BinList (List LamSort × LamTerm)) :=
  valid.allp (fun ⟨lctx, t⟩ => LamThmValid lval lctx t)

theorem RTable.validInv_get
  {valid : BinList _} (inv : RTable.validInv lval valid)
  (h : BinList.get? valid n = Option.some val) :
  LamThmValid lval val.fst val.snd := by
  have inv' := inv n; rw [h] at inv'; exact inv'

-- Invariant of `RTable`
def RTable.inv (lval : LamValuation.{u}) (r : RTable) :=
  wfInv lval r.wf ∧ validInv lval r.valid

-- The meta code of the checker will prepare this `ImportTable`
abbrev ImportTable (lval : LamValuation.{u}) :=
  Auto.BinList (@PSigma LamTerm (fun p => (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down))

-- Used by the meta code of the checker to build `ImportTable`
abbrev importTablePSigmaβ (lval : LamValuation.{u}) (p : LamTerm) :=
  (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down

abbrev importTablePSigmaMk (lval : LamValuation.{u}) :=
  @PSigma.mk LamTerm (importTablePSigmaβ lval)

abbrev importTablePSigmaDefault (lval : LamValuation.{u}) :
  @PSigma LamTerm (fun p => (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down) :=
  ⟨.base .trueE, True.intro⟩

def ImportTable.importFacts (it : ImportTable lval) : BinList (List LamSort × LamTerm) :=
  it.mapOpt (fun ⟨p, _⟩ =>
    match p.lamCheck? lval.ilVal.toLamTyVal dfLCtxTy with
    | .some (.base .prop) =>
      match p.maxLooseBVarSucc with
      | 0 => .some ([], p)
      | _ + 1 => .none
    | _                   => .none)

theorem ImportTable.importFacts_correct (it : ImportTable lval) :
  RTable.validInv lval (importFacts it) := by
  dsimp [RTable.validInv, importFacts]; rw [BinList.mapOpt_allp]
  intro n; apply Option.allp_uniform;
  intro ⟨p, validp⟩; dsimp
  cases h₁ : LamTerm.lamCheck? lval.ilVal.toLamTyVal dfLCtxTy p <;> try exact True.intro
  case a.some s =>
    cases s <;> try exact True.intro
    case base b =>
      cases b <;> try exact True.intro
      dsimp
      cases h₂ : p.maxLooseBVarSucc <;> try exact True.intro
      dsimp [Option.allp]
      apply LamThmValid.ofInterpAsProp _ _ h₁ validp h₂    

inductive ChkStep where
  -- Adds `⟨lctx, t, t.lamCheck!⟩` to `rtable.wf`
  | nop : ChkStep
  | wfOfCheck (lctx : List LamSort) (t : LamTerm) : ChkStep
  | wfOfAppend (ex : List LamSort) (wPos : Nat) : ChkStep
  | wfOfPrepend (ex : List LamSort) (wPos : Nat) : ChkStep
  | wfOfHeadBeta (wPos : Nat) : ChkStep
  | validOfResolveImport (vPos : Nat) : ChkStep
  | validOfHeadBeta (vPos : Nat) : ChkStep
  deriving Lean.ToExpr

def ChkStep.eval (ltv : LamTyVal) (r : RTable) : (cs : ChkStep) → REntry
| .nop => .none
| .wfOfCheck lctx t =>
  match LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t with
  | .some rty =>
    match Nat.ble (t.maxLooseBVarSucc) (lctx.length) with
    | true  => .wf lctx rty t
    | false => .none
  | .none => .none
| .wfOfAppend ex wPos =>
  match r.wf.get? wPos with
  | .some ⟨lctx, s, t⟩ => .wf (lctx ++ ex) s t
  | .none => .none
| .wfOfPrepend ex wPos =>
  match r.wf.get? wPos with
  | .some ⟨lctx, s, t⟩ => .wf (ex ++ lctx) s (t.bvarLifts ex.length)
  | .none => .none
| .wfOfHeadBeta wPos =>
  match r.wf.get? wPos with
  | .some ⟨lctx, s, t⟩ => .wf lctx s t.headBeta
  | .none => .none
| .validOfResolveImport vPos =>
  match r.valid.get? vPos with
  | .some ⟨lctx, t⟩ => .valid lctx (t.resolveImport ltv)
  | .none => .none
| .validOfHeadBeta vPos =>
  match r.valid.get? vPos with
  | .some ⟨lctx, t⟩ => .valid lctx t.headBeta
  | .none => .none

theorem ChkStep.eval_correct
  (lval : LamValuation.{u}) (r : RTable) (inv : r.inv lval) :
  (cs : ChkStep) → REntry.correct lval (cs.eval lval.ilVal.toLamTyVal r)
| .nop => True.intro
| .wfOfCheck lctx t => by
  dsimp [eval]
  cases h₁ : LamTerm.lamCheck? lval.ilVal.toLamTyVal (pushLCtxs lctx dfLCtxTy) t <;> try exact True.intro
  case some s =>
    cases h₂ : Nat.ble (LamTerm.maxLooseBVarSucc t) (List.length lctx) <;> try exact True.intro
    dsimp [REntry.correct]; apply LamThmWFP.ofLamThmWF
    exact LamThmWF.ofLamCheck? h₁ (Nat.le_of_ble_eq_true h₂)
| .wfOfAppend ex wPos => by
  dsimp [eval]
  cases h : BinList.get? r.wf wPos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.append (RTable.wfInv_get inv.left h)
| .wfOfPrepend ex wPos => by
  dsimp [eval]
  cases h : BinList.get? r.wf wPos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.prepend (RTable.wfInv_get inv.left h)
| .wfOfHeadBeta wPos => by
  dsimp [eval]
  cases h : BinList.get? r.wf wPos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.headBeta (RTable.wfInv_get inv.left h)
| .validOfResolveImport vPos => by
  dsimp [eval]
  cases h : BinList.get? r.valid vPos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      apply LamThmValid.resolveImport (RTable.validInv_get inv.right h)
| .validOfHeadBeta vPos => by
  dsimp [eval]
  cases h : BinList.get? r.valid vPos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      apply LamThmValid.headBeta (RTable.validInv_get inv.right h)

-- The first `ChkStep` specifies the checker step
-- The second `Nat` specifies the position to insert the resulting term
-- Note that
--   1. All entries `(x : ChkStep × Nat)` that insert result into the
--      `wf` table should have distinct second component
--   2. All entries `(x : ChkStep × Nat)` that insert result into the
--      `valid` table should have distinct second component
-- Note that we decide where (`wf` or `valid`) to insert the resulting
--   term by looking at `(c : ChkStep).eval`
abbrev ChkSteps := BinList (ChkStep × Nat)

def ChkStep.run (ltv : LamTyVal) (r : RTable) (c : ChkStep) (n : Nat) : RTable :=
  match ChkStep.eval ltv r c with
  | .none => r
  | .wf lctx s t => ⟨r.wf.insert n (lctx, s, t), r.valid⟩
  | .valid lctx t => ⟨r.wf, r.valid.insert n (lctx, t)⟩

theorem ChkStep.run_correct
  (lval : LamValuation.{u}) (r : RTable) (inv : r.inv lval) (c : ChkStep) (n : Nat) :
  (ChkStep.run lval.ilVal.toLamTyVal r c n).inv lval := by
  dsimp [ChkStep.run]
  have eval_correct := ChkStep.eval_correct lval r inv c; revert eval_correct
  cases h : eval lval.ilVal.toLamTyVal r c <;> intro eval_correct
  case none => exact inv
  case wf lctx s t =>
    apply And.intro
    case left =>
      dsimp [RTable.wfInv]; rw [BinList.allp_insert]; dsimp
      apply And.intro
      case left => exact eval_correct
      case right => intros; apply inv.left
    case right =>
      exact inv.right
  case valid lctx t =>
    apply And.intro <;> dsimp
    case left => exact inv.left
    case right =>
      dsimp [RTable.validInv]; rw [BinList.allp_insert]; dsimp
      apply And.intro
      case left => exact eval_correct
      case right => intros; apply inv.right

def ChkSteps.run (ltv : LamTyVal) (r : RTable) (cs : ChkSteps) : RTable :=
  BinList.foldl (fun r (c, n) => ChkStep.run ltv r c n) r cs

theorem CheckSteps.run_correct
  (lval : LamValuation.{u}) (r : RTable) (inv : r.inv lval) (cs : ChkSteps) :
  (ChkSteps.run lval.ilVal.toLamTyVal r cs).inv lval := by
  dsimp [ChkSteps.run]; apply BinList.foldl_inv (RTable.inv lval) inv
  intro r (c, n) inv'; exact ChkStep.run_correct lval r inv' c n

theorem Checker
  (lval : LamValuation.{u}) (it : ImportTable lval) (cs : ChkSteps) :
  (ChkSteps.run lval.ilVal.toLamTyVal ⟨.empty, it.importFacts⟩ cs).inv lval := by
  apply CheckSteps.run_correct; apply And.intro;
  case left =>
    intro n; cases n <;> dsimp [BinList.get?]
    case zero => exact True.intro
    case succ n => dsimp [BinList.empty]; rw [BinTree.get?_leaf]; exact True.intro
  case right => apply ImportTable.importFacts_correct

end Auto.Embedding.Lam