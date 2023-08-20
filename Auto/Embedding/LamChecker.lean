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
  --   we have `LamWF.ofCheck?`
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

def RTable.addEntry (r : RTable) (n : Nat) : REntry → RTable
| .none         => r
| .wf lctx s t  => ⟨r.wf.insert n ⟨lctx, s, t⟩, r.valid⟩
| .valid lctx t => ⟨r.wf, r.valid.insert n ⟨lctx, t⟩⟩

-- Invariant of `wf`
def RTable.wfInv
  (lval : LamValuation.{u})
  (wf : Auto.BinList (List LamSort × LamSort × LamTerm)) :=
  wf.allp (fun ⟨lctx, rty, t⟩ => LamThmWF' lval lctx rty t)

-- Invariant of `valid
def RTable.validInv
  (lval : LamValuation.{u})
  (valid : Auto.BinList (List LamSort × LamTerm)) :=
  valid.allp (fun ⟨lctx, t⟩ => LamThmValid lval lctx t)

-- Invariant of `RTable`
def RTable.inv (lval : LamValuation.{u}) (r : RTable) :=
  wfInv lval r.wf ∧ validInv lval r.valid

-- The meta code of the checker will prepare this `ImportTable`
abbrev ImportTable (lval : LamValuation.{u}) :=
  Auto.BinList (@PSigma LamTerm (fun p => (LamTerm.interpAsProp lval dfLCtxTy (dfLCtxTerm _) p).down))

def RTable.importFacts (it : ImportTable lval) : BinList (List LamSort × LamTerm) :=
  it.mapOpt (fun ⟨p, _⟩ =>
    match p.lamCheck? lval.ilVal.toLamTyVal dfLCtxTy with
    | .some (.base .prop) =>
      match p.maxLooseBVarSucc with
      | 0 => .some ([], p)
      | _ + 1 => .none
    | _                   => .none)

theorem RTable.import_correct (it : ImportTable lval) :
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
  | wfOfCheck (lctx : List LamSort) (t : LamTerm) : ChkStep

def ChkStep.eval (ltv : LamTyVal) (r : RTable) : (cs : ChkStep) → REntry
| .wfOfCheck lctx t =>
  match LamTerm.lamCheck? ltv (pushLCtxs lctx dfLCtxTy) t with
  | .some rty =>
    match Nat.ble (t.maxLooseBVarSucc) (lctx.length) with
    | true  => .wf lctx rty t
    | false => .none
  | .none => .none

end Auto.Embedding.Lam