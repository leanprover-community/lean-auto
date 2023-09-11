import Auto.Embedding.LamConv
import Auto.Lib.BinTree

namespace Auto.Embedding.Lam

-- An entry of RTable
inductive REntry where
  -- Well-formed formulas, with types
  -- We do not import well-formedness facts because
  --   we have `LamWF.ofLamCheck?`
  | wf        : List LamSort → LamSort → LamTerm → REntry
  -- Valid propositions
  -- The initial formulas in the `valid` table will be
  --   imported from `ImportTable`
  | valid     : List LamSort → LamTerm → REntry
  | nonempty : LamSort → REntry
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

def REntry.repr : REntry → String
| .wf ss s t => s!"Auto.Embedding.Lam.REntry.wf {reprPrec ss 1} {reprPrec s 1} {reprPrec t 1}"
| .valid ss t => s!"Auto.Embedding.Lam.REntry.valid {reprPrec ss 1} {reprPrec t 1}"
| .nonempty s => s!"Audo.Embedding.Lam.REntry.nonempty {reprPrec s 1}"

instance : Repr REntry where
  reprPrec := fun re _ => re.repr

def REntry.toString : REntry → String
| .wf ss s t => s!"wf {ss} {s} {t}"
| .valid ss t => s!"valid {ss} {t}"
| .nonempty s => s!"nonempty {s}"

instance : ToString REntry where
  toString := REntry.toString

-- Table of valid propositions and well-formed formulas
-- Note that `Auto.BinTree α` is equivalent to `Nat → Option α`,
--   which means that `.some` entries may be interspersed
--   with `.none` entries
abbrev RTable := Auto.BinTree REntry

def RTable.addEntry (r : RTable) (n : Nat) (re : REntry) : RTable :=
  r.insert n re

section CheckerValuation

  structure CheckerValuation where
    tyVal : Nat → Type u
    var   : BinTree ((s : LamSort) × (s.interp tyVal))
    il    : BinTree ((s : LamSort) × (ILLift.{u} (s.interp tyVal)))
  
  -- Used in checker metacode to construct `var`
  abbrev varSigmaMk.{u} (tyVal : Nat → Type u) :=
    @Sigma.mk LamSort (LamSort.interp tyVal)
  
  -- Used in checker metacode to construct `il`
  abbrev ilSigmaβ.{u} (tyVal : Nat → Type u) (s : LamSort) : Type u :=
    ILLift.{u} (s.interp tyVal)
  
  -- Used in checker metacode to construct `il`
  abbrev ilSigmaMk.{u} (tyVal : Nat → Type u) :=
    @Sigma.mk LamSort (ilSigmaβ.{u} tyVal)
  
  def ilVal.default (lamILTy : Nat → LamSort) (tyVal : Nat → Type u) :
    ∀ (n : Nat), ILLift.{u} ((lamILTy n).interp tyVal) :=
    fun n => ILLift.default ((lamILTy n).interp tyVal)

  def CheckerValuation.toLamTyVal (cv : CheckerValuation.{u}) : LamTyVal :=
    ⟨fun n => ((cv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).fst,
     fun n => ((cv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).fst⟩
  
  def CheckerValuation.toLamValuation (cv : CheckerValuation.{u}) : LamValuation :=
    ⟨cv.toLamTyVal, cv.tyVal,
     fun n => ((cv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).snd,
     fun n => ((cv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).snd⟩

end CheckerValuation

def REntry.correct (lval : CheckerValuation.{u}) : REntry → Prop
| .wf lctx s t => LamThmWFP lval.toLamValuation lctx s t
| .valid lctx t => LamThmValid lval.toLamValuation lctx t
| .nonempty s => LamNonempty lval.tyVal s

-- Invariant of `RTable`
def RTable.inv (lval : CheckerValuation.{u}) (r : RTable) :=
  r.allp (fun re => re.correct lval)

theorem RTable.wfInv_get
  {r : RTable} (inv : RTable.inv lval r) (h : BinTree.get? r n = Option.some (.wf lctx s t)) :
  LamThmWF lval.toLamValuation lctx s t := by
  have inv' := inv n; rw [h] at inv'; exact LamThmWF.ofLamThmWFP inv'

theorem RTable.validInv_get
  {r : RTable} (inv : RTable.inv lval r) (h : BinTree.get? r n = Option.some (.valid lctx t)) :
  LamThmValid lval.toLamValuation lctx t := by
  have inv' := inv n; rw [h] at inv'; exact inv'

theorem RTable.nonemptyInv_get
  {r : RTable} (inv : RTable.inv lval r) (h : BinTree.get? r n = Option.some (.nonempty s)) :
  LamNonempty lval.tyVal s := by
  have inv' := inv n; rw [h] at inv'; exact inv'

def RTable.getWF (r : RTable) (v : Nat) : Option (List LamSort × LamSort × LamTerm) :=
  match r.get? v with
  | .some (.valid _ _ ) => .none
  | .some (.wf lctx s t) => .some (lctx, s, t)
  | .some (.nonempty _) => .none
  | .none => .none

theorem RTable.getWF_correct
  (inv : RTable.inv lval r) (heq : getWF r v = .some (lctx, s, t)) :
  LamThmWF lval.toLamValuation lctx s t := by
  revert heq; dsimp [getWF]
  match h : BinTree.get? r v with
  | .some (.valid lctx t) => intro heq; cases heq
  | .some (.wf _ _ _) => intro heq; cases heq; apply RTable.wfInv_get inv h
  | .some (.nonempty _) => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValid (r : RTable) (v : Nat) : Option (List LamSort × LamTerm) :=
  match r.get? v with
  | .some (.valid lctx t) => .some (lctx, t)
  | .some (.wf _ _ _) => .none
  | .some (.nonempty _) => .none
  | .none => .none

theorem RTable.getValid_correct
  (inv : RTable.inv lval r) (heq : getValid r v = .some (lctx, t)) :
  LamThmValid lval.toLamValuation lctx t := by
  revert heq; dsimp [getValid]
  match h : BinTree.get? r v with
  | .some (.valid lctx t) => intro heq; cases heq; apply RTable.validInv_get inv h
  | .some (.wf _ _ _) => intro heq; cases heq
  | .some (.nonempty _) => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValidEnsureLCtx (r : RTable) (lctx : List LamSort) (v : Nat) : Option LamTerm :=
  match r.get? v with
  | .some (.valid lctx' t) =>
    match lctx.beq lctx' with
    | true => .some t
    | false => .none
  | .some (.wf _ _ _) => .none
  | .some (.nonempty _) => .none
  | .none => .none

theorem RTable.getValidEnsureLCtx_correct
  (inv : RTable.inv lval r) (heq : getValidEnsureLCtx r lctx v = .some t) :
  LamThmValid lval.toLamValuation lctx t := by
  revert heq; dsimp [getValidEnsureLCtx]
  match hv : BinTree.get? r v with
  | .some (.valid lctx' t) =>
    dsimp
    match hlctx : lctx.beq lctx' with
    | true =>
      intro heq; cases heq; cases (List.beq_eq LamSort.beq_eq _ _ hlctx)
      apply RTable.validInv_get inv hv
    | false => intro heq; cases heq
  | .some (.wf _ _ _) => intro heq; cases heq
  | .some (.nonempty _) => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValidsEnsureLCtx (r : RTable) (lctx : List LamSort) (vs : List Nat) : Option (List LamTerm) :=
  match vs with
  | .nil => .some .nil
  | .cons v vs =>
    match r.get? v with
    | .some (.valid lctx' t) =>
      match lctx.beq lctx' with
      | true => List.cons t <$> getValidsEnsureLCtx r lctx vs
      | false => .none
    | .some (.wf _ _ _) => .none
    | .some (.nonempty _) => .none
    | .none => .none

theorem RTable.getValidsEnsureLCtx_correct
  (inv : RTable.inv lval r) (heq : getValidsEnsureLCtx r lctx vs = .some ts) :
  HList (fun t => LamThmValid lval.toLamValuation lctx t) ts := by
  revert ts; induction vs <;> intro ts heq
  case nil =>
    cases heq; apply HList.nil
  case cons v vs IH =>
    dsimp [getValidsEnsureLCtx] at heq; revert heq
    match hv : BinTree.get? r v with
    | .some (.valid lctx' t) =>
      dsimp
      match hlctx : lctx.beq lctx' with
      | true =>
        dsimp; cases (List.beq_eq LamSort.beq_eq _ _ hlctx)
        match hvs : getValidsEnsureLCtx r lctx vs with
        | .some ts' =>
          intro heq; cases heq
          apply HList.cons (RTable.validInv_get inv hv)
          apply IH hvs;
        | .none => intro heq; cases heq
      | false => intro heq; cases heq
    | .some (.wf _ _ _) => intro heq; cases heq
    | .some (.nonempty _) => intro heq; cases heq
    | .none => intro heq; cases heq

-- The meta code of the checker will prepare this `ImportTable`
abbrev ImportTable (lval : CheckerValuation.{u}) :=
  Auto.BinTree (@PSigma LamTerm (fun p => (LamTerm.interpAsProp lval.toLamValuation dfLCtxTy (dfLCtxTerm _) p).down))

-- Used by the meta code of the checker to build `ImportTable`
abbrev importTablePSigmaβ (lval : CheckerValuation.{u}) (p : LamTerm) :=
  (LamTerm.interpAsProp lval.toLamValuation dfLCtxTy (dfLCtxTerm _) p).down

abbrev importTablePSigmaMk (lval : CheckerValuation.{u}) :=
  @PSigma.mk LamTerm (importTablePSigmaβ lval)

abbrev importTablePSigmaDefault (lval : CheckerValuation.{u}) :
  @PSigma LamTerm (fun p => (LamTerm.interpAsProp lval.toLamValuation dfLCtxTy (dfLCtxTerm _) p).down) :=
  ⟨.base .trueE, True.intro⟩

def ImportTable.importFacts (it : ImportTable lval) : RTable :=
  it.mapOpt (fun ⟨p, _⟩ =>
    match p.lamCheck? lval.toLamTyVal dfLCtxTy with
    | .some (.base .prop) =>
      match p.maxLooseBVarSucc with
      | 0 => .some (.valid [] (p.resolveImport lval.toLamTyVal))
      | _ + 1 => .none
    | _                   => .none)

theorem ImportTable.importFacts_correct (it : ImportTable lval) :
  RTable.inv lval (importFacts it) := by
  dsimp [RTable.inv, importFacts]; rw [BinTree.mapOpt_allp]
  intro n; apply Option.allp_uniform;
  intro ⟨p, validp⟩; dsimp
  cases h₁ : LamTerm.lamCheck? lval.toLamTyVal dfLCtxTy p <;> try exact True.intro
  case a.some s =>
    cases s <;> try exact True.intro
    case base b =>
      cases b <;> try exact True.intro
      dsimp
      cases h₂ : p.maxLooseBVarSucc <;> try exact True.intro
      dsimp [Option.allp]
      apply LamThmValid.resolveImport
      apply LamThmValid.ofInterpAsProp lval.toLamValuation _ h₁ validp h₂    

inductive ChkStep where
  -- Adds `⟨lctx, t, t.lamCheck!⟩` to `rtable.wf`
  | nop : ChkStep
  | wfOfCheck (lctx : List LamSort) (t : LamTerm) : ChkStep
  | wfOfAppend (ex : List LamSort) (pos : Nat) : ChkStep
  | wfOfPrepend (ex : List LamSort) (pos : Nat) : ChkStep
  | wfOfHeadBeta (pos : Nat) : ChkStep
  | wfOfBetaBounded (pos : Nat) (bound : Nat) : ChkStep
  | validOfIntro1F (pos : Nat) : ChkStep
  | validOfIntro1H (pos : Nat) : ChkStep
  | validOfIntros (pos idx : Nat) : ChkStep
  | validOfHeadBeta (pos : Nat) : ChkStep
  | validOfBetaBounded (pos : Nat) (bound : Nat) : ChkStep
  -- `t₁ → t₂` and `t₁` implies `t₂`
  | validOfImp (p₁₂ : Nat) (p₁ : Nat) : ChkStep
  -- `t₁ → t₂ → ⋯ → tₖ → s` and `t₁, t₂, ⋯, tₖ` implies `s`
  | validOfImps (imp : Nat) (ps : List Nat) : ChkStep
  | validOfInstantiate1 (pos : Nat) (arg : LamTerm) : ChkStep
  | validOfInstantiate (pos : Nat) (args : List LamTerm) : ChkStep
  | validOfInstantiateRev (pos : Nat) (args : List LamTerm) : ChkStep
  | validOfCongrArg (pos rw : Nat) : ChkStep
  | validOfCongrFun (pos rw : Nat) : ChkStep
  | validOfCongr (pos rwFn rwArg : Nat) : ChkStep
  | validOfCongrArgs (pos : Nat) (rws : List Nat)
  | validOfCongrFunN (pos rwFn n : Nat) : ChkStep
  | validOfCongrs (pos rwFn : Nat) (rwArgs : List Nat) : ChkStep
  deriving Lean.ToExpr

def ChkStep.toString : ChkStep → String
| .nop => s!"nop"
| .wfOfCheck lctx t => s!"wfOfCheck {lctx} {t}"
| .wfOfAppend ex pos => s!"wfOfAppend {ex} {pos}"
| .wfOfPrepend ex pos => s!"wfOfPrepend {ex} {pos}"
| .wfOfHeadBeta pos => s!"wfOfHeadBeta {pos}"
| .wfOfBetaBounded pos bound => s!"wfOfBetaBounded {pos} {bound}"
| .validOfIntro1F pos => s!"validOfIntro1F {pos}"
| .validOfIntro1H pos => s!"validOfIntro1H {pos}"
| .validOfIntros pos idx => s!"validOfIntros {pos} {idx}"
| .validOfHeadBeta pos => s!"validOfHeadBeta {pos}"
| .validOfBetaBounded pos bound => s!"validOfBetaBounded {pos} {bound}"
| .validOfImp p₁₂ p₁ => s!"validOfImp {p₁₂} {p₁}"
| .validOfImps imp ps => s!"validOfImps {imp} {ps}"
| .validOfInstantiate1 pos arg => s!"validOfInstantiate1 {pos} {arg}"
| .validOfInstantiate pos args => s!"validOfInstantiate {pos} {args}"
| .validOfInstantiateRev pos args => s!"validOfInstantiateRev {pos} {args}"
| .validOfCongrArg pos rw => s!"validOfCongrArg {pos} {rw}"
| .validOfCongrFun pos rw => s!"validOfCongrFun {pos} {rw}"
| .validOfCongr pos rwFn rwArg => s!"validOfCongr {pos} {rwFn} {rwArg}"
| .validOfCongrArgs pos rws => s!"validOfCongrArgs {pos} {rws}"
| .validOfCongrFunN pos rwFn n => s!"validOfCongrFunN {pos} {rwFn} {n}"
| .validOfCongrs pos rwFn rwArgs => s!"validOfCongrs {pos} {rwFn} {rwArgs}"

instance : ToString ChkStep where
  toString := ChkStep.toString

def ChkStep.evalValidOfIntros (lctx : List LamSort) (t : LamTerm)
  : (idx : Nat) → Option REntry
  | 0 => .some (.valid lctx t)
  | .succ idx =>
    match t.intro1? with
    | .some (s, t') => evalValidOfIntros (s :: lctx) t' idx
    | .none => .none

def ChkStep.evalValidOfInstantiate (ltv : LamTyVal) (lctx : List LamSort) (t : LamTerm)
  : (args : List LamTerm) → Option REntry
  | .nil => .some (.valid lctx t)
  | .cons arg args =>
    match lctx with
    | .nil => .none
    | .cons argTy lctx =>
      match arg.lamThmWFCheck? ltv lctx with
      | .some s =>
        match s.beq argTy with
        | true => evalValidOfInstantiate ltv lctx (LamTerm.instantiate1 arg t) args
        | false => .none
      | .none => .none

def ChkStep.eval (ltv : LamTyVal) (r : RTable) : (cs : ChkStep) → Option REntry
| .nop => .none
| .wfOfCheck lctx t =>
  match LamTerm.lamThmWFCheck? ltv lctx t with
  | .some rty => .some (.wf lctx rty t)
  | .none => .none
| .wfOfAppend ex pos =>
  match r.getWF pos with
  | .some (lctx, s, t) => .some (.wf (lctx ++ ex) s t)
  | .none => .none
| .wfOfPrepend ex pos =>
  match r.getWF pos with
  | .some (lctx, s, t) => .some (.wf (ex ++ lctx) s (t.bvarLifts ex.length))
  | .none => .none
| .wfOfHeadBeta pos =>
  match r.getWF pos with
  | .some (lctx, s, t) => .some (.wf lctx s t.headBeta)
  | .none => .none
| .wfOfBetaBounded pos bound =>
  match r.getWF pos with
  | .some (lctx, s, t) => .some (.wf lctx s (t.betaBounded bound))
  | .none => .none
| .validOfIntro1F pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match t.intro1F? with
    | .some (s, p) => .some (.valid (s :: lctx) p)
    | .none => .none
  | .none => .none
| .validOfIntro1H pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match t.intro1H? with
    | .some (s, p) => .some (.valid (s :: lctx) p)
    | .none => .none
  | .none => .none
| .validOfIntros pos idx =>
  match r.getValid pos with
  | .some (lctx, t) => evalValidOfIntros lctx t idx
  | .none => .none
| .validOfHeadBeta pos =>
  match r.getValid pos with
  | .some (lctx, t) => .some (.valid lctx t.headBeta)
  | .none => .none
| .validOfBetaBounded pos bound =>
  match r.getValid pos with
  | .some (lctx, t) => .some (.valid lctx (t.betaBounded bound))
  | .none => .none
| .validOfImp p₁₂ p₁ =>
  match r.getValid p₁₂ with
  | .some (lctx, t₁₂) =>
    match r.getValidEnsureLCtx lctx p₁ with
    | .some t₁ =>
      match LamTerm.impApp? t₁₂ t₁ with
      | .some t₂ => .some (.valid lctx t₂)
      | .none => .none
    | .none => .none
  | .none => .none
| .validOfImps imp ps =>
  match r.getValid imp with
  | .some (lctx, t) =>
    match r.getValidsEnsureLCtx lctx ps with
    | .some ts => REntry.valid lctx <$> t.impApps? ts
    | .none => .none
  | .none => .none
| .validOfInstantiate1 pos arg =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match lctx with
    | .nil => .none
    | .cons argTy lctx =>
      match arg.lamThmWFCheck? ltv lctx with
      | .some s =>
        match s.beq argTy with
        | true => .some (.valid lctx (LamTerm.instantiate1 arg t))
        | false => .none
      | .none => .none
  | .none => .none
| .validOfInstantiate pos args =>
  match r.getValid pos with
  | .some (lctx, t) => evalValidOfInstantiate ltv lctx t args
  | .none => .none
| .validOfInstantiateRev pos args =>
  match r.getValid pos with
  | .some (lctx, t) => evalValidOfInstantiate ltv lctx t args.reverse
  | .none => .none
| .validOfCongrArg pos rw =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rw with
    | .some rwt => REntry.valid lctx <$> t.congrArg? rwt
    | .none => .none
  | .none => .none
| .validOfCongrFun pos rw =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rw with
    | .some rwt => REntry.valid lctx <$> t.congrFun? rwt
    | .none => .none
  | .none => .none
| .validOfCongr pos rwFn rwArg =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      match r.getValidEnsureLCtx lctx rwArg with
      | .some rwArgt => REntry.valid lctx <$> t.congr? rwFnt rwArgt
      | .none => .none
    | .none => .none
  | .none => .none
| .validOfCongrArgs pos rws =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidsEnsureLCtx lctx rws with
    | .some ts => REntry.valid lctx <$> t.congrArgs? ts
    | .none => .none
  | .none => .none
| .validOfCongrFunN pos rwFn n =>
  match r.getValid pos with
  | .some (lctx, t) => 
    match r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt => REntry.valid lctx <$> t.congrFunN? rwFnt n
    | _ => .none
  | .none => .none
| .validOfCongrs pos rwFn rwArgs =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      match r.getValidsEnsureLCtx lctx rwArgs with
      | .some rwArgt => REntry.valid lctx <$> t.congrs? rwFnt rwArgt
      | .none => .none
    | .none => .none
  | .none => .none

theorem ChkStep.evalValidOfIntros_correct (lval : CheckerValuation)
  (tV : LamThmValid lval.toLamValuation lctx t) :
  Option.allp (REntry.correct lval) (evalValidOfIntros lctx t idx) := by
  revert lctx t; induction idx <;> intros lctx t tV
  case zero => exact tV
  case succ idx IH =>
    dsimp [evalValidOfIntros]
    match h : t.intro1? with
    | .some (s, t') =>
      apply IH; apply LamThmValid.intro1 tV h
    | .none => exact True.intro

theorem ChkStep.evalValidOfInstantiate_coorect (lval : CheckerValuation)
  (tV : LamThmValid lval.toLamValuation lctx t) :
  Option.allp (REntry.correct lval) (evalValidOfInstantiate lval.toLamTyVal lctx t args) := by
  revert lctx t; induction args <;> intros lctx t tV
  case nil =>
    unfold evalValidOfInstantiate; exact tV
  case cons arg args IH =>
    unfold evalValidOfInstantiate;
    match lctx with
    | .nil => exact True.intro
    | .cons argTy lctx =>
      dsimp
      match h₁ : LamTerm.lamThmWFCheck? lval.toLamTyVal lctx arg with
      | .some s =>
        dsimp
        match h₂ : s.beq argTy with
        | true =>
          dsimp; apply IH
          cases (LamSort.beq_eq _ _ h₂)
          have h₁' := LamThmWF.ofLamThmWFCheck? (lval:=lval.toLamValuation) h₁
          apply LamThmValid.instantiate1 h₁' tV
        | false => exact True.intro
      | .none => exact True.intro

theorem ChkStep.eval_correct
  (lval : CheckerValuation.{u}) (r : RTable) (inv : r.inv lval) :
  (cs : ChkStep) → Option.allp (REntry.correct lval) (cs.eval lval.toLamTyVal r)
| .nop => True.intro
| .wfOfCheck lctx t => by
  dsimp [eval]
  cases h : LamTerm.lamThmWFCheck? lval.toLamTyVal lctx t <;> try exact True.intro
  case some s =>
    dsimp [REntry.correct]; apply LamThmWFP.ofLamThmWF
    exact LamThmWF.ofLamThmWFCheck? h
| .wfOfAppend ex pos => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.append (RTable.getWF_correct inv h)
| .wfOfPrepend ex pos => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.prepend (RTable.getWF_correct inv h)
| .wfOfHeadBeta pos => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.ofLamThmEquiv_r;
      apply LamThmEquiv.ofHeadBeta (RTable.getWF_correct inv h)
| .wfOfBetaBounded pos bound => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      apply LamThmWFP.ofLamThmWF;
      apply LamThmWF.ofLamThmEquiv_r;
      apply LamThmEquiv.ofBetaBounded (RTable.getWF_correct inv h)
| .validOfIntro1F pos => by
  dsimp [eval]
  cases h₁ : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      dsimp
      match h₂ : t.intro1F? with
      | .some (s, p) =>
        apply LamThmValid.intro1F (RTable.getValid_correct inv h₁) h₂
      | .none => exact True.intro
| .validOfIntro1H pos => by
  dsimp [eval]
  cases h₁ : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      dsimp
      match h₂ : t.intro1H? with
      | .some (s, p) =>
        apply LamThmValid.intro1H (RTable.getValid_correct inv h₁) h₂
      | .none => exact True.intro
| .validOfIntros pos idx => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.evalValidOfIntros_correct _ h'
| .validOfHeadBeta pos => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply LamThmValid.mpLamThmEquiv _ _ _ h'
      apply LamThmEquiv.ofHeadBeta (LamThmWF.ofLamThmValid h')
| .validOfBetaBounded pos bound => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply LamThmValid.mpLamThmEquiv _ _ _ h'
      apply LamThmEquiv.ofBetaBounded (LamThmWF.ofLamThmValid h')
| .validOfImp p₁₂ p₁ => by
  dsimp [eval]
  match h₁ : r.getValid p₁₂ with
  | .some (lctx, t₁₂) =>
    dsimp
    match h₂ : r.getValidEnsureLCtx lctx p₁ with
    | .some t₁ =>
      dsimp
      match h₃ : LamTerm.impApp? t₁₂ t₁ with
      | .some t₂ =>
        have h₁' := RTable.getValid_correct inv h₁
        have h₂' := RTable.getValidEnsureLCtx_correct inv h₂
        apply LamThmValid.impApp h₁' h₂' h₃
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfImps imp ps => by
  dsimp [eval]
  match himp : r.getValid imp with
  | .some (lctx, t) =>
    dsimp
    match hps : RTable.getValidsEnsureLCtx r lctx ps with
    | .some ts =>
      dsimp
      match hap : LamTerm.impApps? t ts with
      | .some t' =>
        have himp := RTable.getValid_correct inv himp
        have hps := RTable.getValidsEnsureLCtx_correct inv hps
        apply LamThmValid.impApps himp hps hap
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfInstantiate1 pos arg => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match lctx with
    | .nil => exact True.intro
    | .cons argTy lctx =>
      dsimp
      match h₂ : LamTerm.lamThmWFCheck? lval.toLamTyVal lctx arg with
      | .some s =>
        dsimp
        match h₃ : s.beq argTy with
        | true =>
          dsimp [Option.allp, REntry.correct]
          cases (LamSort.beq_eq _ _ h₃)
          have h₁' := LamThmWF.ofLamThmWFCheck? (lval:=lval.toLamValuation) h₂
          have h₂' := RTable.getValid_correct inv h₁
          apply LamThmValid.instantiate1 h₁' h₂'
        | false => exact True.intro
      | .none => exact True.intro
  | .none => exact True.intro
| .validOfInstantiate pos args => by
  dsimp [eval]
  match h : r.getValid pos with
  | .some (lctx, t) =>
    let h' := RTable.getValid_correct inv h
    apply ChkStep.evalValidOfInstantiate_coorect _ h'
  | .none => exact True.intro
| .validOfInstantiateRev pos args => by
  dsimp [eval]
  match h : r.getValid pos with
  | .some (lctx, t) =>
    let h' := RTable.getValid_correct inv h
    apply ChkStep.evalValidOfInstantiate_coorect _ h'
  | .none => exact True.intro
| .validOfCongrArg pos rw => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrw : r.getValidEnsureLCtx lctx rw with
    | .some rwt =>
      dsimp
      match hcongr : t.congrArg? rwt with
      | .some t' =>
        dsimp [Option.allp, REntry.correct]
        let ht := RTable.getValid_correct inv hpos
        let hrw := RTable.getValidEnsureLCtx_correct inv hrw
        apply LamThmValid.mpLamThmEquiv _ _ _ ht
        apply LamThmEquiv.congrArg? (LamThmWF.ofLamThmValid ht) hrw hcongr
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfCongrFun pos rw => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrw : r.getValidEnsureLCtx lctx rw with
    | .some rwt =>
      dsimp
      match hcongr : t.congrFun? rwt with
      | .some t' =>
        dsimp [Option.allp, REntry.correct]
        let ht := RTable.getValid_correct inv hpos
        let hrw := RTable.getValidEnsureLCtx_correct inv hrw
        apply LamThmValid.mpLamThmEquiv _ _ _ ht
        apply LamThmEquiv.congrFun? (LamThmWF.ofLamThmValid ht) hrw hcongr
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfCongr pos rwFn rwArg => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrwFn : r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      dsimp
      match hrwArg : r.getValidEnsureLCtx lctx rwArg with
      | .some rwArgt =>
        dsimp
        match hcongr : t.congr? rwFnt rwArgt with
        | .some t' =>
          dsimp [Option.allp, REntry.correct]
          let ht := RTable.getValid_correct inv hpos
          let hrwFn := RTable.getValidEnsureLCtx_correct inv hrwFn
          let hrwArg := RTable.getValidEnsureLCtx_correct inv hrwArg
          apply LamThmValid.mpLamThmEquiv _ _ _ ht
          apply LamThmEquiv.congr? (LamThmWF.ofLamThmValid ht) hrwFn hrwArg hcongr
        | .none => exact True.intro
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfCongrArgs pos rws => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrws : r.getValidsEnsureLCtx lctx rws with
    | .some rws' =>
      dsimp
      match hcongr : t.congrArgs? rws' with
      | .some t' =>
        let ht := RTable.getValid_correct inv hpos
        let hrws := RTable.getValidsEnsureLCtx_correct inv hrws
        apply LamThmValid.mpLamThmEquiv _ _ _ ht
        apply LamThmEquiv.congrArgs? (LamThmWF.ofLamThmValid ht) hrws hcongr
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfCongrFunN pos rwFn n => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrwFn : RTable.getValidEnsureLCtx r lctx rwFn with
    | .some rwFnt =>
      dsimp
      match hcongr : t.congrFunN? rwFnt n with
      | .some t' =>
        dsimp [Option.allp, REntry.correct]
        let ht := RTable.getValid_correct inv hpos
        let hrwFn := RTable.getValidEnsureLCtx_correct inv hrwFn
        apply LamThmValid.mpLamThmEquiv _ _ _ ht
        apply LamThmEquiv.congrFunN? (LamThmWF.ofLamThmValid ht) hrwFn hcongr
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfCongrs pos rwFn rwArgs => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrwFn : r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      dsimp
      match hrwArgs : r.getValidsEnsureLCtx lctx rwArgs with
      | .some rwArgt =>
        dsimp
        match hcongr : t.congrs? rwFnt rwArgt with
        | .some t' =>
          dsimp [Option.allp, REntry.correct]
          let ht := RTable.getValid_correct inv hpos
          let hrwFn := RTable.getValidEnsureLCtx_correct inv hrwFn
          let hrwArgs := RTable.getValidsEnsureLCtx_correct inv hrwArgs
          apply LamThmValid.mpLamThmEquiv _ _ _ ht
          apply LamThmEquiv.congrs? (LamThmWF.ofLamThmValid ht) hrwFn hrwArgs hcongr
        | .none => exact True.intro
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro

-- The first `ChkStep` specifies the checker step
-- The second `Nat` specifies the position to insert the resulting term
-- Note that
--   1. All entries `(x : ChkStep × Nat)` that insert result into the
--      `wf` table should have distinct second component
--   2. All entries `(x : ChkStep × Nat)` that insert result into the
--      `valid` table should have distinct second component
-- Note that we decide where (`wf` or `valid`) to insert the resulting
--   term by looking at `(c : ChkStep).eval`
abbrev ChkSteps := BinTree (ChkStep × Nat)

def ChkStep.run (ltv : LamTyVal) (r : RTable) (c : ChkStep) (n : Nat) : RTable :=
  match ChkStep.eval ltv r c with
  | .none => r
  | .some re => r.insert n re

theorem ChkStep.run_correct
  (lval : CheckerValuation.{u}) (r : RTable) (inv : r.inv lval) (c : ChkStep) (n : Nat) :
  (ChkStep.run lval.toLamTyVal r c n).inv lval := by
  dsimp [ChkStep.run]
  have eval_correct := ChkStep.eval_correct lval r inv c; revert eval_correct
  cases h : eval lval.toLamTyVal r c <;> intro eval_correct
  case none => exact inv
  case some re =>
    cases re <;> dsimp [RTable.inv] <;> rw [BinTree.allp_insert] <;> dsimp
    case wf lctx s t =>
      apply And.intro
      case left => exact eval_correct
      case right => intros; apply inv
    case valid lctx t =>
      apply And.intro
      case left => exact eval_correct
      case right => intros; apply inv
    case nonempty s =>
      apply And.intro
      case left => exact eval_correct
      case right => intros; apply inv

def ChkSteps.run (ltv : LamTyVal) (r : RTable) (cs : ChkSteps) : RTable :=
  BinTree.foldl (fun r (c, n) => ChkStep.run ltv r c n) r cs

theorem ChkSteps.run_correct
  (lval : CheckerValuation.{u}) (r : RTable) (inv : r.inv lval) (cs : ChkSteps) :
  (ChkSteps.run lval.toLamTyVal r cs).inv lval := by
  dsimp [ChkSteps.run]; apply BinTree.foldl_inv (RTable.inv lval) inv
  intro r (c, n) inv'; exact ChkStep.run_correct lval r inv' c n

def ChkSteps.runFromBeginning (lval : CheckerValuation.{u}) (it : ImportTable lval) (cs : ChkSteps) :=
  ChkSteps.run lval.toLamTyVal it.importFacts cs

theorem Checker
  (lval : CheckerValuation.{u}) (it : ImportTable lval) (cs : ChkSteps) :
  (ChkSteps.runFromBeginning lval it cs).inv lval := by
  apply ChkSteps.run_correct; apply ImportTable.importFacts_correct

end Auto.Embedding.Lam