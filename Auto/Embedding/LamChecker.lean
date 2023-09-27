import Auto.Embedding.LamConv
import Auto.Embedding.LamTermInterp
import Auto.Lib.BinTree

namespace Auto.Embedding.Lam

-- An entry of RTable
inductive REntry where
  -- Well-formed formulas, with types
  -- We do not import well-formedness facts because
  --   we have `LamWF.ofLamCheck?`
  | wf         : List LamSort → LamSort → LamTerm → REntry
  -- Valid propositions
  -- The initial formulas in the `valid` table will be
  --   validEVar0 from `ImportTable`
  | valid      : List LamSort → LamTerm → REntry
  | nonempty   : LamSort → REntry
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

def REntry.beq : REntry → REntry → Bool
| .wf ss s t, .wf ss' s' t' => ss == ss' && s == s' && t == t'
| .valid ss t, .valid ss' t' => ss == ss' && t == t'
| .nonempty s, .nonempty s' => s == s'
| _, _ => false

instance : BEq REntry where
  beq := REntry.beq

theorem REntry.beq_def {l r : REntry} : (l == r) = l.beq r := rfl

theorem REntry.beq_refl {r : REntry} : (r == r) = true := by
  cases r <;> rw [REntry.beq_def] <;> dsimp [beq] <;>
    (try rw [LawfulBEq.rfl]) <;>
    (try rw [LawfulBEq.rfl]) <;>
    (try rw [LawfulBEq.rfl]) <;> rfl

theorem REntry.eq_of_beq_eq_true {l r : REntry} (H : (l == r) = true) : l = r := by
  cases l <;> cases r <;> (try cases H) <;> rw [beq_def] at H <;> dsimp [beq] at H
    <;> (try rw [Bool.and_eq_true] at H)
  case wf =>
    rw [Bool.and_eq_true] at H; have ⟨⟨sseq, seq⟩, teq⟩ := H
    rw [LawfulBEq.eq_of_beq sseq, LawfulBEq.eq_of_beq seq, LawfulBEq.eq_of_beq teq]
  case valid =>
    have ⟨sseq, teq⟩ := H
    rw [LawfulBEq.eq_of_beq sseq, LawfulBEq.eq_of_beq teq]
  case nonempty =>
    rw [LawfulBEq.eq_of_beq H]

instance : LawfulBEq REntry where
  eq_of_beq := REntry.eq_of_beq_eq_true
  rfl := REntry.beq_refl

def REntry.getValid? : REntry → Option (List LamSort × LamTerm)
| .wf _ _ _ => .none
| .valid ss t => .some (ss, t)
| .nonempty _ => .none

-- Table of valid propositions and well-formed formulas
-- Note that `Auto.BinTree α` is equivalent to `Nat → Option α`,
--   which means that `.some` entries may be interspersed
--   with `.none` entries
structure RTable where
  entries     : BinTree REntry
  maxEVarSucc : Nat
  lamEVarTy   : BinTree LamSort

def RTable.beq : RTable → RTable → Bool
| ⟨le, lmax, llam⟩, ⟨re, rmax, rlam⟩ => le == re && lmax == rmax && llam == rlam

instance : BEq RTable where
  beq := RTable.beq

theorem RTable.beq_def {l r : RTable} : (l == r) = l.beq r := rfl

theorem RTable.beq_refl {r : RTable} : (r == r) = true := by
  rw [beq_def]; cases r; dsimp [beq]
  rw [LawfulBEq.rfl, LawfulBEq.rfl, LawfulBEq.rfl]; rfl

theorem RTable.eq_of_beq_eq_true {l r : RTable} (H : (l == r) = true) : l = r := by
  rw [RTable.beq_def] at H; cases l; cases r; dsimp [beq] at H
  rw [Bool.and_eq_true, Bool.and_eq_true] at H
  have ⟨⟨hentries, hme⟩, hle⟩ := H
  rw [LawfulBEq.eq_of_beq hentries]
  rw [LawfulBEq.eq_of_beq hme]
  rw [LawfulBEq.eq_of_beq hle]

instance : LawfulBEq RTable where
  eq_of_beq := RTable.eq_of_beq_eq_true
  rfl := RTable.beq_refl

def RTable.get? (r : RTable) := r.entries.get?

def RTable.addEntry (r : RTable) (e : REntry) (n : Nat) :=
  {r with entries := r.entries.insert n e}

def RTable.toLamEVarTy (r : RTable) := fun n => (r.lamEVarTy.get? n).getD (.base .prop)

section CVal

  -- Checker Partial Valuation (Valuation without `lamEVarTy` and `eVarVal`)
  structure CPVal where
    tyVal     : Nat → Type u
    var       : BinTree ((s : LamSort) × (s.interp tyVal))
    il        : BinTree ((s : LamSort) × (ILLift.{u} (s.interp tyVal)))

  -- Checker Valuation
  structure CVal (lamEVarTy : BinTree LamSort) extends CPVal where
    eVarVal   : ∀ (n : Nat), ((lamEVarTy.get? n).getD (.base .prop)).interp tyVal

  abbrev eVarTy (tyVal : Nat → Type u) (lamEVarTy : BinTree LamSort) :=
    ∀ (n : Nat), ((lamEVarTy.get? n).getD (.base .prop)).interp tyVal

  -- Used in checker metacode to construct `var`
  abbrev varSigmaMk.{u} (tyVal : Nat → Type u) :=
    @Sigma.mk LamSort (LamSort.interp tyVal)
  
  -- Used in checker metacode to construct `il`
  abbrev ilβ.{u} (tyVal : Nat → Type u) (s : LamSort) : Type u :=
    ILLift.{u} (s.interp tyVal)
  
  -- Used in checker metacode to construct `il`
  abbrev ilSigmaMk.{u} (tyVal : Nat → Type u) :=
    @Sigma.mk LamSort (ilβ.{u} tyVal)
  
  def ilVal.default (lamILTy : Nat → LamSort) (tyVal : Nat → Type u) :
    ∀ (n : Nat), ILLift.{u} ((lamILTy n).interp tyVal) :=
    fun n => ILLift.default ((lamILTy n).interp tyVal)

  def CVal.toLamTyVal (cv : CVal.{u} levt) : LamTyVal :=
    ⟨fun n => ((cv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).fst,
     fun n => ((cv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).fst,
     fun n => (levt.get? n).getD (.base .prop)⟩
  
  def CVal.toLamValuation (cv : CVal.{u} levt) : LamValuation :=
    ⟨cv.toLamTyVal, cv.tyVal,
     fun n => ((cv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).snd,
     fun n => ((cv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).snd,
     cv.eVarVal⟩

  def CPVal.toLamVarTy (cpv : CPVal.{u}) : Nat → LamSort :=
    fun n => ((cpv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).fst

  def CPVal.toLamILTy (cpv : CPVal.{u}) : Nat → LamSort :=
    fun n => ((cpv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).fst

  def CPVal.toLamTyValWithLamEVarTy (cpv : CPVal.{u}) (levt : Nat → LamSort) : LamTyVal :=
    ⟨fun n => ((cpv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).fst,
     fun n => ((cpv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).fst,
     levt⟩

  def CPVal.toLamTyValEraseEtom (cpv : CPVal.{u}) : LamTyVal :=
    ⟨fun n => ((cpv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).fst,
     fun n => ((cpv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).fst,
     fun _ => .base .prop⟩
  
  def CPVal.toLamValuationEraseEtom (cpv : CPVal.{u}) : LamValuation :=
    ⟨cpv.toLamTyValEraseEtom, cpv.tyVal,
     fun n => ((cpv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).snd,
     fun n => ((cpv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).snd,
     fun _ => GLift.up False⟩

  def CPVal.toLamValuationWithEVar (cpv : CPVal.{u}) (letv : Nat → LamSort)
    (eVarVal : ∀ (n : Nat), (letv n).interp cpv.tyVal) : LamValuation :=
    ⟨cpv.toLamTyValWithLamEVarTy letv, cpv.tyVal,
     fun n => ((cpv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).snd,
     fun n => ((cpv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).snd,
     eVarVal⟩

end CVal

def REntry.correct (cv : CVal.{u} levt) (maxEVarSucc : Nat) : REntry → Prop
| .wf lctx s t => LamThmWFP cv.toLamValuation lctx s t ∧ t.maxEVarSucc ≤ maxEVarSucc
| .valid lctx t => LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ maxEVarSucc
| .nonempty s => LamNonempty cv.tyVal s

theorem REntry.correct_eVarIrrelevance
  (cpv : CPVal.{u})
  (levt₁ levt₂ : BinTree LamSort)
  (val₁ : eVarTy cpv.tyVal levt₁) (val₂ : eVarTy cpv.tyVal levt₂)
  (hirr : ∀ n, n < maxEVarSucc →
    (levt₁.get? n).getD (.base .prop) = (levt₂.get? n).getD (.base .prop) ∧
    HEq (val₁ n) (val₂ n))
  (c₁ : REntry.correct ⟨cpv, val₁⟩ maxEVarSucc re) :
  REntry.correct ⟨cpv, val₂⟩ maxEVarSucc re := by
  cases re <;> (try exact c₁) <;> (try apply And.intro _ c₁.right) <;> (try intro lctx')
  case _ =>
    cases c₁.left lctx'; case intro wf =>
      apply Nonempty.intro; apply LamWF.eVarIrrelevance (lwf:=wf) <;> try rfl
      intro n H; apply (hirr n (Nat.le_trans H c₁.right)).left
  case _ =>
    have hValid := c₁.left lctx'
    apply LamValid.eVarIrrelevance (hValid := hValid) <;> try rfl
    intro n H; apply hirr n (Nat.le_trans H c₁.right)

theorem REntry.correct_increaseMaxEVarSucc
  (c₁ : REntry.correct cv maxEVarSucc₁ re) (h : maxEVarSucc₁ ≤ maxEVarSucc₂) :
  REntry.correct cv maxEVarSucc₂ re := by
  cases re <;> (try apply c₁) <;> (try apply And.intro c₁.left) <;> try (apply Nat.le_trans c₁.right; apply h)

-- Invariant of `RTable`
def RTable.inv (r : RTable) (cv : CVal.{u} r.lamEVarTy) :=
  r.entries.allp (fun re => re.correct cv r.maxEVarSucc)

theorem RTable.inv_eVarIrrelevance
  (cpv : CPVal.{u})
  (levt₁ levt₂ : BinTree LamSort)
  (val₁ : eVarTy cpv.tyVal levt₁) (val₂ : eVarTy cpv.tyVal levt₂)
  (hirr : ∀ (n : Nat), n < maxEVarSucc_ →
    (levt₁.get? n).getD (.base .prop) = (levt₂.get? n).getD (.base .prop) ∧
    HEq (val₁ n) (val₂ n))
  (c₁ : RTable.inv ⟨entries_, maxEVarSucc_, levt₁⟩ ⟨cpv, val₁⟩) :
  RTable.inv ⟨entries_, maxEVarSucc_, levt₂⟩ ⟨cpv, val₂⟩ := by
  dsimp [inv, BinTree.allp] at *; intro n; have c₁' := c₁ n; revert c₁'
  cases BinTree.get? entries_ n
  case none => intro _; exact True.intro
  case some re =>
    dsimp [Option.allp]; apply REntry.correct_eVarIrrelevance; exact hirr

theorem RTable.inv_increaseMaxEVarSucc
  (c₁ : RTable.inv r cv) (h : r.maxEVarSucc ≤ maxEVarSucc_ ) :
  RTable.inv {r with maxEVarSucc := maxEVarSucc_} cv := by
  dsimp [inv, BinTree.allp] at *; intro n; have c₁' := c₁ n; revert c₁'
  cases BinTree.get? r.entries n
  case none => intro _; exact True.intro
  case some re =>
    dsimp [Option.allp]; intro c₁'; apply REntry.correct_increaseMaxEVarSucc c₁' h

theorem RTable.wfInv_get {r : RTable} {cv : CVal.{u} r.lamEVarTy}
  (inv : RTable.inv r cv) (h : get? r n = Option.some (.wf lctx s t)) :
  LamThmWFP cv.toLamValuation lctx s t ∧ t.maxEVarSucc ≤ r.maxEVarSucc := by
  have inv' := inv n; dsimp [get?] at h; rw [h] at inv'; exact inv'

theorem RTable.validInv_get {r : RTable} {cv : CVal.{u} r.lamEVarTy}
  (inv : RTable.inv r cv) (h : get? r n = Option.some (.valid lctx t)) :
  LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc := by
  have inv' := inv n; dsimp [get?] at h; rw [h] at inv'; exact inv'

theorem RTable.nonemptyInv_get {r : RTable} {cv : CVal.{u} r.lamEVarTy}
  (inv : RTable.inv r cv) (h : get? r n = Option.some (.nonempty s)) :
  LamNonempty cv.tyVal s := by
  have inv' := inv n; dsimp [get?] at h; rw [h] at inv'; exact inv'

def RTable.getWF (r : RTable) (v : Nat) : Option (List LamSort × LamSort × LamTerm) :=
  match r.get? v with
  | .some (.wf lctx s t) => .some (lctx, s, t)
  | .some (.valid _ _) => .none
  | .some (.nonempty _) => .none
  | .none => .none

theorem RTable.getWF_correct
  (inv : RTable.inv r cv) (heq : getWF r v = .some (lctx, s, t)) :
  LamThmWFP cv.toLamValuation lctx s t ∧ t.maxEVarSucc ≤ r.maxEVarSucc := by
  revert heq; dsimp [getWF]
  match h : r.get? v with
  | .some (.wf _ _ _) => intro heq; cases heq; apply RTable.wfInv_get inv h
  | .some (.valid lctx t) => intro heq; cases heq
  | .some (.nonempty _) => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValid (r : RTable) (v : Nat) : Option (List LamSort × LamTerm) :=
  match r.get? v with
  | .some (.valid lctx t) => .some (lctx, t)
  | .some (.wf _ _ _) => .none
  | .some (.nonempty _) => .none
  | .none => .none

theorem RTable.getValid_correct
  (inv : RTable.inv r cv) (heq : getValid r v = .some (lctx, t)) :
  LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc := by
  revert heq; dsimp [getValid]
  match h : r.get? v with
  | .some (.valid lctx t) => intro heq; cases heq; apply RTable.validInv_get inv h
  | .some (.wf _ _ _) => intro heq; cases heq
  | .some (.nonempty _) => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValidEnsureLCtx (r : RTable) (lctx : List LamSort) (v : Nat) : Option LamTerm :=
  match r.getValid v with
  | .some (lctx', t) =>
    match lctx.beq lctx' with
    | true => .some t
    | false => .none
  | .none => .none

theorem RTable.getValidEnsureLCtx_correct
  (inv : RTable.inv r cv) (heq : getValidEnsureLCtx r lctx v = .some t) :
  LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc := by
  revert heq; dsimp [getValidEnsureLCtx]
  match hv : r.getValid v with
  | .some (lctx', t) =>
    dsimp
    match hlctx : lctx.beq lctx' with
    | true =>
      intro heq; cases heq; cases (LawfulBEq.eq_of_beq (α:=List LamSort) hlctx)
      apply RTable.getValid_correct inv hv
    | false => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValidExport (r : RTable) (v : Nat) : Option (List LamSort × LamTerm) :=
  match r.getValid v with
  | .some (lctx, t) =>
    match t.maxEVarSucc with
    | 0 => .some (lctx, t)
    | _ + 1 => .none
  | .none => .none

theorem RTable.getValidExport_correct
  (inv : ∃ eV, RTable.inv r ⟨cpv, eV⟩) (heq : getValidExport r v = .some (lctx, t)) :
  LamThmValid cpv.toLamValuationEraseEtom lctx t := by
  revert heq; dsimp [getValidExport]
  match hv : r.getValid v with
  | .some (lctx', t) =>
    dsimp
    match htE : t.maxEVarSucc with
    | 0 =>
      intro heq; cases heq; have ⟨eV, inv⟩ := inv
      apply LamThmValid.eVarIrrelevance (CVal.toLamValuation ⟨cpv, eV⟩) <;> try rfl
      case hirr =>
        intros h H; rw [htE] at H; cases H
      case a =>
        apply (RTable.getValid_correct inv hv).left
    | _ + 1 => intro heq; cases heq
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
  (inv : RTable.inv r cv) (heq : getValidsEnsureLCtx r lctx vs = .some ts) :
  HList (fun t => LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc) ts := by
  induction vs generalizing ts
  case nil =>
    cases heq; apply HList.nil
  case cons v vs IH =>
    dsimp [getValidsEnsureLCtx] at heq; revert heq
    match hv : r.get? v with
    | .some (.valid lctx' t) =>
      dsimp
      match hlctx : lctx.beq lctx' with
      | true =>
        dsimp; cases (LawfulBEq.eq_of_beq (α:=List LamSort) hlctx)
        match hvs : getValidsEnsureLCtx r lctx vs with
        | .some ts' =>
          intro heq; cases heq
          exact HList.cons (RTable.validInv_get inv hv) (IH hvs);
        | .none => intro heq; cases heq
      | false => intro heq; cases heq
    | .some (.wf _ _ _) => intro heq; cases heq
    | .some (.nonempty _) => intro heq; cases heq
    | .none => intro heq; cases heq

-- The meta code of the checker will prepare this `ImportTable`
abbrev ImportTable (cpv : CPVal.{u}) :=
  Auto.BinTree (@PSigma LamTerm (fun p => (LamTerm.interpAsProp cpv.toLamValuationEraseEtom dfLCtxTy (dfLCtxTerm _) p).down))

-- Used by the meta code of the checker to build `ImportTable`
abbrev importTablePSigmaβ (cpv : CPVal.{u}) (p : LamTerm) :=
  (LamTerm.interpAsProp cpv.toLamValuationEraseEtom dfLCtxTy (dfLCtxTerm _) p).down

abbrev importTablePSigmaMk (cpv : CPVal.{u}) :=
  @PSigma.mk LamTerm (importTablePSigmaβ cpv)

abbrev importTablePSigmaDefault (cpv : CPVal.{u}) :
  @PSigma LamTerm (fun p => (LamTerm.interpAsProp cpv.toLamValuationEraseEtom dfLCtxTy (dfLCtxTerm _) p).down) :=
  ⟨.base .trueE, True.intro⟩

def ImportTable.importFacts (it : ImportTable cpv) : BinTree REntry :=
  it.mapOpt (fun ⟨p, _⟩ =>
    match p.lamCheck? cpv.toLamTyValEraseEtom dfLCtxTy with
    | .some (.base .prop) =>
      match p.maxLooseBVarSucc with
      | 0 =>
        match p.maxEVarSucc with
        | 0 => .some (.valid [] (p.resolveImport cpv.toLamTyValEraseEtom))
        | _ + 1 => .none
      | _ + 1 => .none
    | _                   => .none)

theorem ImportTable.importFacts_correct (it : ImportTable cpv) (n : Nat) :
  it.importFacts.allp (@REntry.correct levt ⟨cpv, eVarVal⟩ n) := by
  dsimp [RTable.inv, importFacts]; rw [BinTree.mapOpt_allp]
  intro n; apply Option.allp_uniform;
  intro ⟨p, validp⟩; dsimp
  cases h₁ : LamTerm.lamCheck? cpv.toLamTyValEraseEtom dfLCtxTy p <;> try exact True.intro
  case a.some s =>
    cases s <;> try exact True.intro
    case base b =>
      cases b <;> try exact True.intro
      dsimp
      cases h₂ : p.maxLooseBVarSucc <;> try exact True.intro
      cases h₃ : p.maxEVarSucc <;> try exact True.intro
      dsimp [Option.allp, REntry.correct]
      apply And.intro
      case left =>
        apply LamThmValid.eVarIrrelevance cpv.toLamValuationEraseEtom <;> try rfl
        case hirr =>
          intro n H; rw [LamTerm.maxEVarSucc_resolveImport, h₃] at H; cases H
        case a =>
          apply LamThmValid.resolveImport (lval:=cpv.toLamValuationEraseEtom)
          apply LamThmValid.ofInterpAsProp cpv.toLamValuationEraseEtom _ h₁ validp h₂    
      case right =>
        rw [LamTerm.maxEVarSucc_resolveImport]
        rw [h₃]; apply Nat.zero_le

inductive ChkStep where
  | wfOfCheck (lctx : List LamSort) (t : LamTerm) : ChkStep
  | wfOfAppend (ex : List LamSort) (pos : Nat) : ChkStep
  | wfOfPrepend (ex : List LamSort) (pos : Nat) : ChkStep
  | wfOfHeadBeta (pos : Nat) : ChkStep
  | wfOfBetaBounded (pos : Nat) (bound : Nat) : ChkStep
  | validOfIntro1F (pos : Nat) : ChkStep
  | validOfIntro1H (pos : Nat) : ChkStep
  | validOfIntros (pos idx : Nat) : ChkStep
  | validOfRevert (pos : Nat) : ChkStep
  | validOfReverts (pos : Nat) (idx : Nat) : ChkStep
  | validOfHeadBeta (pos : Nat) : ChkStep
  | validOfBetaBounded (pos : Nat) (bound : Nat) : ChkStep
  | validOfExtensionalize (pos : Nat) : ChkStep
  -- `t₁ → t₂` and `t₁` implies `t₂`
  | validOfImp (p₁₂ : Nat) (p₁ : Nat) : ChkStep
  -- `t₁ → t₂ → ⋯ → tₖ → s` and `t₁, t₂, ⋯, tₖ` implies `s`
  | validOfImps (imp : Nat) (ps : List Nat) : ChkStep
  | validOfInstantiate1 (pos : Nat) (arg : LamTerm) : ChkStep
  -- `.bvar i` replaced with `args[i]`
  | validOfInstantiate (pos : Nat) (args : List LamTerm) : ChkStep
  -- `.bvar i` replaced with `args.reverse[i]`
  | validOfInstantiateRev (pos : Nat) (args : List LamTerm) : ChkStep
  | validOfCongrArg (pos rw : Nat) : ChkStep
  | validOfCongrFun (pos rw : Nat) : ChkStep
  | validOfCongr (pos rwFn rwArg : Nat) : ChkStep
  | validOfCongrArgs (pos : Nat) (rws : List Nat) : ChkStep
  | validOfCongrFunN (pos rwFn n : Nat) : ChkStep
  | validOfCongrs (pos rwFn : Nat) (rwArgs : List Nat) : ChkStep
  | skolemize (pos : Nat) : ChkStep
  | define (t : LamTerm) : ChkStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

def ChkStep.toString : ChkStep → String
| .wfOfCheck lctx t => s!"wfOfCheck {lctx} {t}"
| .wfOfAppend ex pos => s!"wfOfAppend {ex} {pos}"
| .wfOfPrepend ex pos => s!"wfOfPrepend {ex} {pos}"
| .wfOfHeadBeta pos => s!"wfOfHeadBeta {pos}"
| .wfOfBetaBounded pos bound => s!"wfOfBetaBounded {pos} {bound}"
| .validOfIntro1F pos => s!"validOfIntro1F {pos}"
| .validOfIntro1H pos => s!"validOfIntro1H {pos}"
| .validOfIntros pos idx => s!"validOfIntros {pos} {idx}"
| .validOfRevert pos => s!"validOfRevert {pos}"
| .validOfReverts pos idx => s!"validOfReverts {pos} {idx}"
| .validOfHeadBeta pos => s!"validOfHeadBeta {pos}"
| .validOfBetaBounded pos bound => s!"validOfBetaBounded {pos} {bound}"
| .validOfExtensionalize pos => s!"validOfExtensionalize {pos}"
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
| .skolemize pos => s!"skolemize {pos}"
| .define t => s!"define {t}"

instance : ToString ChkStep where
  toString := ChkStep.toString

inductive EvalResult where
  | fail
  | addEntry (e : REntry)
  | newEtomWithValid (s : LamSort) (lctx : List LamSort) (t : LamTerm)
deriving Inhabited, Hashable, BEq

def EvalResult.toString : EvalResult → String
| .fail => "fail"
| .addEntry e => s!"addEntry ({e})"
| .newEtomWithValid s lctx t => s!"newEtomWithValid {s} {lctx} {t}"

instance : ToString EvalResult where
  toString := EvalResult.toString

def EvalResult.correct (r : RTable) (cv : CVal.{u} r.lamEVarTy)
  (res : EvalResult) :=
  match res with
  | .fail => True
  | .addEntry re => REntry.correct cv r.maxEVarSucc re
  | .newEtomWithValid s lctx t =>
    ∃ (eVarVal' : eVarTy cv.tyVal (r.lamEVarTy.insert r.maxEVarSucc s)),
      (∀ n, n < r.maxEVarSucc → HEq (eVarVal' n) (cv.eVarVal n)) ∧
      REntry.correct ⟨cv.toCPVal, eVarVal'⟩ r.maxEVarSucc.succ (.valid lctx t)

theorem EvalResult.correct_newEtomWithValid_mpLamEVarTy
  {r : RTable} {cv : CVal.{u} r.lamEVarTy}
  (levt : Nat → LamSort)
  (heq : (∀ n, levt n = ((r.lamEVarTy.insert r.maxEVarSucc s).get? n).getD (.base .prop)))
  (H : ∃ (eVarVal' : ∀ (n : Nat), (levt n).interp cv.tyVal),
      (∀ n, n < r.maxEVarSucc → HEq (eVarVal' n) (cv.eVarVal n)) ∧
      LamThmValid (cv.toCPVal.toLamValuationWithEVar levt eVarVal') lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc.succ) :
  EvalResult.correct r cv (.newEtomWithValid s lctx t) := by
  dsimp [correct, REntry.correct]; have ⟨eVarVal', hirr, H⟩ := H
  have levteq : levt = (fun n => ((r.lamEVarTy.insert r.maxEVarSucc s).get? n).getD (.base .prop)) := funext heq
  cases levteq; exists eVarVal'

def ChkStep.evalValidOfIntros (lctx : List LamSort) (t : LamTerm)
  : (idx : Nat) → EvalResult
  | 0 => .addEntry (.valid lctx t)
  | .succ idx =>
    match t.intro1? with
    | .some (s, t') => evalValidOfIntros (s :: lctx) t' idx
    | .none => .fail

def ChkStep.evalValidOfReverts (lctx : List LamSort) (t : LamTerm)
  : (idx : Nat) → EvalResult
  | 0 => .addEntry (.valid lctx t)
  | .succ idx =>
    match lctx with
    | .nil => .fail
    | .cons s lctx => evalValidOfReverts lctx (.mkForallEF s t) idx

def ChkStep.evalValidOfInstantiate (n : Nat) (ltv : LamTyVal) (lctx : List LamSort) (t : LamTerm)
  : (args : List LamTerm) → EvalResult
  | .nil => .addEntry (.valid lctx t)
  | .cons arg args =>
    match lctx with
    | .nil => .fail
    | .cons argTy lctx =>
      match arg.lamThmWFCheck? ltv lctx with
      | .some s =>
        match s.beq argTy with
        | true =>
          match Nat.ble arg.maxEVarSucc n with
          | true => evalValidOfInstantiate n ltv lctx (LamTerm.instantiate1 arg t) args
          | false => .fail
        | false => .fail
      | .none => .fail

def ChkStep.eval (lvt lit : Nat → LamSort) (r : RTable) : (cs : ChkStep) → EvalResult
| .wfOfCheck lctx t =>
  match LamTerm.lamThmWFCheck? ⟨lvt, lit, r.toLamEVarTy⟩ lctx t with
  | .some rty =>
    match Nat.ble t.maxEVarSucc r.maxEVarSucc with
    | true => .addEntry (.wf lctx rty t)
    | false => .fail
  | .none => .fail
| .wfOfAppend ex pos =>
  match r.getWF pos with
  | .some (lctx, s, t) => .addEntry (.wf (lctx ++ ex) s t)
  | .none => .fail
| .wfOfPrepend ex pos =>
  match r.getWF pos with
  | .some (lctx, s, t) => .addEntry (.wf (ex ++ lctx) s (t.bvarLifts ex.length))
  | .none => .fail
| .wfOfHeadBeta pos =>
  match r.getWF pos with
  | .some (lctx, s, t) => .addEntry (.wf lctx s t.headBeta)
  | .none => .fail
| .wfOfBetaBounded pos bound =>
  match r.getWF pos with
  | .some (lctx, s, t) => .addEntry (.wf lctx s (t.betaBounded bound))
  | .none => .fail
| .validOfIntro1F pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match t.intro1F? with
    | .some (s, p) => .addEntry (.valid (s :: lctx) p)
    | .none => .fail
  | .none => .fail
| .validOfIntro1H pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match t.intro1H? with
    | .some (s, p) => .addEntry (.valid (s :: lctx) p)
    | .none => .fail
  | .none => .fail
| .validOfIntros pos idx =>
  match r.getValid pos with
  | .some (lctx, t) => evalValidOfIntros lctx t idx
  | .none => .fail
| .validOfRevert pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match lctx with
    | .nil => .fail
    | .cons ty lctx => .addEntry (.valid lctx (.mkForallEF ty t))
  | .none => .fail
| .validOfReverts pos idx =>
  match r.getValid pos with
  | .some (lctx, t) => evalValidOfReverts lctx t idx
  | .none => .fail
| .validOfHeadBeta pos =>
  match r.getValid pos with
  | .some (lctx, t) => .addEntry (.valid lctx t.headBeta)
  | .none => .fail
| .validOfBetaBounded pos bound =>
  match r.getValid pos with
  | .some (lctx, t) => .addEntry (.valid lctx (t.betaBounded bound))
  | .none => .fail
| .validOfExtensionalize pos =>
  match r.getValid pos with
  | .some (lctx, t) => .addEntry (.valid lctx t.extensionalize)
  | .none => .fail
| .validOfImp p₁₂ p₁ =>
  match r.getValid p₁₂ with
  | .some (lctx, t₁₂) =>
    match r.getValidEnsureLCtx lctx p₁ with
    | .some t₁ =>
      match LamTerm.impApp? t₁₂ t₁ with
      | .some t₂ => .addEntry (.valid lctx t₂)
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfImps imp ps =>
  match r.getValid imp with
  | .some (lctx, t) =>
    match r.getValidsEnsureLCtx lctx ps with
    | .some ts =>
      match t.impApps? ts with
      | .some res => .addEntry (REntry.valid lctx res)
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfInstantiate1 pos arg =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match lctx with
    | .nil => .fail
    | .cons argTy lctx =>
      match arg.lamThmWFCheck? ⟨lvt, lit, r.toLamEVarTy⟩ lctx with
      | .some s =>
        match s.beq argTy with
        | true =>
          match Nat.ble arg.maxEVarSucc r.maxEVarSucc with
          | true => .addEntry (.valid lctx (LamTerm.instantiate1 arg t))
          | false => .fail
        | false => .fail
      | .none => .fail
  | .none => .fail
| .validOfInstantiate pos args =>
  match r.getValid pos with
  | .some (lctx, t) =>
    evalValidOfInstantiate r.maxEVarSucc ⟨lvt, lit, r.toLamEVarTy⟩ lctx t args
  | .none => .fail
| .validOfInstantiateRev pos args =>
  match r.getValid pos with
  | .some (lctx, t) =>
    evalValidOfInstantiate r.maxEVarSucc ⟨lvt, lit, r.toLamEVarTy⟩ lctx t args.reverse
  | .none => .fail
| .validOfCongrArg pos rw =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rw with
    | .some rwt =>
      match t.congrArg? rwt with
      | .some res => .addEntry (REntry.valid lctx res)
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfCongrFun pos rw =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rw with
    | .some rwt =>
      match t.congrFun? rwt with
      | .some res => .addEntry (REntry.valid lctx res)
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfCongr pos rwFn rwArg =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      match r.getValidEnsureLCtx lctx rwArg with
      | .some rwArgt =>
        match t.congr? rwFnt rwArgt with
        | .some res => .addEntry (REntry.valid lctx res)
        | .none => .fail
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfCongrArgs pos rws =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidsEnsureLCtx lctx rws with
    | .some ts =>
      match t.congrArgs? ts with
      | .some res => .addEntry (REntry.valid lctx res)
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfCongrFunN pos rwFn n =>
  match r.getValid pos with
  | .some (lctx, t) => 
    match r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      match t.congrFunN? rwFnt n with
      | .some res => .addEntry (REntry.valid lctx res)
      | .none => .fail
    | _ => .fail
  | .none => .fail
| .validOfCongrs pos rwFn rwArgs =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rwFn with
    | .some rwFnt =>
      match r.getValidsEnsureLCtx lctx rwArgs with
      | .some rwArgt =>
        match t.congrs? rwFnt rwArgt with
        | .some res => .addEntry (REntry.valid lctx res)
        | .none => .fail
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .skolemize pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match t.skolemize? r.maxEVarSucc lctx with
    | .some (s, t) => .newEtomWithValid (s.mkFuncsRev lctx) lctx t
    | .none => .fail
  | .none => .fail
| .define t =>
  match LamTerm.lamThmWFCheck? ⟨lvt, lit, r.toLamEVarTy⟩ [] t with
  | .some s =>
    match Nat.ble t.maxEVarSucc r.maxEVarSucc with
    | true => .newEtomWithValid s [] (.mkEq s (.etom r.maxEVarSucc) t)
    | false => .fail
  | .none => .fail

private theorem ChkStep.eval_correct_wfAux
  {cond₁ cond₂ : Prop} (h : LamThmWFP lval₁ lctx₁ s₁ t₁ ∧ cond₁)
  (wfimp : LamThmWF lval₁ lctx₁ s₁ t₁ → LamThmWF lval₂ lctx₂ s₂ t₂)
  (condimp : cond₁ → cond₂) :
  LamThmWFP lval₂ lctx₂ s₂ t₂ ∧ cond₂ :=
  And.intro (LamThmWFP.ofLamThmWF (wfimp (LamThmWF.ofLamThmWFP h.left))) (condimp h.right)

private theorem ChkStep.eval_correct_validAux
  {cond₁ cond₂ : Prop} (h : LamThmValid lval₁ lctx₁ t₁ ∧ cond₁)
  (vimp : LamThmValid lval₁ lctx₁ t₁ → LamThmValid lval₂ lctx₂ t₂)
  (condimp : cond₁ → cond₂) :
  LamThmValid lval₂ lctx₂ t₂ ∧ cond₂ :=
  And.intro (vimp h.left) (condimp h.right)

theorem ChkStep.evalValidOfIntros_correct
  {r : RTable} (cv : CVal.{u} r.lamEVarTy)
  (tV : LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc) :
  (evalValidOfIntros lctx t idx).correct r cv := by
  induction idx generalizing lctx t
  case zero => exact tV
  case succ idx IH =>
    dsimp [evalValidOfIntros]
    match h : t.intro1? with
    | .some (s, t') =>
      have ⟨tV, eS⟩ := tV
      apply IH; apply And.intro (LamThmValid.intro1? tV h)
      rw [LamTerm.maxEVarSucc_intro1? h]; exact eS
    | .none => exact True.intro

theorem ChkStep.evalValidOfReverts_correct
  {r : RTable} (cv : CVal.{u} r.lamEVarTy)
  (tV : LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc) :
  (evalValidOfReverts lctx t idx).correct r cv := by
  induction idx generalizing lctx t
  case zero => unfold evalValidOfReverts; exact tV
  case succ idx IH =>
    unfold evalValidOfReverts
    match lctx with
    | .nil => exact True.intro
    | .cons s lctx =>
      apply IH; apply And.intro tV.left.revert1F
      dsimp [LamTerm.mkForallEF, LamTerm.maxEVarSucc]
      rw [Nat.max, Nat.max_zero_left]; apply tV.right

theorem ChkStep.evalValidOfInstantiate_correct
  {r : RTable} (cv : CVal.{u} r.lamEVarTy)
  (tV : LamThmValid cv.toLamValuation lctx t ∧ t.maxEVarSucc ≤ r.maxEVarSucc) :
  (evalValidOfInstantiate r.maxEVarSucc cv.toLamTyVal lctx t args).correct r cv := by
  induction args generalizing lctx t
  case nil =>
    unfold evalValidOfInstantiate; exact tV
  case cons arg args IH =>
    unfold evalValidOfInstantiate;
    match lctx with
    | .nil => exact True.intro
    | .cons argTy lctx =>
      dsimp
      match h₁ : LamTerm.lamThmWFCheck? cv.toLamTyVal lctx arg with
      | .some s =>
        dsimp
        match h₂ : s.beq argTy with
        | true =>
          dsimp
          match h₃ : Nat.ble (LamTerm.maxEVarSucc arg) r.maxEVarSucc with
          | true =>
            apply IH
            cases (LamSort.eq_of_beq_eq_true h₂)
            have h₁' := LamThmWF.ofLamThmWFCheck? (lval:=cv.toLamValuation) h₁
            have ⟨tV, eS⟩ := tV
            apply And.intro (LamThmValid.instantiate1 h₁' tV)
            apply Nat.le_trans (LamTerm.maxEVarSucc_instantiateAt)
            rw [Nat.max_le]; apply And.intro _ eS; apply Nat.le_of_ble_eq_true h₃
          | false => exact True.intro
        | false => exact True.intro
      | .none => exact True.intro

theorem ChkStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : ChkStep) → EvalResult.correct r cv (cs.eval cv.toLamVarTy cv.toLamILTy r)
| .wfOfCheck lctx t => by
  dsimp [eval]
  cases h₁ : LamTerm.lamThmWFCheck? ⟨cv.toLamVarTy, cv.toLamILTy, r.toLamEVarTy⟩ lctx t <;> try exact True.intro
  case some s =>
    match h₂ : Nat.ble (LamTerm.maxEVarSucc t) r.maxEVarSucc with
    | true =>
      dsimp [REntry.correct]; apply And.intro (LamThmWFP.ofLamThmWF ?left) ?right
      case left =>
        exact LamThmWF.ofLamThmWFCheck? (lval := cv.toLamValuation) h₁
      case right =>
        apply Nat.le_of_ble_eq_true h₂
    | false => exact True.intro
| .wfOfAppend ex pos => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      have h' := RTable.getWF_correct inv h
      apply ChkStep.eval_correct_wfAux h' _ id
      intro hwf; apply LamThmWF.append hwf
| .wfOfPrepend ex pos => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      have h' := RTable.getWF_correct inv h
      apply ChkStep.eval_correct_wfAux h'
      case wfimp =>
        intro hwf; apply LamThmWF.prepend hwf
      case condimp =>
        intro hcond;
        dsimp [LamTerm.bvarLifts, LamTerm.bvarLiftsIdx]
        rw [LamTerm.maxEVarSucc_mapBVarAt]; exact hcond
| .wfOfHeadBeta pos => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      have h' := RTable.getWF_correct inv h
      apply ChkStep.eval_correct_wfAux h'
      case wfimp =>
        intro hwf; apply LamThmWF.ofLamThmEquiv_r;
        apply LamThmEquiv.ofHeadBeta hwf
      case condimp =>
        intro hcond; apply Nat.le_trans _ hcond
        apply LamTerm.maxEVarSucc_headBeta
| .wfOfBetaBounded pos bound => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      have h' := RTable.getWF_correct inv h
      apply ChkStep.eval_correct_wfAux h'
      case wfimp =>
        intro hwf; apply LamThmWF.ofLamThmEquiv_r;
        apply LamThmEquiv.ofBetaBounded hwf
      case condimp =>
        intro hcond; apply Nat.le_trans _ hcond
        apply LamTerm.maxEVarSucc_betaBounded
| .validOfIntro1F pos => by
  dsimp [eval]
  cases h₁ : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      dsimp
      match h₂ : t.intro1F? with
      | .some (s, p) =>
        have h' := RTable.getValid_correct inv h₁
        apply ChkStep.eval_correct_validAux h'
        case vimp =>
          intro hv; apply LamThmValid.intro1F? hv h₂
        case condimp =>
          intro hcond; rw [LamTerm.maxEVarSucc_intro1F? h₂]; exact hcond
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
        have h' := RTable.getValid_correct inv h₁
        apply ChkStep.eval_correct_validAux h'
        case vimp =>
          intro hv; apply LamThmValid.intro1H? hv h₂
        case condimp =>
          intro hcond; rw [LamTerm.maxEVarSucc_intro1H? h₂]; exact hcond
      | .none => exact True.intro
| .validOfIntros pos idx => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      have hcorrect := ChkStep.evalValidOfIntros_correct (idx:=idx) _ h'
      dsimp; revert hcorrect
      cases (evalValidOfIntros lctx t idx) <;> exact id
| .validOfRevert pos => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      match lctx with
      | .nil => exact True.intro
      | .cons ty lctx =>
        have h' := RTable.getValid_correct inv h
        apply And.intro
        case left => intro lctx'; apply h'.left.revert1F
        case right =>
          dsimp [LamTerm.mkForallEF, LamTerm.maxEVarSucc]
          rw [Nat.max, Nat.max_zero_left]; apply h'.right
| .validOfReverts pos idx => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.evalValidOfReverts_correct _ h'
| .validOfHeadBeta pos => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.eval_correct_validAux h'
      case vimp =>
        intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
        apply LamThmEquiv.ofHeadBeta (LamThmWF.ofLamThmValid hv)
      case condimp =>
        intro hcond; apply Nat.le_trans LamTerm.maxEVarSucc_headBeta hcond
| .validOfBetaBounded pos bound => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.eval_correct_validAux h'
      case vimp =>
        intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
        apply LamThmEquiv.ofBetaBounded (LamThmWF.ofLamThmValid hv)
      case condimp =>
        intro hcond; apply Nat.le_trans LamTerm.maxEVarSucc_betaBounded hcond
| .validOfExtensionalize pos => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.eval_correct_validAux h'
      case vimp =>
        intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
        apply LamThmEquiv.ofExtensionalize (LamThmWF.ofLamThmValid hv)
      case condimp =>
        intro hcond; rw [LamTerm.maxEVarSucc_extensionalizeAux]; exact hcond
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
        apply ChkStep.eval_correct_validAux h₁'
        case vimp =>
          intro hv; apply LamThmValid.impApp hv h₂'.left h₃
        case condimp =>
          intro hcond; apply Nat.le_trans (LamTerm.maxEVarSucc_impApp? h₃) hcond
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
        apply ChkStep.eval_correct_validAux himp
        case vimp =>
          have hps' := HList.map (fun _ h => And.left h) hps
          intro hv; apply LamThmValid.impApps himp.left hps' hap
        case condimp =>
          intro hcond; apply Nat.le_trans (LamTerm.maxEVarSucc_impApps? hap) hcond
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
      match h₂ : LamTerm.lamThmWFCheck? ⟨cv.toLamVarTy, cv.toLamILTy, r.toLamEVarTy⟩ lctx arg with
      | .some s =>
        dsimp
        match h₃ : s.beq argTy with
        | true =>
          match h₄ : Nat.ble (LamTerm.maxEVarSucc arg) r.maxEVarSucc with
          | true =>
            dsimp [Option.allp, REntry.correct]
            cases (LamSort.eq_of_beq_eq_true h₃)
            have h₁' := LamThmWF.ofLamThmWFCheck? (lval:=cv.toLamValuation) h₂
            have h₂' := RTable.getValid_correct inv h₁
            apply ChkStep.eval_correct_validAux h₂'
            case vimp =>
              intro hv; apply LamThmValid.instantiate1 h₁' hv
            case condimp =>
              intro cond; apply Nat.le_trans LamTerm.maxEVarSucc_instantiate1
              rw [Nat.max_le]; apply And.intro (Nat.le_of_ble_eq_true h₄) cond
          | false => exact True.intro
        | false => exact True.intro
      | .none => exact True.intro
  | .none => exact True.intro
| .validOfInstantiate pos args => by
  dsimp [eval]
  match h : r.getValid pos with
  | .some (lctx, t) =>
    let h' := RTable.getValid_correct inv h
    apply ChkStep.evalValidOfInstantiate_correct _ h'
  | .none => exact True.intro
| .validOfInstantiateRev pos args => by
  dsimp [eval]
  match h : r.getValid pos with
  | .some (lctx, t) =>
    let h' := RTable.getValid_correct inv h
    apply ChkStep.evalValidOfInstantiate_correct _ h'
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
        apply ChkStep.eval_correct_validAux ht
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
          apply LamThmEquiv.congrArg? (LamThmWF.ofLamThmValid hv) hrw.left hcongr
        case condimp =>
          intro cond; apply LamTerm.maxEVarSucc_congrArg? cond hrw.right hcongr
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
        apply ChkStep.eval_correct_validAux ht
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
          apply LamThmEquiv.congrFun? (LamThmWF.ofLamThmValid hv) hrw.left hcongr
        case condimp =>
          intro cond; apply LamTerm.maxEVarSucc_congrFun? cond hrw.right hcongr
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
          apply ChkStep.eval_correct_validAux ht
          case vimp =>
            intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
            apply LamThmEquiv.congr? (LamThmWF.ofLamThmValid hv) hrwFn.left hrwArg.left hcongr
          case condimp =>
            intro cond; apply LamTerm.maxEVarSucc_congr? cond hrwFn.right hrwArg.right hcongr
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
        apply ChkStep.eval_correct_validAux ht
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
          have hrws' := HList.map (fun _ h => And.left h) hrws
          apply LamThmEquiv.congrArgs? (LamThmWF.ofLamThmValid hv) hrws' hcongr
        case condimp =>
          have hrws' := HList.map (fun _ h => And.right h) hrws
          intro cond; apply LamTerm.maxEVarSucc_congrArgs? cond hrws' hcongr
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
        apply ChkStep.eval_correct_validAux ht
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
          apply LamThmEquiv.congrFunN? (LamThmWF.ofLamThmValid hv) hrwFn.left hcongr
        case condimp =>
          intro cond; apply LamTerm.maxEVarSucc_congrFunN? cond hrwFn.right hcongr
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
          apply ChkStep.eval_correct_validAux ht
          case vimp =>
            intro hv; apply LamThmValid.mpLamThmEquiv _ _ hv
            have hrwArgs' := HList.map (fun _ h => And.left h) hrwArgs
            apply LamThmEquiv.congrs? (LamThmWF.ofLamThmValid hv) hrwFn.left hrwArgs' hcongr
          case condimp =>
            have hrwArgs' := HList.map (fun _ h => And.right h) hrwArgs
            intro cond; apply LamTerm.maxEVarSucc_congrs? cond hrwFn.right hrwArgs' hcongr
        | .none => exact True.intro
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .skolemize pos => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.skolemize? t r.maxEVarSucc lctx with
    | .some (s, t') =>
      dsimp
      let levt' := replaceAt (LamSort.mkFuncsRev s lctx) r.maxEVarSucc
        (fun n => (r.lamEVarTy.get? n).getD (.base .prop))
      apply EvalResult.correct_newEtomWithValid_mpLamEVarTy levt' (fun n => by
        rw [BinTree.get?_insert_eq_replaceAt_get?])
      have ⟨h₁', hle⟩ := RTable.getValid_correct inv h₁
      have ⟨eVarVal', hsk⟩ := LamThmValid.skolemize? h₁' h₂ hle
      cases cv; case mk cpv eV =>
        exists replaceAtDep eVarVal' r.maxEVarSucc eV
        apply And.intro ?left (And.intro hsk ?right)
        case left =>
          intro n hlt; dsimp [replaceAt, replaceAtDep]
          rw [Nat.beq_eq_false_of_ne (Nat.ne_of_lt hlt)]
        case right =>
          apply Nat.le_trans (LamTerm.maxEVarSucc_skolemize? h₂)
          rw [Nat.max_le]; apply And.intro _ (Nat.le_refl _)
          apply Nat.le_trans hle (Nat.le_succ _)
    | .none => exact True.intro
  | .none => exact True.intro
| .define t => by
  dsimp [eval]
  match h₁ : LamTerm.lamThmWFCheck? ⟨cv.toLamVarTy, cv.toLamILTy, r.toLamEVarTy⟩ [] t with
  | .some s =>
    dsimp
    match h₂ : Nat.ble t.maxEVarSucc r.maxEVarSucc with
    | true =>
      dsimp
      have h₁' := LamThmWF.ofLamThmWFCheck? (lval:=cv.toLamValuation) h₁
      have h₂' := Nat.le_of_ble_eq_true h₂
      let levt' := replaceAt s r.maxEVarSucc
        (fun n => (r.lamEVarTy.get? n).getD (.base .prop))
      apply EvalResult.correct_newEtomWithValid_mpLamEVarTy levt' (fun n => by
        rw [BinTree.get?_insert_eq_replaceAt_get?])
      have ⟨eVarVal', hdef⟩ := LamThmValid.define h₁' h₂'
      cases cv; case mk cpv eV =>
        exists replaceAtDep eVarVal' r.maxEVarSucc eV
        apply And.intro ?left (And.intro hdef ?right)
        case left =>
          intro n hlt; dsimp [replaceAt, replaceAtDep]
          rw [Nat.beq_eq_false_of_ne (Nat.ne_of_lt hlt)]
        case right =>
          rw [LamTerm.maxEVarSucc_mkEq]; dsimp [LamTerm.maxEVarSucc]
          rw [Nat.max_le]; apply And.intro (Nat.le_refl _) (Nat.le_step h₂')
    | false => exact True.intro
  | .none => exact True.intro

def RTable.runEvalResult (r : RTable) (n : Nat) : EvalResult → RTable
| .fail => r
| .addEntry e => { r with entries := r.entries.insert n e }
| .newEtomWithValid s lctx t =>
  { r with entries := r.entries.insert n (.valid lctx t),
           lamEVarTy := r.lamEVarTy.insert r.maxEVarSucc s,
           maxEVarSucc := r.maxEVarSucc + 1 }

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

def ChkStep.run (lvt lit : Nat → LamSort) (r : RTable) (c : ChkStep) (n : Nat) : RTable :=
  r.runEvalResult n (ChkStep.eval lvt lit r c)

theorem ChkStep.run_correct
  (r : RTable) (cpv : CPVal.{u}) (inv : ∃ eV, r.inv ⟨cpv, eV⟩) (c : ChkStep) (n : Nat) :
  ∃ eV', (ChkStep.run cpv.toLamVarTy cpv.toLamILTy r c n).inv ⟨cpv, eV'⟩ := by
  have ⟨eV, inv⟩ := inv
  dsimp [ChkStep.run]
  have eval_correct := ChkStep.eval_correct r ⟨cpv, eV⟩ inv c; revert eval_correct
  cases h : eval cpv.toLamVarTy cpv.toLamILTy r c <;> intro eval_correct
  case fail => exact ⟨eV, inv⟩
  case addEntry re =>
    exists eV
    cases re <;> dsimp [RTable.inv, RTable.runEvalResult] <;> rw [BinTree.allp_insert]
      <;> dsimp <;> apply And.intro eval_correct (fun _ _ => inv _)
  case newEtomWithValid s lctx t =>
    have ⟨eVarVal, ⟨hirr, hcorrect⟩⟩ := eval_correct; exists eVarVal
    dsimp [RTable.inv, RTable.runEvalResult]; rw [BinTree.allp_insert]
    apply And.intro hcorrect
    intro n' _
    cases r; case mk entries maxEVarSucc lamEVarTy _ =>
      dsimp; dsimp at eV hirr eVarVal hcorrect
      have inv' := RTable.inv_eVarIrrelevance _ _ _ _ eVarVal (fun n H => by
        apply And.intro;
        case left =>
          rw [BinTree.insert.correct₂]; apply Nat.ne_of_gt H
        case right =>
          apply HEq.symm; apply hirr n H) inv
      have inv' := RTable.inv_increaseMaxEVarSucc inv' (Nat.le_succ _)
      dsimp at inv'; apply inv'

def ChkSteps.run (lvt lit : Nat → LamSort) (r : RTable) (cs : ChkSteps) : RTable :=
  BinTree.foldl (fun r (c, n) => ChkStep.run lvt lit r c n) r cs

theorem ChkSteps.run_correct
  (r : RTable) (cpv : CPVal.{u}) (inv : ∃ eV, r.inv ⟨cpv, eV⟩) (cs : ChkSteps) :
  ∃ eV', (ChkSteps.run cpv.toLamVarTy cpv.toLamILTy r cs).inv ⟨cpv, eV'⟩ := by
  dsimp [ChkSteps.run]; apply BinTree.foldl_inv (fun (r : RTable) => ∃ eV', RTable.inv r ⟨cpv, eV'⟩) inv
  intro r' (c, n) inv'; exact ChkStep.run_correct r' cpv inv' c n

def ChkSteps.runFromBeginning (cpv : CPVal.{u}) (it : ImportTable cpv) (cs : ChkSteps) :=
  ChkSteps.run cpv.toLamVarTy cpv.toLamILTy ⟨it.importFacts, 0, .leaf⟩ cs


-- Note : Using this theorem directly in the checker will cause
--   performance issue, especially when there are a lot of
--   `etom`s. This is probably caused by the type of `eV` in
--   `∃ eV` being dependent on the result of `ChkSteps.runFromBeginning` 
theorem CheckerAux
  (cpv : CPVal.{u}) (it : ImportTable cpv) (cs : ChkSteps) :
  ∃ eV, (ChkSteps.runFromBeginning cpv it cs).inv ⟨cpv, eV⟩ := by
  apply ChkSteps.run_correct; dsimp [RTable.inv, BinTree.get?]
  exists fun _ => BinTree.get?'_leaf _ ▸ GLift.up False;
  apply ImportTable.importFacts_correct

theorem Checker.getValidExport_directReduce
  (cpv : CPVal.{u}) (it : ImportTable cpv) (cs : ChkSteps) (v : Nat)
  (heq : RTable.getValidExport (ChkSteps.runFromBeginning cpv it cs) v = some (lctx, t)) :
  LamThmValid cpv.toLamValuationEraseEtom lctx t :=
  RTable.getValidExport_correct (CheckerAux _ _ _) heq

-- Note : Do not use the counterpart of this theorem in proof by reflection.
-- Surprisingly, if we use this theorem in proof by reflection, the performance
--   issue will not be the `ChkSteps.run` in `runEq`. Instead, it would be
--   caused by compiling the definition of `runResult`. I'm not sure why it's
--   the case, but Lean sometimes exhibit superlinear (even quadratic) compilation
--   time with respect to the size of `runResult`.
theorem Checker.getValidExport_indirectReduceAux
  (cpv : CPVal.{u}) (it : ImportTable cpv) (cs : ChkSteps) (v : Nat)
  (importFacts : BinTree REntry) (hImport : it.importFacts = importFacts)
  (lvt lit : BinTree LamSort)
  (hlvt : lvt = cpv.var.mapOpt (fun x => .some x.fst))
  (hlit : lit = cpv.il.mapOpt (fun x => .some x.fst))
  (runResult : RTable)
  (runEq : ChkSteps.run
    (fun n => (lvt.get? n).getD (.base .prop))
    (fun n => (lit.get? n).getD (.base .prop))
    ⟨importFacts, 0, .leaf⟩ cs = runResult)
  (lctx : List LamSort) (t : LamTerm)
  (heq : RTable.getValidExport runResult v = some (lctx, t)) :
  LamThmValid cpv.toLamValuationEraseEtom lctx t := by
  apply RTable.getValidExport_correct _ heq
  have lvtEq : (fun n => (lvt.get? n).getD (.base .prop)) = cpv.toLamVarTy := by
    cases cpv; dsimp [CPVal.toLamVarTy]; apply funext; intro n
    rw [← Option.getD_map (f:=@Sigma.fst LamSort _)]; dsimp
    apply congrFun; apply congrArg; rw [hlvt, BinTree.get?_mapOpt]
    apply Eq.symm; apply Option.map_eq_bind
  have litEq : (fun n => (lit.get? n).getD (.base .prop)) = cpv.toLamILTy := by
    cases cpv; dsimp [CPVal.toLamILTy]; apply funext; intro n
    rw [← Option.getD_map (f:=@Sigma.fst LamSort _)]; dsimp
    apply congrFun; apply congrArg; rw [hlit, BinTree.get?_mapOpt]
    apply Eq.symm; apply Option.map_eq_bind
  rw [lvtEq, litEq] at runEq; cases runEq; apply ChkSteps.run_correct
  dsimp [RTable.inv, BinTree.get?]
  exists fun _ => BinTree.get?'_leaf _ ▸ GLift.up False
  cases hImport; apply ImportTable.importFacts_correct

theorem Checker.getValidExport_indirectReduce
  (cpv : CPVal.{u}) (it : ImportTable cpv) (cs : ChkSteps) (v : Nat)
  (importFacts : BinTree REntry) (hImport : it.importFacts = importFacts)
  (lvt lit : BinTree LamSort)
  (hlvt : lvt = cpv.var.mapOpt (fun x => .some x.fst))
  (hlit : lit = cpv.il.mapOpt (fun x => .some x.fst))
  (lctx : List LamSort) (t : LamTerm)
  (heq : RTable.getValidExport (ChkSteps.run
    (fun n => (lvt.get? n).getD (.base .prop))
    (fun n => (lit.get? n).getD (.base .prop))
    ⟨importFacts, 0, .leaf⟩ cs) v = some (lctx, t)) :
  LamThmValid cpv.toLamValuationEraseEtom lctx t := Checker.getValidExport_indirectReduceAux
    cpv it cs v importFacts hImport lvt lit hlvt hlit _ rfl lctx t heq

def Checker.getValidExport_indirectReduce_reflection_runEq
  (lvt lit : BinTree LamSort) (importFacts : BinTree REntry)
  (cs : ChkSteps) (v : Nat) (lctx : List LamSort) (t : LamTerm):=
  RTable.getValidExport (ChkSteps.run
    (fun n => (lvt.get? n).getD (.base .prop))
    (fun n => (lit.get? n).getD (.base .prop))
    ⟨importFacts, 0, .leaf⟩ cs) v == (lctx, t)

theorem Checker.getValidExport_indirectReduce_reflection
  (cpv : CPVal.{u}) (it : ImportTable cpv) (cs : ChkSteps) (v : Nat)
  (importFacts : BinTree REntry) (hImport : it.importFacts = importFacts)
  (lvt lit : BinTree LamSort)
  (hlvt : lvt = cpv.var.mapOpt (fun x => .some x.fst))
  (hlit : lit = cpv.il.mapOpt (fun x => .some x.fst))
  (lctx : List LamSort) (t : LamTerm)
  (heq : Checker.getValidExport_indirectReduce_reflection_runEq lvt lit importFacts cs v lctx t) :
  LamThmValid cpv.toLamValuationEraseEtom lctx t :=
  Checker.getValidExport_indirectReduce cpv it cs v importFacts hImport lvt
    lit hlvt hlit lctx t (LawfulBEq.eq_of_beq heq)

end Auto.Embedding.Lam