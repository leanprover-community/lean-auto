import Auto.Embedding.LamTermInterp
import Auto.Embedding.LamConv
import Auto.Embedding.LamInference
import Auto.Embedding.LamLCtx
import Auto.Embedding.LamPrep
import Auto.Embedding.LamBitVec
import Auto.Embedding.LamInductive
import Auto.Lib.BinTree
open Lean

namespace Auto.Embedding.Lam

/-- An entry of RTable -/
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

def REntry.containsSort (re : REntry) (s : LamSort) : Bool :=
  match re with
  | .wf ss s' t => ss.any (fun s' => s'.contains s) || s'.contains s || t.containsSort s
  | .valid ss t => ss.any (fun s' => s'.contains s) || t.containsSort s
  | .nonempty s' => s'.contains s

def REntry.allLamTerms (re : REntry) : List LamTerm :=
  match re with
  | .wf _ _ t   => [t]
  | .valid _  t => [t]
  | .nonempty _ => []

/--
  Table of valid propositions and well-formed formulas
  Note that `Auto.BinTree α` is equivalent to `Nat → Option α`,
    which means that `.some` entries may be interspersed
    with `.none` entries
-/
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

  /-- Checker Partial Valuation (Valuation without `lamEVarTy` and `eVarVal`) -/
  structure CPVal where
    tyVal     : Nat → Type u
    var       : BinTree ((s : LamSort) × (s.interp tyVal))
    il        : BinTree ((s : LamSort) × (ILLift.{u} (s.interp tyVal)))

  /-- Checker Valuation -/
  structure CVal (lamEVarTy : BinTree LamSort) extends CPVal where
    eVarVal   : ∀ (n : Nat), ((lamEVarTy.get? n).getD (.base .prop)).interp tyVal

  abbrev eVarTy (tyVal : Nat → Type u) (lamEVarTy : BinTree LamSort) :=
    ∀ (n : Nat), ((lamEVarTy.get? n).getD (.base .prop)).interp tyVal

  /-- Used in checker metacode to construct `var` -/
  abbrev varSigmaMk.{u} (tyVal : Nat → Type u) :=
    @Sigma.mk LamSort (LamSort.interp tyVal)

  /-- Used in checker metacode to construct `il` -/
  abbrev ilβ.{u} (tyVal : Nat → Type u) (s : LamSort) : Type u :=
    ILLift.{u} (s.interp tyVal)

  /-- Used in checker metacode to construct `il` -/
  abbrev ilSigmaMk.{u} (tyVal : Nat → Type u) :=
    @Sigma.mk LamSort (ilβ.{u} tyVal)

  noncomputable def ilVal.default (lamILTy : Nat → LamSort) (tyVal : Nat → Type u) :
    ∀ (n : Nat), ILLift.{u} ((lamILTy n).interp tyVal) :=
    fun n => ILLift.default ((lamILTy n).interp tyVal)

  def CVal.toLamTyVal (cv : CVal.{u} levt) : LamTyVal :=
    ⟨fun n => ((cv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).fst,
     fun n => ((cv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).fst,
     fun n => (levt.get? n).getD (.base .prop)⟩

  noncomputable def CVal.toLamValuation (cv : CVal.{u} levt) : LamValuation :=
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

  noncomputable def CPVal.toLamValuationEraseEtom (cpv : CPVal.{u}) : LamValuation :=
    ⟨cpv.toLamTyValEraseEtom, cpv.tyVal,
     fun n => ((cpv.var.get? n).getD ⟨.base .prop, GLift.up False⟩).snd,
     fun n => ((cpv.il.get? n).getD ⟨.base .prop, ILLift.default _⟩).snd,
     fun _ => GLift.up False⟩

  noncomputable def CPVal.toLamValuationWithEVar (cpv : CPVal.{u}) (letv : Nat → LamSort)
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

/-- Invariant of `RTable` -/
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

def RTable.getWF (r : RTable) (w : Nat) : Option (List LamSort × LamSort × LamTerm) :=
  match r.get? w with
  | .some (.wf lctx s t) => .some (lctx, s, t)
  | _ => .none

theorem RTable.getWF_correct
  (inv : RTable.inv r cv) (heq : getWF r w = .some (lctx, s, t)) :
  LamThmWFP cv.toLamValuation lctx s t ∧ t.maxEVarSucc ≤ r.maxEVarSucc := by
  revert heq; dsimp [getWF]
  match h : r.get? w with
  | .some (.wf _ _ _) => intro heq; cases heq; apply RTable.wfInv_get inv h
  | .some (.valid lctx t) => intro heq; cases heq
  | .some (.nonempty _) => intro heq; cases heq
  | .none => intro heq; cases heq

def RTable.getValid (r : RTable) (v : Nat) : Option (List LamSort × LamTerm) :=
  match r.get? v with
  | .some (.valid lctx t) => .some (lctx, t)
  | _ => .none

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

noncomputable def RTable.getValidsEnsureLCtx_correct
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

def RTable.getNonempty (r : RTable) (v : Nat) : Option LamSort :=
  match r.get? v with
  | .some (.nonempty s) => .some s
  | _ => .none

theorem RTable.getNonempty_correct
  (inv : RTable.inv r cv) (heq : getNonempty r w = .some s) :
  LamNonempty cv.tyVal s := by
  revert heq; dsimp [getNonempty]
  match h : r.get? w with
  | .some (.nonempty s) => intro heq; cases heq; apply RTable.nonemptyInv_get inv h
  | .some (.wf _ _ _) => intro heq; cases heq
  | .some (.valid _ _) => intro heq; cases heq
  | .none => intro heq; cases heq

inductive ImportEntry where
  | valid     : LamTerm → ImportEntry
  | nonempty  : LamSort → ImportEntry

def ImportEntry.correct (lval : LamValuation) : ImportEntry → Prop
| .valid t => (t.interpAsProp lval dfLCtxTy (dfLCtxTerm _)).down
| .nonempty s => Nonempty (s.interp lval.tyVal)

/-- The meta code of the checker will prepare this `ImportTable` -/
abbrev ImportTable (cpv : CPVal.{u}) :=
  Auto.BinTree (@PSigma ImportEntry (ImportEntry.correct cpv.toLamValuationEraseEtom))

/-- Used by the meta code of the checker to build `ImportTable` -/
abbrev importTablePSigmaβ (cpv : CPVal.{u}) (ie : ImportEntry) :=
  ImportEntry.correct cpv.toLamValuationEraseEtom ie

abbrev importTablePSigmaMk (cpv : CPVal.{u}) :=
  @PSigma.mk ImportEntry (importTablePSigmaβ cpv)

def ImportTable.importFacts (it : ImportTable cpv) : BinTree REntry :=
  it.mapOpt (fun ⟨ie, _⟩ =>
    match ie with
    | .valid p =>
      match p.lamThmWFCheck? cpv.toLamTyValEraseEtom [] with
      | .some (.base .prop) =>
        match p.maxEVarSucc with
        | 0 => .some (.valid [] (p.resolveImport cpv.toLamTyValEraseEtom))
        | _ + 1 => .none
      | _                   => .none
    | .nonempty s => .some (.nonempty s))

theorem ImportTable.importFacts_correct (it : ImportTable cpv) (n : Nat) :
  it.importFacts.allp (@REntry.correct levt ⟨cpv, eVarVal⟩ n) := by
  dsimp [RTable.inv, importFacts]; rw [BinTree.mapOpt_allp]
  intro n; apply Option.allp_uniform
  intro ⟨ie, validIe⟩; dsimp
  match ie with
  | .valid p =>
    dsimp
    cases h₁ : LamTerm.lamThmWFCheck? cpv.toLamTyValEraseEtom [] p <;> try exact True.intro
    case some s =>
      cases s <;> try exact True.intro
      case base b =>
        cases b <;> try exact True.intro
        dsimp
        have ⟨h₁, h₂⟩ := LamTerm.lamThmWFCheck?_spec h₁
        have h₂ := Nat.le_zero.mp h₂
        cases h₃ : p.maxEVarSucc <;> try exact True.intro
        apply And.intro
        case left =>
          apply LamThmValid.eVarIrrelevance cpv.toLamValuationEraseEtom <;> try rfl
          case hirr =>
            intro n H; rw [LamTerm.maxEVarSucc_resolveImport, h₃] at H; cases H
          case a =>
            apply LamThmValid.resolveImport (lval:=cpv.toLamValuationEraseEtom)
            apply LamThmValid.ofInterpAsProp cpv.toLamValuationEraseEtom _ h₁ validIe h₂
        case right =>
          rw [LamTerm.maxEVarSucc_resolveImport]
          rw [h₃]; apply Nat.zero_le
  | .nonempty s =>
    dsimp [REntry.correct, Option.allp]; exact validIe

inductive ConvStep where
  | validOfHeadBeta (pos : Nat) : ConvStep
  | validOfBetaBounded (pos : Nat) (bound : Nat) : ConvStep
  /-- Exhaustively rewrite using functional extensionality -/
  | validOfExtensionalize (pos : Nat) : ConvStep
  /-- Symmetry to top-level equality -/
  | validOfEqSymm (pos : Nat) : ConvStep
  | validOfMp (pos rw : Nat) : ConvStep
  /-- Exhaustively rewrite using facts of form `valid [] (lhs = rhs)` -/
  | validOfMpAll (pos rw : Nat) : ConvStep
  | validOfCongrArg (pos rw : Nat) : ConvStep
  | validOfCongrFun (pos rw : Nat) : ConvStep
  | validOfCongr (pos rwFn rwArg : Nat) : ConvStep
  | validOfCongrArgs (pos : Nat) (rws : List Nat) : ConvStep
  | validOfCongrFunN (pos rwFn n : Nat) : ConvStep
  | validOfCongrs (pos rwFn : Nat) (rwArgs : List Nat) : ConvStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive ConvAtStep where
  | validOfEtaExpand1At (pos : Nat) (occ : List Bool) : ConvAtStep
  | validOfEtaReduce1At (pos : Nat) (occ : List Bool) : ConvAtStep
  | validOfEtaExpandNAt (pos n : Nat) (occ : List Bool) : ConvAtStep
  | validOfEtaReduceNAt (pos n : Nat) (occ : List Bool) : ConvAtStep
  /--
    Turn
    · `f = g`   into              `∀ x₁ x₂ ⋯ xₙ, f x₁ x₂ ⋯ xₙ = g x₁ x₂ ⋯ xₙ`
    · `f =  `   into     `fun g => ∀ x₁ x₂ ⋯ xₙ, f x₁ x₂ ⋯ xₙ = g x₁ x₂ ⋯ xₙ`
    · `  =  `   into   `fun f g => ∀ x₁ x₂ ⋯ xₙ, f x₁ x₂ ⋯ xₙ = g x₁ x₂ ⋯ xₙ`
  -/
  | validOfExtensionalizeEqAt (pos : Nat) (occ : List Bool) : ConvAtStep
  /--
    Turn `f = g` into `∀ x₁ x₂ ⋯ xₙ, f x₁ x₂ ⋯ xₙ = g x₁ x₂ ⋯ xₙ`,
      where `f` and `g` must be of type `s₀ → s₁ → ⋯ → sₙ₋₁ → ?`
  -/
  | validOfExtensionalizeEqFNAt (pos n : Nat) (occ : List Bool) : ConvAtStep
  /-- Turn `∀ x₁ x₂ ⋯ xₙ, f x₁ x₂ ⋯ xₙ = g x₁ x₂ ⋯ xₙ` into `f = g` -/
  | validOfIntensionalizeEqAt (pos : Nat) (occ : List Bool) : ConvAtStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive EtomStep where
  | skolemize (pos : Nat) : EtomStep
  | define (t : LamTerm) : EtomStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive FactStep where
  | boolFacts : FactStep
  | iteSpec  : LamSort → FactStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive InferenceStep where
  /--
    If `t` has no loose bvar `0` and `s` is inhabited (pn), then
    `∀ (_ : s), t` (pv) implies `LamTerm.instantiate1 (.atom 0) t`
  -/
  | validOfBVarLower (pv : Nat) (pn : Nat) : InferenceStep
  /-- Equivalent to repeated `validOfBVarLower` -/
  | validOfBVarLowers (pv : Nat) (pns : List Nat) : InferenceStep
  /-- `t₁ → t₂` and `t₁` implies `t₂` -/
  | validOfImp (p₁₂ : Nat) (p₁ : Nat) : InferenceStep
  /-- `t₁ → t₂ → ⋯ → tₖ → s` and `t₁, t₂, ⋯, tₖ` implies `s` -/
  | validOfImps (imp : Nat) (ps : List Nat) : InferenceStep
  /-- `.bvar 0` replaced with `arg` -/
  | validOfInstantiate1 (pos : Nat) (arg : LamTerm) : InferenceStep
  /--
    Call `validOfInstantiate1` sequentially on `arg[0] ⋯ args[k-1]`
    Note that `.bvar i` is not always replaced with `args[i]` because
      later instantiations will lower bvars in `args[i]` and may further
      instantiate bound variables occurring in `args[i]`
  -/
  | validOfInstantiate (pos : Nat) (args : List LamTerm) : InferenceStep
  /--
    Call `validOfInstantiate1` sequentially on `arg[k-1] ⋯ args[0]`
    Note that `.bvar i` is not always replaced with `args.reverse[i]` because
      later instantiations will lower bvars in `args.reverse[i]` and may further
      instantiate bound variables occurring in `args.reverse[i]`
  -/
  | validOfInstantiateRev (pos : Nat) (args : List LamTerm) : InferenceStep
  | validOfEqualize (pos : Nat) (occ : List Bool) : InferenceStep
  | validOfAndLeft (pos : Nat) (occ : List Bool) : InferenceStep
  | validOfAndRight (pos : Nat) (occ : List Bool) : InferenceStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive LCtxStep where
  | validOfIntro1F (pos : Nat) : LCtxStep
  | validOfIntro1H (pos : Nat) : LCtxStep
  | validOfIntros (pos idx : Nat) : LCtxStep
  | validOfRevert (pos : Nat) : LCtxStep
  | validOfReverts (pos : Nat) (idx : Nat) : LCtxStep
  /-- `valid lctx t` => `valid (lctx ++ ex) t` -/
  | validOfAppend (pos : Nat) (ex : List LamSort) : LCtxStep
  /-- `valid lctx t` => `valid (ex ++ lctx) (t.bvarLifts ex.length)` -/
  | validOfPrepend (pos : Nat) (ex : List LamSort) : LCtxStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive NonemptyStep where
  | nonemptyOfAtom (n : Nat) : NonemptyStep
  | nonemptyOfEtom (n : Nat) : NonemptyStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive PrepConvStep where
  /-- (a ≠ b) ↔ (a = (¬ b)) -/
  | validOfPropNeEquivEqNot : PrepConvStep
  /-- (True = False) ↔ False -/
  | validOfTrueEqFalseEquivFalse : PrepConvStep
  /-- (False = True) ↔ False -/
  | validOfFalseEqTrueEquivFalse : PrepConvStep
  /-- (a = True) ↔ a -/
  | validOfEqTrueEquiv : PrepConvStep
  /-- (a = False) ↔ (¬ a) -/
  | validOfEqFalseEquiv : PrepConvStep
  /-- (a ≠ True) ↔ (a = False) -/
  | validOfNeTrueEquivEqFalse : PrepConvStep
  /-- (a ≠ False) ↔ (a = True) -/
  | validOfNeFalseEquivEqTrue : PrepConvStep
  /-- ((¬ a) = True) ↔ (a = False) -/
  | validOfNotEqTrueEquivEqFalse : PrepConvStep
  /-- ((¬ a) = False) ↔ (a = True) -/
  | validOfNotEqFalseEquivEqTrue : PrepConvStep
  /-- (¬¬a) ↔ a -/
  | validOfNotNotEquiv : PrepConvStep
  /-- ((¬ a) = b) ↔ (a = (¬ b)) -/
  | validOfNotEqEquivEqNot : PrepConvStep
  /-- ((¬ a) = (¬ b)) ↔ (a = b) -/
  | validOfNotEqNotEquivEq : PrepConvStep
  /-- (a ↔ b) ↔ (a = b) -/
  | validOfPropext : PrepConvStep
  /-- (¬ (a ∧ b)) ↔ (¬ a ∨ ¬ b) -/
  | validOfNotAndEquivNotOrNot : PrepConvStep
  /-- (¬ (a ∨ b)) ↔ (¬ a ∧ ¬ b) -/
  | validOfNotOrEquivNotAndNot : PrepConvStep
  /-- (a → b) ↔ (¬ a ∨ b) -/
  | validOfImpEquivNotOr : PrepConvStep
  /-- (¬ (a → b)) ↔ (a ∧ ¬ b) -/
  | validOfNotImpEquivAndNot : PrepConvStep
  /-- (a = b) ↔ (a ∨ ¬ b) ∧ (¬ a ∨ b) -/
  | validOfPropEq : PrepConvStep
  /-- (a = b) ↔ (a ∨ b) ∧ (¬ a ∨ ¬ b) -/
  | validOfPropNe : PrepConvStep
  /-- Basic BitVec simplification operations -/
  | validOfPushBVCast : PrepConvStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive WFStep where
  | wfOfCheck (lctx : List LamSort) (t : LamTerm) : WFStep
  /-- `wf lctx s t` => `wf (lctx ++ ex) s t` -/
  | wfOfAppend (pos : Nat) (ex : List LamSort) : WFStep
  /-- `wf lctx s t` => `wf (ex ++ lctx) s (t.bvarLifts ex.length)` -/
  | wfOfPrepend (pos : Nat) (ex : List LamSort) : WFStep
  | wfOfHeadBeta (pos : Nat) : WFStep
  | wfOfBetaBounded (pos : Nat) (bound : Nat) : WFStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr

inductive ChkStep where
  | c : ConvStep → ChkStep
  | ca : ConvAtStep → ChkStep
  | e : EtomStep → ChkStep
  | f : FactStep → ChkStep
  | i : InferenceStep → ChkStep
  | l : LCtxStep → ChkStep
  | n : NonemptyStep → ChkStep
  | p : PrepConvStep → Nat → List Bool → ChkStep
  | w : WFStep → ChkStep
  deriving Inhabited, Hashable, BEq, Lean.ToExpr


section ChkStepToString

  def ConvStep.toString : ConvStep → String
  | .validOfHeadBeta pos => s!"validOfHeadBeta {pos}"
  | .validOfBetaBounded pos bound => s!"validOfBetaBounded {pos} {bound}"
  | .validOfExtensionalize pos => s!"validOfExtensionalize {pos}"
  | .validOfEqSymm pos => s!"validOfEqSymm {pos}"
  | .validOfMp pos rw => s!"validOfMp {pos} {rw}"
  | .validOfMpAll pos rw => s!"validOfMpAll {pos} {rw}"
  | .validOfCongrArg pos rw => s!"validOfCongrArg {pos} {rw}"
  | .validOfCongrFun pos rw => s!"validOfCongrFun {pos} {rw}"
  | .validOfCongr pos rwFn rwArg => s!"validOfCongr {pos} {rwFn} {rwArg}"
  | .validOfCongrArgs pos rws => s!"validOfCongrArgs {pos} {rws}"
  | .validOfCongrFunN pos rwFn n => s!"validOfCongrFunN {pos} {rwFn} {n}"
  | .validOfCongrs pos rwFn rwArgs => s!"validOfCongrs {pos} {rwFn} {rwArgs}"

  def ConvAtStep.toString : ConvAtStep → String
  | .validOfEtaExpand1At pos occ => s!"validOfEtaExpand1At {pos} {occ}"
  | .validOfEtaReduce1At pos occ => s!"validOfEtaReduce1At {pos} {occ}"
  | .validOfEtaExpandNAt pos n occ => s!"validOfEtaExpandNAt {pos} {n} {occ}"
  | .validOfEtaReduceNAt pos n occ => s!"validOfEtaReduceNAt {pos} {n} {occ}"
  | .validOfExtensionalizeEqAt pos occ => s!"validOfExtensionalizeEqAt {pos} {occ}"
  | .validOfExtensionalizeEqFNAt pos n occ => s!"validOfExtensionalizeEqFNAt {pos} {n} {occ}"
  | .validOfIntensionalizeEqAt pos occ => s!"validOfIntensionalizeEqAt {pos} {occ}"

  def EtomStep.toString : EtomStep → String
  | .skolemize pos => s!"skolemize {pos}"
  | .define t => s!"define {t}"

  def FactStep.toString : FactStep → String
  | .boolFacts => s!"boolFacts"
  | .iteSpec s => s!"iteSpec {s}"

  def InferenceStep.toString : InferenceStep → String
  | .validOfBVarLower pv pn => s!"validOfBVarLower {pv} {pn}"
  | .validOfBVarLowers pv pns => s!"validOfBVarLowers {pv} {pns}"
  | .validOfImp p₁₂ p₁ => s!"validOfImp {p₁₂} {p₁}"
  | .validOfImps imp ps => s!"validOfImps {imp} {ps}"
  | .validOfInstantiate1 pos arg => s!"validOfInstantiate1 {pos} {arg}"
  | .validOfInstantiate pos args => s!"validOfInstantiate {pos} {args}"
  | .validOfInstantiateRev pos args => s!"validOfInstantiateRev {pos} {args}"
  | .validOfEqualize pos occ => s!"validOfEqualize {pos} {occ}"
  | .validOfAndLeft pos occ => s!"validOfAndLeft {pos} {occ}"
  | .validOfAndRight pos occ => s!"validOfAndRight {pos} {occ}"

  def LCtxStep.toString : LCtxStep → String
  | .validOfIntro1F pos => s!"validOfIntro1F {pos}"
  | .validOfIntro1H pos => s!"validOfIntro1H {pos}"
  | .validOfIntros pos idx => s!"validOfIntros {pos} {idx}"
  | .validOfRevert pos => s!"validOfRevert {pos}"
  | .validOfReverts pos idx => s!"validOfReverts {pos} {idx}"
  | .validOfAppend pos ex => s!"validOfAppend {pos} {ex}"
  | .validOfPrepend pos ex => s!"validOfPrepend {pos} {ex}"

  def NonemptyStep.toString : NonemptyStep → String
  | .nonemptyOfAtom n => s!"nonemptyOfAtom {n}"
  | .nonemptyOfEtom n => s!"nonemptyOfEtom {n}"

  def PrepConvStep.toString : PrepConvStep → String
  | .validOfPropNeEquivEqNot => s!"validOfPropNeEquivEqNot"
  | .validOfTrueEqFalseEquivFalse => s!"validOfTrueEqFalseEquivFalse"
  | .validOfFalseEqTrueEquivFalse => s!"validOfFalseEqTrueEquivFalse"
  | .validOfEqTrueEquiv => s!"validOfEqTrueEquiv"
  | .validOfEqFalseEquiv => s!"validOfEqFalseEquiv"
  | .validOfNeTrueEquivEqFalse => s!"validOfNeTrueEquivEqFalse"
  | .validOfNeFalseEquivEqTrue => s!"validOfNeFalseEquivEqTrue"
  | .validOfNotEqTrueEquivEqFalse => s!"validOfNotEqTrueEquivEqFalse"
  | .validOfNotEqFalseEquivEqTrue => s!"validOfNotEqFalseEquivEqTrue"
  | .validOfNotNotEquiv => s!"validOfNotNotEquiv"
  | .validOfNotEqEquivEqNot => s!"validOfNotEqEquivEqNot"
  | .validOfNotEqNotEquivEq => s!"validOfNotEqNotEquivEq"
  | .validOfPropext => s!"validOfPropext"
  | .validOfNotAndEquivNotOrNot => s!"validOfNotAndEquivNotOrNot"
  | .validOfNotOrEquivNotAndNot => s!"validOfNotOrEquivNotAndNot"
  | .validOfImpEquivNotOr => s!"validOfImpEquivNotOr"
  | .validOfNotImpEquivAndNot => s!"validOfNotImpEquivAndNot"
  | .validOfPropEq => s!"validOfPropEq"
  | .validOfPropNe => s!"validOfPropNe"
  | .validOfPushBVCast => s!"validOfPushBVCast"

  def WFStep.toString : WFStep → String
  | .wfOfCheck lctx t => s!"wfOfCheck {lctx} {t}"
  | .wfOfAppend pos ex => s!"wfOfAppend {pos} {ex}"
  | .wfOfPrepend pos ex => s!"wfOfPrepend {pos} {ex}"
  | .wfOfHeadBeta pos => s!"wfOfHeadBeta {pos}"
  | .wfOfBetaBounded pos bound => s!"wfOfBetaBounded {pos} {bound}"

  def ChkStep.toString : ChkStep → String
  | .c s  => ConvStep.toString s
  | .ca s => ConvAtStep.toString s
  | .e s  => EtomStep.toString s
  | .f s  => FactStep.toString s
  | .i s  => InferenceStep.toString s
  | .l s  => LCtxStep.toString s
  | .n s  => NonemptyStep.toString s
  | .p s pos occ => s!"{PrepConvStep.toString s} {pos} {occ}"
  | .w s  => WFStep.toString s

  instance : ToString ChkStep where
    toString := ChkStep.toString

end ChkStepToString


section ChkStepPremises

  def ConvStep.premises : ConvStep → List Nat
  | .validOfHeadBeta pos => [pos]
  | .validOfBetaBounded pos _ => [pos]
  | .validOfExtensionalize pos => [pos]
  | .validOfEqSymm pos => [pos]
  | .validOfMp pos rw => [pos, rw]
  | .validOfMpAll pos rw => [pos, rw]
  | .validOfCongrArg pos rw => [pos, rw]
  | .validOfCongrFun pos rw => [pos, rw]
  | .validOfCongr pos rwFn rwArg => [pos, rwFn, rwArg]
  | .validOfCongrArgs pos rws => pos :: rws
  | .validOfCongrFunN pos rwFn _ => [pos, rwFn]
  | .validOfCongrs pos rwFn rwArgs => pos :: rwFn :: rwArgs

  def ConvAtStep.premises : ConvAtStep → List Nat
  | .validOfEtaExpand1At pos _ => [pos]
  | .validOfEtaReduce1At pos _ => [pos]
  | .validOfEtaExpandNAt pos _ _ => [pos]
  | .validOfEtaReduceNAt pos _ _ => [pos]
  | .validOfExtensionalizeEqAt pos _ => [pos]
  | .validOfExtensionalizeEqFNAt pos _ _ => [pos]
  | .validOfIntensionalizeEqAt pos _ => [pos]

  def EtomStep.premises : EtomStep → List Nat
  | .skolemize pos => [pos]
  | .define _ => []

  def FactStep.premises : FactStep → List Nat
  | .boolFacts => []
  | .iteSpec _ => []

  def InferenceStep.premises : InferenceStep → List Nat
  | .validOfBVarLower pv pn => [pv, pn]
  | .validOfBVarLowers pv pns => pv :: pns
  | .validOfImp p₁₂ p₁ => [p₁₂, p₁]
  | .validOfImps imp ps => imp :: ps
  | .validOfInstantiate1 pos _ => [pos]
  | .validOfInstantiate pos _ => [pos]
  | .validOfInstantiateRev pos _ => [pos]
  | .validOfEqualize pos _ => [pos]
  | .validOfAndLeft pos _ => [pos]
  | .validOfAndRight pos _ => [pos]

  def LCtxStep.premises : LCtxStep → List Nat
  | .validOfIntro1F pos => [pos]
  | .validOfIntro1H pos => [pos]
  | .validOfIntros pos _ => [pos]
  | .validOfRevert pos => [pos]
  | .validOfReverts pos _ => [pos]
  | .validOfAppend pos _ => [pos]
  | .validOfPrepend pos _ => [pos]

  def NonemptyStep.premises : NonemptyStep → List Nat
  | .nonemptyOfAtom _ => []
  | .nonemptyOfEtom _ => []

  /--
    Whether a term is well-formed or not does not depend
      on assertions. So, the premises of a WFStep is
      deemed empty (although for some `WFStep`s they seem
      to have premise syntactically)
  -/
  def WFStep.premises (_ : WFStep) : List Nat := []

  def ChkStep.premises : ChkStep → List Nat
  | .c s  => ConvStep.premises s
  | .ca s => ConvAtStep.premises s
  | .e s  => EtomStep.premises s
  | .f s  => FactStep.premises s
  | .i s  => InferenceStep.premises s
  | .l s  => LCtxStep.premises s
  | .n s  => NonemptyStep.premises s
  | .p _ pos _ => [pos]
  | .w s  => WFStep.premises s

end ChkStepPremises


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

def LCtxStep.evalValidOfIntros (lctx : List LamSort) (t : LamTerm)
  : (idx : Nat) → EvalResult
  | 0 => .addEntry (.valid lctx t)
  | .succ idx =>
    match t.intro1? with
    | .some (s, t') => evalValidOfIntros (s :: lctx) t' idx
    | .none => .fail

def LCtxStep.evalValidOfReverts (lctx : List LamSort) (t : LamTerm)
  : (idx : Nat) → EvalResult
  | 0 => .addEntry (.valid lctx t)
  | .succ idx =>
    match lctx with
    | .nil => .fail
    | .cons s lctx => evalValidOfReverts lctx (.mkForallEF s t) idx

def InferenceStep.evalValidOfInstantiate (n : Nat) (ltv : LamTyVal) (lctx : List LamSort) (t : LamTerm)
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

def InferenceStep.evalValidOfBVarLowers (r : RTable) (lctx : List LamSort) (pns : List Nat) : Option (List LamSort) :=
  match pns with
  | .nil => .some lctx
  | .cons pn pns' =>
    match r.getNonempty pn with
    | .none => .none
    | .some s =>
      match lctx with
      | .nil => .none
      | .cons s' lctx' =>
        match s.beq s' with
        | false => .none
        | true => evalValidOfBVarLowers r lctx' pns'

@[reducible] def ConvStep.eval (r : RTable) : (cs : ConvStep) → EvalResult
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
| .validOfEqSymm pos =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match t.eqSymm? with
    | .some t' => .addEntry (REntry.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfMp pos rw =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx lctx rw with
    | .some rw =>
      match LamTerm.mp? rw t with
      | .some t' => .addEntry (REntry.valid lctx t')
      | .none => .fail
    | .none => .fail
  | .none => .fail
| .validOfMpAll pos rw =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match r.getValidEnsureLCtx [] rw with
    | .some rw =>
      match LamTerm.mpAll? rw t with
      | .some t' => .addEntry (REntry.valid lctx t')
      | .none => .fail
    | .none => .fail
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

@[reducible] def ConvAtStep.eval (r : RTable) : (cs : ConvAtStep) → EvalResult
| .validOfEtaExpand1At pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAtWith occ LamTerm.etaExpand1? (.base .prop) t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfEtaReduce1At pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAt occ LamTerm.etaReduce1? t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfEtaExpandNAt pos n occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAtWith occ (LamTerm.etaExpandN? n) (.base .prop) t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfEtaReduceNAt pos n occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAt occ (LamTerm.etaReduceN? n) t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfExtensionalizeEqAt pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAt occ (fun t => LamTerm.extensionalizeEq t) t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfExtensionalizeEqFNAt pos n occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAt occ (LamTerm.extensionalizeEq?FN? n) t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfIntensionalizeEqAt pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAt occ LamTerm.intensionalizeEq? t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail

@[reducible] def EtomStep.eval (lvt lit : Nat → LamSort) (r : RTable) : (cs : EtomStep) → EvalResult
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

@[reducible] def FactStep.eval : (cs : FactStep) → EvalResult
| .boolFacts => .addEntry (.valid [] LamTerm.boolFacts)
| .iteSpec s => .addEntry (.valid [] (LamTerm.iteSpec s))

@[reducible] def InferenceStep.eval (lvt lit : Nat → LamSort) (r : RTable) : (cs : InferenceStep) → EvalResult
| .validOfBVarLower pv pn =>
  match r.getValid pv with
  | .some (lctx, t) =>
    match r.getNonempty pn with
    | .none => .fail
    | .some s =>
      match lctx with
      | .nil => .fail
      | .cons s' lctx' =>
        match s.beq s', LamTerm.bvarLower? t with
        | true, .some t' => .addEntry (.valid lctx' t')
        | _, _ => .fail
  | .none => .fail
| .validOfBVarLowers pv pns =>
  match r.getValid pv with
  | .some (lctx, t) =>
    match t.bvarLowers? pns.length with
    | .some t' =>
      match evalValidOfBVarLowers r lctx pns with
      | .some lctx' => .addEntry (.valid lctx' t')
      | .none => .fail
    | .none => .fail
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
| .validOfEqualize pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAtWith occ LamTerm.equalize? (.base .prop) t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfAndLeft pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAtIfSign true occ LamTerm.andLeft? t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .validOfAndRight pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAtIfSign true occ LamTerm.andRight? t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail

@[reducible] def LCtxStep.eval (r : RTable) : (cs : LCtxStep) → EvalResult
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
| .validOfAppend pos ex =>
  match r.getValid pos with
  | .some (lctx, t) => .addEntry (.valid (lctx ++ ex) t)
  | .none => .fail
| .validOfPrepend pos ex =>
  match r.getValid pos with
  | .some (lctx, t) => .addEntry (.valid (ex ++ lctx) (t.bvarLifts ex.length))
  | .none => .fail

@[reducible] def NonemptyStep.eval (lvt : Nat → LamSort) (r : RTable) : (cs : NonemptyStep) → EvalResult
| .nonemptyOfAtom n => .addEntry (.nonempty (lvt n))
| .nonemptyOfEtom n =>
  match r.maxEVarSucc.ble n with
  | true => .fail
  | false => .addEntry (.nonempty ((r.lamEVarTy.get? n).getD (.base .prop)))

@[reducible] def PrepConvStep.eval : (cs : PrepConvStep) → LamTerm → Option LamTerm
| .validOfPropNeEquivEqNot => LamTerm.prop_ne_equiv_eq_not?
| .validOfTrueEqFalseEquivFalse => LamTerm.true_eq_false_equiv_false?
| .validOfFalseEqTrueEquivFalse => LamTerm.false_eq_true_equiv_false?
| .validOfEqTrueEquiv => LamTerm.eq_true_equiv?
| .validOfEqFalseEquiv => LamTerm.eq_false_equiv?
| .validOfNeTrueEquivEqFalse => LamTerm.ne_true_equiv_eq_false?
| .validOfNeFalseEquivEqTrue => LamTerm.ne_false_equiv_eq_true?
| .validOfNotEqTrueEquivEqFalse => LamTerm.not_eq_true_equiv_eq_false?
| .validOfNotEqFalseEquivEqTrue => LamTerm.not_eq_false_equiv_eq_true?
| .validOfNotNotEquiv => LamTerm.not_not_equiv?
| .validOfNotEqEquivEqNot => LamTerm.not_eq_equiv_eq_not?
| .validOfNotEqNotEquivEq => LamTerm.not_eq_not_equiv_eq?
| .validOfPropext => LamTerm.propext?
| .validOfNotAndEquivNotOrNot => LamTerm.not_and_equiv_not_or_not?
| .validOfNotOrEquivNotAndNot => LamTerm.not_or_equiv_not_and_not?
| .validOfImpEquivNotOr => LamTerm.imp_equiv_not_or?
| .validOfNotImpEquivAndNot => LamTerm.not_imp_equiv_and_not?
| .validOfPropEq => LamTerm.propeq?
| .validOfPropNe => LamTerm.propne?
| .validOfPushBVCast => fun t => LamTerm.pushBVCast .none t

@[reducible] def WFStep.eval (lvt lit : Nat → LamSort) (r : RTable) : (cs : WFStep) → EvalResult
| .wfOfCheck lctx t =>
  match LamTerm.lamThmWFCheck? ⟨lvt, lit, r.toLamEVarTy⟩ lctx t with
  | .some rty =>
    match Nat.ble t.maxEVarSucc r.maxEVarSucc with
    | true => .addEntry (.wf lctx rty t)
    | false => .fail
  | .none => .fail
| .wfOfAppend pos ex =>
  match r.getWF pos with
  | .some (lctx, s, t) => .addEntry (.wf (lctx ++ ex) s t)
  | .none => .fail
| .wfOfPrepend pos ex =>
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

def ChkStep.eval (lvt lit : Nat → LamSort) (r : RTable) : (cs : ChkStep) → EvalResult
| .c s  => ConvStep.eval r s
| .ca s => ConvAtStep.eval r s
| .e s  => EtomStep.eval lvt lit r s
| .f s  => FactStep.eval s
| .i s  => InferenceStep.eval lvt lit r s
| .l s  => LCtxStep.eval r s
| .n s  => NonemptyStep.eval lvt r s
| .p s pos occ =>
  match r.getValid pos with
  | .some (lctx, t) =>
    match LamTerm.rwGenAt occ s.eval t with
    | .some t' => .addEntry (.valid lctx t')
    | .none => .fail
  | .none => .fail
| .w s  => WFStep.eval lvt lit r s

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

theorem LCtxStep.evalValidOfIntros_correct
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

theorem LCtxStep.evalValidOfReverts_correct
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

theorem InferenceStep.evalValidOfBVarLowers_correct
  {r : RTable} (cv : CVal.{u} r.lamEVarTy) (inv : RTable.inv r cv)
  (heq : evalValidOfBVarLowers r lctx pns = .some lctx') :
  ∃ (ss : _) (_ : HList (LamNonempty cv.tyVal) ss),
    ss.length = pns.length ∧ lctx = ss ++ lctx' := by
  induction pns generalizing lctx
  case nil =>
    unfold evalValidOfBVarLowers at heq; cases heq; exists .nil, .nil;
  case cons pn pns' IH =>
    unfold evalValidOfBVarLowers at heq; revert heq
    match h₁ : r.getNonempty pn with
    | .none => intro h; cases h
    | .some s =>
      dsimp
      match lctx with
      | .nil => intro h; cases h
      | .cons s' lctx'' =>
        dsimp
        match h₂ : LamSort.beq s s' with
        | true =>
          have h₁' := RTable.getNonempty_correct inv h₁
          cases (LamSort.eq_of_beq_eq_true h₂); dsimp
          intro eeq; have ⟨ss, hInh, pneq, sseq⟩ := IH eeq
          exists .cons s ss, .cons h₁' hInh; simp [pneq, sseq]
        | false => intro h; cases h

theorem InferenceStep.evalValidOfInstantiate_correct
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
            apply Nat.le_trans (LamTerm.maxEVarSucc_instantiateAt_le)
            rw [Nat.max_le]; apply And.intro _ eS; apply Nat.le_of_ble_eq_true h₃
          | false => exact True.intro
        | false => exact True.intro
      | .none => exact True.intro

theorem ConvStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : ConvStep) → EvalResult.correct r cv (cs.eval r)
| .validOfHeadBeta pos => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.eval_correct_validAux h'
      case vimp =>
        intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
        intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
        intro hv; apply LamThmValid.mpLamThmEquiv _ hv
        apply LamThmEquiv.ofExtensionalize (LamThmWF.ofLamThmValid hv)
      case condimp =>
        intro hcond; rw [LamTerm.maxEVarSucc_extensionalizeAux]; exact hcond
| .validOfEqSymm pos => by
  dsimp [eval]
  cases h₁ : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      dsimp
      match h₂ : t.eqSymm? with
      | .some t' =>
        have h' := RTable.getValid_correct inv h₁
        apply ChkStep.eval_correct_validAux h'
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
          apply LamThmEquiv.eqSymm? (LamThmWF.ofLamThmValid hv) h₂
        case condimp =>
          intro hcond; rw [LamTerm.maxEVarSucc_eqSymm? h₂]; exact hcond
      | .none => exact True.intro
| .validOfMp pos rw => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrw : r.getValidEnsureLCtx lctx rw with
    | .some rwt =>
      dsimp
      match hmp : LamTerm.mp? rwt t with
      | .some t' =>
        have hpos' := RTable.getValid_correct inv hpos
        have hrw' := RTable.getValidEnsureLCtx_correct inv hrw
        apply ChkStep.eval_correct_validAux hpos'
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
          apply LamThmEquiv.mp? (LamThmWF.ofLamThmValid hv) hrw'.left hmp
        case condimp =>
          intro _; apply Nat.le_trans _ hrw'.right
          apply LamTerm.maxEVarSucc_mp? hmp
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfMpAll pos rw => by
  dsimp [eval]
  match hpos : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match hrw : r.getValidEnsureLCtx [] rw with
    | .some rwt =>
      dsimp
      match hmp : LamTerm.mpAll? rwt t with
      | .some t' =>
        have hpos' := RTable.getValid_correct inv hpos
        have hrw' := RTable.getValidEnsureLCtx_correct inv hrw
        apply ChkStep.eval_correct_validAux hpos'
        case vimp =>
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
          intro lctx'; have ⟨hwf, _⟩ := hpos'.left lctx'
          apply LamGenConv.mpAll? hrw'.left _ _ hmp _ _ hwf
        case condimp =>
          intro _; apply Nat.le_trans (LamTerm.evarBounded_mpAll? _ _ hmp)
          apply Nat.max_le.mpr (And.intro hrw'.right hpos'.right)
      | .none => exact True.intro
    | .none => exact True.intro
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
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
            intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
          intro hv; apply LamThmValid.mpLamThmEquiv _ hv
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
            intro hv; apply LamThmValid.mpLamThmEquiv _ hv
            have hrwArgs' := HList.map (fun _ h => And.left h) hrwArgs
            apply LamThmEquiv.congrs? (LamThmWF.ofLamThmValid hv) hrwFn.left hrwArgs' hcongr
          case condimp =>
            have hrwArgs' := HList.map (fun _ h => And.right h) hrwArgs
            intro cond; apply LamTerm.maxEVarSucc_congrs? cond hrwFn.right hrwArgs' hcongr
        | .none => exact True.intro
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro

theorem EtomStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : EtomStep) → EvalResult.correct r cv (cs.eval cv.toLamVarTy cv.toLamILTy r)
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
          -- Note how the result of `dsimp` remains seemingly unchanged while `rw` fails when we remove `levt'`
          intro n hlt; dsimp [levt', replaceAt, replaceAtDep]
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
          -- Note how the result of `dsimp` remains seemingly unchanged while `rw` fails when we remove `levt'`
          intro n hlt; dsimp [levt', replaceAt, replaceAtDep]
          rw [Nat.beq_eq_false_of_ne (Nat.ne_of_lt hlt)]
        case right =>
          rw [LamTerm.maxEVarSucc_mkEq]; dsimp [LamTerm.maxEVarSucc]
          rw [Nat.max_le]; apply And.intro (Nat.le_refl _) (Nat.le_step h₂')
    | false => exact True.intro
  | .none => exact True.intro

theorem FactStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy):
  (cs : FactStep) → EvalResult.correct r cv cs.eval
| .boolFacts => by
  dsimp [eval]; apply And.intro LamThmValid.boolFacts
  rw [LamTerm.maxEVarSucc_boolFacts]; apply Nat.zero_le
| .iteSpec s => by
  dsimp [eval]; apply And.intro (LamThmValid.iteSpec _)
  rw [LamTerm.maxEVarSucc_iteSpec]; apply Nat.zero_le

theorem InferenceStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : InferenceStep) → EvalResult.correct r cv (cs.eval cv.toLamVarTy cv.toLamILTy r)
| .validOfBVarLower pv pn => by
  dsimp [eval]
  match h₁ : r.getValid pv with
  | .some (lctx, t) =>
    dsimp; have h₁' := RTable.getValid_correct inv h₁
    match h₂ : r.getNonempty pn with
    | .some s =>
      dsimp; have h₂' := RTable.getNonempty_correct inv h₂
      match lctx with
      | .nil => exact True.intro
      | .cons s' lctx =>
        dsimp
        match h₃ : s.beq s', h₄ : t.bvarLower? with
        | true, .some t' =>
          cases LamSort.eq_of_beq_eq_true h₃
          apply ChkStep.eval_correct_validAux h₁'
          case vimp =>
            intro hv; apply LamThmValid.bvarLower? (lval:=cv.toLamValuation) hv h₄ h₂'
          case condimp =>
            intro hcond; rw [LamTerm.maxEVarSucc_bvarLower? h₄]; exact hcond
        | true, .none => exact True.intro
        | false, _ => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfBVarLowers pv pns => by
  dsimp [eval]
  match h₁ : r.getValid pv with
  | .some (lctx, t) =>
    dsimp; have h₁' := RTable.getValid_correct inv h₁
    match h₂ : LamTerm.bvarLowers? (List.length pns) t with
    | .some t' =>
      dsimp
      match h₃ : evalValidOfBVarLowers r lctx pns with
      | .some lctx' =>
        apply ChkStep.eval_correct_validAux h₁'
        case vimp =>
          have ⟨ss, hInh, pneq, sseq⟩ := evalValidOfBVarLowers_correct cv inv h₃
          intro hv; apply LamThmValid.bvarLowers? (lval:=cv.toLamValuation) (ss:=ss) _ pneq h₂ hInh
          rw [← sseq]; exact hv
        case condimp =>
          intro hcond; rw [LamTerm.maxEVarSucc_bvarLowers? h₂]; exact hcond
      | .none => exact True.intro
    | .none => exact True.intro
  | .none => exact True.intro
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
          intro _; apply LamThmValid.impApps himp.left hps' hap
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
              intro cond; apply Nat.le_trans LamTerm.maxEVarSucc_instantiate1_le
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
    apply evalValidOfInstantiate_correct _ h'
  | .none => exact True.intro
| .validOfInstantiateRev pos args => by
  dsimp [eval]
  match h : r.getValid pos with
  | .some (lctx, t) =>
    let h' := RTable.getValid_correct inv h
    apply evalValidOfInstantiate_correct _ h'
  | .none => exact True.intro
| .validOfEqualize pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAtWith occ LamTerm.equalize? (.base .prop) t with
    | .some t' =>
      dsimp; have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'
        have hv' := hv lctx'; apply LamValid.mpLamEquiv hv'
        apply LamGenConvWith.rwGenAtWith LamGenConv.equalize? _ _ _ h₂
        apply LamThmWF.ofLamThmValid hv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAtWith @LamTerm.maxEVarSucc_equalize? _ _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfAndLeft pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAtIfSign true occ LamTerm.andLeft? t with
    | .some t' =>
      dsimp; have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'
        have hv' := hv lctx'; revert hv'; apply LamValid.impLift
        apply LamGenModify.rwGenAtIfSign (weaken?':=true) LamGenModify.andLeft? _ _ h₂
        apply LamThmWF.ofLamThmValid hv
      case condimp =>
        intro hcond; apply Nat.le_trans (Nat.le_trans (m:=max 0 t.maxEVarSucc) _ _) hcond
        apply LamTerm.evarBounded_rwGenAtIfSign LamTerm.evarBounded_andLeft? _ _ h₂
        rw [Nat.max_zero_left]; apply Nat.le_refl
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfAndRight pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAtIfSign true occ LamTerm.andRight? t with
    | .some t' =>
      dsimp; have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'
        have hv' := hv lctx'; revert hv'; apply LamValid.impLift
        apply LamGenModify.rwGenAtIfSign (weaken?':=true) LamGenModify.andRight? _ _ h₂
        apply LamThmWF.ofLamThmValid hv
      case condimp =>
        intro hcond; apply Nat.le_trans (Nat.le_trans (m:=max 0 t.maxEVarSucc) _ _) hcond
        apply LamTerm.evarBounded_rwGenAtIfSign LamTerm.evarBounded_andRight? _ _ h₂
        rw [Nat.max_zero_left]; apply Nat.le_refl
    | .none => exact True.intro
  | .none => exact True.intro

theorem ConvAtStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : ConvAtStep) → EvalResult.correct r cv (cs.eval r)
| .validOfEtaExpand1At pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAtWith occ LamTerm.etaExpand1? (.base .prop) t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConvWith.rwGenAtWith LamGenConvWith.etaExpand1? _ _ _ h₂ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAtWith (fun s => @LamTerm.maxEVarSucc_etaExpand1? s) _ _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfEtaReduce1At pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAt occ LamTerm.etaReduce1? t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConv.rwGenAt LamGenConv.etaReduce1? _ _ h₂ _ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAt @LamTerm.maxEVarSucc_etaReduce1? _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfEtaExpandNAt pos n occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAtWith occ (LamTerm.etaExpandN? n) (.base .prop) t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConvWith.rwGenAtWith LamGenConvWith.etaExpandN? _ _ _ h₂ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAtWith (fun s t₁ t₂ heq => by
          apply LamTerm.maxEVarSucc_etaExpandN? heq) _ _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfEtaReduceNAt pos n occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAt occ (LamTerm.etaReduceN? n) t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConv.rwGenAt LamGenConv.etaReduceN? _ _ h₂ _ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAt (fun t₁ t₂ heq => by
          apply LamTerm.maxEVarSucc_etaReduceN? heq) _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfExtensionalizeEqAt pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAt occ (fun t => LamTerm.extensionalizeEq t) t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConv.rwGenAt LamGenConv.ofExtensionalizeEq _ _ h₂ _ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        have eveq : LamTerm.evarEquiv fun t => some (LamTerm.extensionalizeEq t) := by
          intro t t' h; cases h; apply LamTerm.maxEVarSucc_extensionalizeEq
        rw [LamTerm.evarEquiv_rwGenAt eveq _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfExtensionalizeEqFNAt pos n occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAt occ (LamTerm.extensionalizeEq?FN? n) t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConv.rwGenAt LamGenConv.ofExtensionalizeEq?FN? _ _ h₂ _ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAt (@LamTerm.maxEVarSucc_extensionalizeEq?FN? n) _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro
| .validOfIntensionalizeEqAt pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAt occ LamTerm.intensionalizeEq? t with
    | .some t' =>
      dsimp
      have h₁' := RTable.getValid_correct inv h₁
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        intro hv lctx'; have ⟨wft, _⟩ := hv lctx'
        have hequiv := LamGenConv.rwGenAt LamGenConv.ofIntensionalizeEq? _ _ h₂ _ _ wft
        apply LamValid.mpLamEquiv (hv _) hequiv
      case condimp =>
        intro hcond
        rw [LamTerm.evarEquiv_rwGenAt @LamTerm.maxEVarSucc_intensionalizeEq? _ _ h₂]
        exact hcond
    | .none => exact True.intro
  | .none => exact True.intro

theorem LCtxStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : LCtxStep) → EvalResult.correct r cv (cs.eval r)
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
      have hcorrect := evalValidOfIntros_correct (idx:=idx) _ h'
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
      apply evalValidOfReverts_correct _ h'
| .validOfAppend pos ex => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.eval_correct_validAux h'
      case vimp => intro hv; apply LamThmValid.append; exact hv
      case condimp => exact id
| .validOfPrepend pos ex => by
  dsimp [eval]
  cases h : r.getValid pos <;> try exact True.intro
  case some lctxt =>
    match lctxt with
    | (lctx, t) =>
      have h' := RTable.getValid_correct inv h
      apply ChkStep.eval_correct_validAux h'
      case vimp => intro hv; apply LamThmValid.prepend; exact hv
      case condimp => intro hcond; rw [LamTerm.maxEVarSucc_bvarLifts]; exact hcond

theorem NonemptyStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) :
  (cs : NonemptyStep) → EvalResult.correct r cv (cs.eval cv.toLamVarTy r)
| .nonemptyOfAtom n => by
  dsimp [eval, EvalResult.correct, REntry.correct]
  apply Nonempty.intro; exact cv.toLamValuation.varVal n
| .nonemptyOfEtom n => by
  dsimp [eval]
  match Nat.ble r.maxEVarSucc n with
  | true => exact True.intro
  | false =>
    dsimp [EvalResult.correct, REntry.correct]
    apply Nonempty.intro; exact cv.toLamValuation.eVarVal n

theorem PrepConvStep.eval_correct (lval : LamValuation) :
  (cs : PrepConvStep) → LamGenConv lval cs.eval ∧ LamTerm.evarBounded cs.eval 0
| .validOfPropNeEquivEqNot => And.intro
  LamGenConv.prop_ne_equiv_eq_not?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_prop_ne_equiv_eq_not?)
| .validOfTrueEqFalseEquivFalse => And.intro
  LamGenConv.true_eq_false_equiv_false?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_true_eq_false_equiv_false?)
| .validOfFalseEqTrueEquivFalse => And.intro
  LamGenConv.false_eq_true_equiv_false?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_false_eq_true_equiv_false?)
| .validOfEqTrueEquiv => And.intro
  LamGenConv.eq_true_equiv?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_eq_true_equiv?)
| .validOfEqFalseEquiv => And.intro
  LamGenConv.eq_false_equiv?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_eq_false_equiv?)
| .validOfNeTrueEquivEqFalse => And.intro
  LamGenConv.ne_true_equiv_eq_false?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_ne_true_equiv_eq_false?)
| .validOfNeFalseEquivEqTrue => And.intro
  LamGenConv.ne_false_equiv_eq_true?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_ne_false_equiv_eq_true?)
| .validOfNotEqTrueEquivEqFalse => And.intro
  LamGenConv.not_eq_true_equiv_eq_false?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_eq_true_equiv_eq_false?)
| .validOfNotEqFalseEquivEqTrue => And.intro
  LamGenConv.not_eq_false_equiv_eq_true?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_eq_false_equiv_eq_true?)
| .validOfNotNotEquiv => And.intro
  LamGenConv.not_not_equiv?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_not_equiv?)
| .validOfNotEqEquivEqNot => And.intro
  LamGenConv.not_eq_equiv_eq_not?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_eq_equiv_eq_not?)
| .validOfNotEqNotEquivEq => And.intro
  LamGenConv.not_eq_not_equiv_eq?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_eq_not_equiv_eq?)
| .validOfPropext => And.intro
  LamGenConv.propext?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_propext?)
| .validOfNotAndEquivNotOrNot => And.intro
  LamGenConv.not_and_equiv_not_or_not?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_and_equiv_not_or_not?)
| .validOfNotOrEquivNotAndNot => And.intro
  LamGenConv.not_or_equiv_not_and_not?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_or_equiv_not_and_not?)
| .validOfImpEquivNotOr => And.intro
  LamGenConv.imp_equiv_not_or?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_imp_equiv_not_or?)
| .validOfNotImpEquivAndNot => And.intro
  LamGenConv.not_imp_equiv_and_not?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_not_imp_equiv_and_not?)
| .validOfPropEq => And.intro
  LamGenConv.propeq?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_propeq?)
| .validOfPropNe => And.intro
  LamGenConv.propne?
  (LamTerm.evarBounded_of_evarEquiv @LamTerm.maxEVarSucc_propne?)
| .validOfPushBVCast => And.intro
  LamGenConv.pushBVCast
  (LamTerm.evarBounded_of_evarEquiv LamTerm.evarEquiv_pushBVCast)

theorem WFStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : WFStep) → EvalResult.correct r cv (cs.eval cv.toLamVarTy cv.toLamILTy r)
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
| .wfOfAppend pos ex => by
  dsimp [eval]
  cases h : r.getWF pos <;> try exact True.intro
  case some lctxst =>
    match lctxst with
    | (lctx, s, t) =>
      have h' := RTable.getWF_correct inv h
      apply ChkStep.eval_correct_wfAux h' _ id
      intro hwf; apply LamThmWF.append hwf
| .wfOfPrepend pos ex => by
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

theorem ChkStep.eval_correct
  (r : RTable) (cv : CVal.{u} r.lamEVarTy) (inv : r.inv cv) :
  (cs : ChkStep) → EvalResult.correct r cv (cs.eval cv.toLamVarTy cv.toLamILTy r)
| .c s  => ConvStep.eval_correct r cv inv s
| .ca s => ConvAtStep.eval_correct r cv inv s
| .e s  => EtomStep.eval_correct r cv inv s
| .f s  => FactStep.eval_correct r cv s
| .i s  => InferenceStep.eval_correct r cv inv s
| .l s  => LCtxStep.eval_correct r cv inv s
| .n s  => NonemptyStep.eval_correct r cv s
| .p s pos occ => by
  dsimp [eval]
  match h₁ : r.getValid pos with
  | .some (lctx, t) =>
    dsimp
    match h₂ : LamTerm.rwGenAt occ s.eval t with
    | .some t' =>
      have h₁' := RTable.getValid_correct inv h₁
      have prep_correct := PrepConvStep.eval_correct cv.toLamValuation s
      apply ChkStep.eval_correct_validAux h₁'
      case vimp =>
        apply LamThmValid.mpLamThmEquiv; intro lctx';
        have ⟨wf, _⟩ := h₁'.left lctx'
        apply LamGenConv.rwGenAt prep_correct.left _ _ h₂ _ _ wf
      case condimp =>
        apply Nat.le_trans
        have h := LamTerm.evarBounded_rwGenAt prep_correct.right _ _ h₂
        rw [Nat.max_zero_left] at h; exact h
    | .none => exact True.intro
  | .none => exact True.intro
| .w s  => WFStep.eval_correct r cv inv s

def RTable.runEvalResult (r : RTable) (n : Nat) : EvalResult → RTable
| .fail => r
| .addEntry e => { r with entries := r.entries.insert n e }
| .newEtomWithValid s lctx t =>
  { r with entries := r.entries.insert n (.valid lctx t),
           lamEVarTy := r.lamEVarTy.insert r.maxEVarSucc s,
           maxEVarSucc := r.maxEVarSucc + 1 }

/--
  The first `ChkStep` specifies the checker step
  The second `Nat` specifies the position to insert the resulting term
  Note that
    1. All entries `(x : ChkStep × Nat)` that insert result into the
       `wf` table should have distinct second component
    2. All entries `(x : ChkStep × Nat)` that insert result into the
       `valid` table should have distinct second component
  Note that we decide where (`wf` or `valid`) to insert the resulting
    term by looking at `(c : ChkStep).eval`
-/
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

/--
  Note : Using this theorem directly in the checker will cause
    performance issue, especially when there are a lot of
    `etom`s. This is probably caused by the type of `eV` in
    `∃ eV` being dependent on the result of `ChkSteps.runFromBeginning`
-/
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

/--
  Note : Do not use the counterpart of this theorem in proof by reflection.
  Surprisingly, if we use this theorem in proof by reflection, the performance
    issue will not be the `ChkSteps.run` in `runEq`. Instead, it would be
    caused by compiling the definition of `runResult`. I'm not sure why it's
    the case, but Lean sometimes exhibit superlinear (even quadratic) compilation
    time with respect to the size of `runResult`.
-/
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
    cases cpv; unfold CPVal.toLamVarTy; apply funext; intro n
    rw [← Option.getD_map (f:=@Sigma.fst LamSort _)]; dsimp
    apply congrFun; apply congrArg; rw [hlvt, BinTree.get?_mapOpt]
    apply Eq.symm; apply Option.map_eq_bind
  have litEq : (fun n => (lit.get? n).getD (.base .prop)) = cpv.toLamILTy := by
    cases cpv; unfold CPVal.toLamILTy; apply funext; intro n
    rw [← Option.getD_map (f:=@Sigma.fst LamSort _)]; dsimp
    apply congrFun; apply congrArg; rw [hlit, BinTree.get?_mapOpt]
    apply Eq.symm; apply Option.map_eq_bind
  rw [lvtEq, litEq] at runEq; cases runEq; apply ChkSteps.run_correct
  unfold RTable.inv BinTree.get?
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

/-- Checker utility -/
structure RTableStatus where
  rTable        : Array REntry := #[]
  rTableTree    : BinTree REntry := BinTree.leaf
  nonemptyMap   : HashMap LamSort Nat := {}
  wfMap         : HashMap (List LamSort × LamSort × LamTerm) Nat := {}
  validMap      : HashMap (List LamSort × LamTerm) Nat := {}
  -- maxEVarSucc
  maxEVarSucc   : Nat := 0
  -- lamEVarTy
  lamEVarTy     : Array LamSort := #[]
  -- This works as a cache for `BinTree.ofListGet lamEVarTy.data`
  lamEVarTyTree : BinTree LamSort := BinTree.leaf
  -- `chkMap.find?[re]` returns the checkstep which proves `re`
  chkMap        : HashMap REntry ChkStep := {}
  deriving Inhabited

def RTableStatus.push (rs : RTableStatus) (re : REntry) :=
  let rsize := rs.rTable.size
  let rs := {rs with rTable := rs.rTable.push re,
                     rTableTree := rs.rTableTree.insert rsize re}
  match re with
  | .nonempty s => {rs with nonemptyMap := rs.nonemptyMap.insert s rsize}
  | .wf lctx s t => {rs with wfMap := rs.wfMap.insert (lctx, s, t) rsize}
  | .valid lctx t => {rs with validMap := rs.validMap.insert (lctx, t) rsize}

def RTableStatus.addEntry (rs : RTableStatus) (c : ChkStep) (re : REntry) :=
  { rs.push re with chkMap := rs.chkMap.insert re c}

def RTableStatus.newEtomWithValid (rs : RTableStatus) (c : ChkStep) (re : REntry) (s : LamSort) :=
  let eidx := rs.maxEVarSucc
  { rs.push re with chkMap := rs.chkMap.insert re c
                    maxEVarSucc := eidx + 1,
                    lamEVarTy := rs.lamEVarTy.push s
                    lamEVarTyTree := rs.lamEVarTyTree.insert eidx s}

def RTableStatus.findPos? (rs : RTableStatus) (re : REntry) :=
  match re with
  | .nonempty s => rs.nonemptyMap.find? s
  | .wf lctx s t => rs.wfMap.find? (lctx, s, t)
  | .valid lctx t => rs.validMap.find? (lctx, t)

end Auto.Embedding.Lam
