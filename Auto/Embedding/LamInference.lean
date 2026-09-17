module

public import Auto.Embedding.LamConv

@[expose] public section

namespace Auto.Embedding.Lam

variable (R? : Option ((R : Type) × RealTy R))

theorem LamValid.bvarLowers?
  (hv : LamValid R? lval (pushLCtxs ss lctx) t)
  (hlvl : ss.length = lvl)
  (heq : LamTerm.bvarLowers? lvl t = .some t')
  (hInh : HList (LamNonempty R? lval.tyVal) ss) :
  LamValid R? lval lctx t' := by
  cases LamTerm.bvarLowers?_spec.mp heq
  have ⟨wft', ht'⟩ := hv; have hInh' := hInh.map (fun s inh => Classical.choice inh)
  exists LamWF.fromBVarLifts hlvl _ wft'; intro lctxTerm
  have ht'' := ht' (pushLCtxsDep hInh' lctxTerm)
  rw [LamWF.interp_bvarLifts _ lval hInh' hlvl]; apply Eq.mp _ ht''
  apply congrArg; apply LamWF.interp_substWF

theorem LamThmValid.bvarLowers?
  (hv : LamThmValid R? lval (ss ++ lctx) t)
  (hlvl : ss.length = lvl)
  (heq : LamTerm.bvarLowers? lvl t = .some t')
  (hInh : HList (LamNonempty R? lval.tyVal) ss) :
  LamThmValid R? lval lctx t' := fun lctx' =>
  have hv' := hv lctx'; LamValid.bvarLowers? _ (by rw [pushLCtxs_append] at hv'; exact hv') hlvl heq hInh

theorem LamValid.bvarLower?
  (hv : LamValid R? lval (pushLCtx s lctx) t)
  (heq : LamTerm.bvarLower? t = .some t')
  (hInh : LamNonempty R? lval.tyVal s) :
  LamValid R? lval lctx t' :=
  LamValid.bvarLowers? _ (ss:=[s])
    (by rw [pushLCtxs_singleton]; exact hv)
    rfl heq (HList.cons hInh HList.nil)

theorem LamThmValid.bvarLower?
  (hv : LamThmValid R? lval (s :: lctx) t)
  (heq : LamTerm.bvarLower? t = .some t')
  (hInh : LamNonempty R? lval.tyVal s) :
  LamThmValid R? lval lctx t' := fun lctx' =>
  have hv' := hv lctx'; LamValid.bvarLower? _ (by rw [pushLCtxs_cons] at hv'; exact hv') heq hInh

def LamTerm.impApp? (t₁₂ t₁ : LamTerm) : Option LamTerm :=
  match t₁₂ with
  | .app _ (.app _ imp hyp) concl =>
    match hyp.beq t₁ with
    | true =>
      match imp with
      | .base b =>
        match b with
        | .imp => .some concl
        | _ => .none
      | _ => .none
    | false => .none
  | _ => .none

theorem LamTerm.maxEVarSucc_impApp?
  (heq : LamTerm.impApp? t₁₂ t₁ = .some t') : t'.maxEVarSucc ≤ t₁₂.maxEVarSucc := by
  cases t₁₂ <;> try cases heq
  case app s fn arg =>
    cases fn <;> try cases heq
    case app s' imp hyp =>
      dsimp [impApp?] at heq
      cases h : hyp.beq t₁
      case true =>
        rw [h] at heq; cases imp <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          case pcst p =>
            cases p <;> try cases heq
            dsimp [maxEVarSucc]; cases (LamTerm.eq_of_beq_eq_true h)
            apply Nat.le_max_right
      case false =>
        rw [h] at heq; cases heq

theorem LamValid.impApp
  (v₁₂ : LamValid R? lval lctx t₁₂) (v₁ : LamValid R? lval lctx t₁)
  (heq : LamTerm.impApp? t₁₂ t₁ = .some t₂) : LamValid R? lval lctx t₂ := by
  dsimp [LamTerm.impApp?] at heq
  cases t₁₂ <;> try cases heq
  case app bp₁ hypimp concl =>
    cases hypimp <;> try cases heq
    case app bp₂ imp hyp =>
      dsimp at heq
      match h : LamTerm.beq hyp t₁ with
      | true =>
        rw [h] at heq
        cases imp <;> try cases heq
        case base b =>
          cases b <;> try cases heq
          case pcst p =>
            cases p <;> cases heq
            case imp =>
              have ⟨wf₁₂, h₁₂⟩ := v₁₂
              match wf₁₂ with
              | .ofApp _ (.ofApp _ (.ofBase .ofImp) HArg) wfConcl =>
                exists wfConcl; have ⟨wf₁, h₁⟩ := v₁;
                intro lctxTerm; apply h₁₂; apply Eq.mp _ (h₁ lctxTerm);
                apply congrArg; apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
                exact .symm (LamTerm.eq_of_beq_eq_true h)
      | false =>
        rw [h] at heq; cases heq

theorem LamThmValid.impApp
  (H₁₂ : LamThmValid R? lval lctx t₁₂) (H₁ : LamThmValid R? lval lctx t₁)
  (heq : LamTerm.impApp? t₁₂ t₁ = .some res) : LamThmValid R? lval lctx res :=
  fun lctx' => LamValid.impApp _ (H₁₂ lctx') (H₁ lctx') heq

def LamTerm.impApps? (t : LamTerm) (ps : List LamTerm) : Option LamTerm :=
  match ps with
  | .nil => .some t
  | .cons p ps =>
    match t.impApp? p with
    | .some t' => t'.impApps? ps
    | .none => .none

theorem LamTerm.maxEVarSucc_impApps?
  (heq : LamTerm.impApps? t ps = .some t') : t'.maxEVarSucc ≤ t.maxEVarSucc := by
  induction ps generalizing t t'
  case nil => cases heq; apply Nat.le_refl
  case cons p ps IH =>
    dsimp [impApps?] at heq
    match h : impApp? t p with
    | .some t' =>
      rw [h] at heq; dsimp at heq
      apply Nat.le_trans (IH heq) (maxEVarSucc_impApp? h)
    | .none => rw [h] at heq; cases heq

theorem LamValid.impApps
  (vt : LamValid R? lval lctx t) (vps : HList (LamValid R? lval lctx) ps)
  (heq : LamTerm.impApps? t ps = .some t') : LamValid R? lval lctx t' := by
  induction ps generalizing t
  case nil => cases heq; exact vt
  case cons head tail IH =>
    match vps with
    | .cons vHead vTail =>
      dsimp [LamTerm.impApps?] at heq
      match hap : LamTerm.impApp? t head with
      | .some t'' =>
        rw [hap] at heq; dsimp at heq
        apply IH _ vTail heq
        apply LamValid.impApp _ vt vHead hap
      | .none => rw [hap] at heq; cases heq

theorem LamThmValid.impApps
  (vt : LamThmValid R? lval lctx t) (vps : HList (LamThmValid R? lval lctx) ps)
  (heq : LamTerm.impApps? t ps = .some t') : LamThmValid R? lval lctx t' :=
  fun lctx' => LamValid.impApps _ (vt lctx') (vps.map (fun _ tv => tv lctx')) heq

theorem LamThmValid.define {lval : LamValuation.{u} R?}
  (wft : LamThmWF R? lval [] s t) (heVar : t.maxEVarSucc ≤ eidx) :
  ∃ val, LamThmValid R? (lval.insertEVarAt R? s val eidx) [] (.mkEq s (.etom eidx) t) := by
  exists LamWF.interp _ lval dfLCtxTy (dfLCtxTerm _ _) (wft dfLCtxTy)
  apply LamThmValid.ofLamThmValidD
  let ltv₁ := lval.toLamTyVal
  let ltv₂ := { lval.toLamTyVal with lamEVarTy := replaceAt s eidx lval.lamEVarTy}
  have wft' := LamWF.eVarIrrelevance (ltv₁:=ltv₁) (ltv₂:=ltv₂) rfl rfl
    (fun n H => LamTyVal.insertEVarAt_eVarIrrelevance (Nat.le_trans H heVar)) (wft dfLCtxTy)
  apply And.intro
  case left =>
    rw [LamTerm.maxLooseBVarSucc_mkEq]; dsimp [LamTerm.maxLooseBVarSucc]
    rw [Nat.max_zero_left]; have ⟨_, hlb⟩ := LamThmWFD.ofLamThmWF _ wft; apply hlb
  case right =>
    exists LamWF.mkEq LamWF.insertEVarAt_eIdx wft'
    intro lctxTerm; dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamTerm.mkEq, eqLiftFn]
    apply eq_of_heq; apply HEq.trans (LamWF.interp_insertEVarAt_eIdx _ _)
    apply LamWF.interp_eVarIrrelevance <;> try rfl
    intro n hn; apply LamValuation.insertEVarAt_eVarIrrelevance
    apply Nat.le_trans hn heVar

section Skolemization

  def LamTerm.skolemize? (t : LamTerm) (eidx : Nat) (lctx : List LamSort) : Option (LamSort × LamTerm) :=
    match t with
    | .app _ (.base (.existE s)) p => .some (s, .app s p (LamTerm.bvarApps (.etom eidx) lctx 0))
    | _ => .none

  theorem LamTerm.maxEVarSucc_skolemize? (heq : LamTerm.skolemize? t eidx lctx = .some (s, t')) :
    t'.maxEVarSucc ≤ max t.maxEVarSucc (.succ eidx) :=
    match t, heq with
    | .app _ (.base (.existE s)) p, Eq.refl _ => by
      dsimp [maxEVarSucc]; rw [LamTerm.maxEVarSucc_bvarApps];
      simp only [Nat.max, Nat.max_zero_left]; apply Nat.le_refl

  theorem choose_spec' {p : α → β → Prop} (h : ∀ q, ∃ x, p x q) : ∃ (y : _ → _), ∀ q, p (y q) q :=
    ⟨fun q => Classical.choose (h q), fun q => Classical.choose_spec (h q)⟩

  theorem LamThmValid.skolemize
    (vt : LamThmValid R? lval lctx (.mkExistE s p)) (heVar : p.maxEVarSucc ≤ eidx) :
    ∃ val, LamThmValid R? (lval.insertEVarAt R? (s.mkFuncsRev lctx) val eidx) lctx (.app s p (LamTerm.bvarApps (.etom eidx) lctx 0)) := by
    have ⟨hSucc, ⟨wft, ht⟩⟩ := LamThmValidD.ofLamThmValid _ vt
    cases wft; case ofApp HArg HFn => cases HFn; case ofBase Hb => cases Hb; case ofExistE =>
      dsimp [LamWF.interp, LamBaseTerm.LamWF.interp, LamTerm.mkExistE, existLiftFn] at ht;
      have ⟨valPre, hvalPre⟩ := choose_spec' ht
      exists LamSort.curryRev _ valPre; apply LamThmValid.ofLamThmValidD; apply And.intro;
      case left =>
        dsimp [LamTerm.maxLooseBVarSucc]; rw [Nat.max_le]; apply And.intro (Nat.max_le.mp hSucc).right
        apply Nat.le_trans LamTerm.maxLooseBVarSucc_bvarApps; rw [Nat.max_le]
        apply And.intro (Nat.zero_le _) .refl
      case right =>
        let ltv₁ := lval.toLamTyVal
        let ltv₂ := { lval.toLamTyVal with lamEVarTy := replaceAt (s.mkFuncsRev lctx) eidx lval.lamEVarTy}
        have HArg' := LamWF.eVarIrrelevance (ltv₁:=ltv₁) (ltv₂:=ltv₂) rfl rfl
          (fun n H => LamTyVal.insertEVarAt_eVarIrrelevance (Nat.le_trans H heVar)) HArg
        exists (.ofApp _ HArg' (LamWF.bvarApps (ex:=[]) LamWF.insertEVarAt_eIdx))
        intro lctxTerm; dsimp [LamWF.interp]
        apply Eq.mp _ (hvalPre lctxTerm); apply congrArg; apply eq_of_heq
        apply congr_hd_heq <;> try rfl
        case h₁ =>
          apply LamWF.interp_eVarIrrelevance <;> try rfl;
          intros n H; apply LamValuation.insertEVarAt_eVarIrrelevance;
          apply Nat.le_trans H heVar
        case h₂ =>
          apply HEq.symm
          apply LamWF.interp_bvarApps _ (tyex:=[]) (termex:=.nil) LamWF.insertEVarAt_eIdx
          apply LamWF.interp_insertEVarAt_eIdx

  theorem LamThmValid.skolemize?
    (vt : LamThmValid R? lval lctx t) (heq : t.skolemize? eidx lctx = .some (s, t'))
    (heVar : t.maxEVarSucc ≤ eidx) :
    ∃ val, LamThmValid R? (lval.insertEVarAt R? (s.mkFuncsRev lctx) val eidx) lctx t' := by
    have ⟨_, ⟨wft, ht⟩⟩ := LamThmValidD.ofLamThmValid _ vt
    match t, heq with
    | .app _ (.base (.existE s)) p, Eq.refl _ =>
      match wft with
      | .ofApp _ (.ofBase (.ofExistE _)) HArg =>
        dsimp [LamTerm.maxEVarSucc] at heVar; rw [Nat.max_le] at heVar
        apply LamThmValid.skolemize _ vt heVar.right

end Skolemization

end Auto.Embedding.Lam
