import Auto.Embedding.LamSystem

namespace Auto.Embedding.Lam

def LamTerm.intro1F? (t : LamTerm) : Option (LamSort × LamTerm) :=
  match t with
  | .app _ (.base (.forallE s)) (.lam _ t) => .some (s, t)
  | _ => .none

theorem LamTerm.maxEVarSucc_intro1F?
  (heq : LamTerm.intro1F? t = .some (s, t')) : t'.maxEVarSucc = t.maxEVarSucc :=
  match t, heq with
  | .app _ (.base (.forallE _)) (.lam _ _), Eq.refl _ => by
    simp [maxEVarSucc, Nat.max, Nat.max_zero_left]

theorem LamValid.intro1F? (H : LamValid lval lctx t)
  (heq : LamTerm.intro1F? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p :=
  match t, heq with
  | .app _ (.base (.forallE _)) (.lam _ _), Eq.refl _ =>
    have ⟨wfl, _⟩ := H
    match wfl with
    | .ofApp _ (.ofBase (.ofForallE _)) (.ofLam _ Hp) => by
      apply LamValid.intro1F H

/-- First-order logic style intro1 -/
theorem LamThmValid.intro1F? (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1F? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs_cons]; apply LamValid.intro1F? (H lctx') heq

def LamTerm.intro1H? (t : LamTerm) : Option (LamSort × LamTerm) :=
  match t with
  | .app _ (.base (.forallE s)) p => .some (s, .app s p.bvarLift (.bvar 0))
  | _ => .none

theorem LamTerm.maxEVarSucc_intro1H?
  (heq : LamTerm.intro1H? t = .some (s, t')) : t'.maxEVarSucc = t.maxEVarSucc := by
  match t, heq with
  | .app _ (.base (.forallE s)) p, Eq.refl _ =>
    dsimp [maxEVarSucc, bvarLift, bvarLiftIdx, bvarLiftsIdx];
    rw [LamTerm.maxEVarSucc_mapBVarAt]; apply Nat.max_comm

theorem LamValid.intro1H? (H : LamValid lval lctx t)
  (heq : LamTerm.intro1H? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p :=
  match t, heq with
  | .app s' (.base (.forallE s)) t, Eq.refl _ =>
    have ⟨wfl, vl⟩ := H
    match wfl with
    | .ofApp _ (.ofBase (.ofForallE _)) Hp => by
      let Hp' := LamWF.bvarLiftIdx (s:=s) 0 _ Hp
      let HApp := LamWF.ofApp s Hp' (.ofBVar 0)
      rw [← pushLCtxAt_zero]; exists HApp; intro lctxTerm
      dsimp [LamWF.interp, LamTerm.bvarLift]
      have vl' := vl (fun n => lctxTerm (.succ n)) (lctxTerm 0)
      apply Eq.mp _ vl'; apply congrArg; apply congrFun;
      apply Eq.trans (LamWF.interp_bvarLiftIdx lval (idx:=0) lctx
        (fun n => lctxTerm (Nat.succ n)) (lctxTerm 0) _ Hp) ?req
      apply eq_of_heq; apply LamWF.interp_heq <;> try rfl
      case HLCtxTermEq =>
        apply HEq.funext; intro n; cases n <;> rfl

/-- Higher-order logic style intro1 -/
theorem LamThmValid.intro1H? (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1H? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs_cons]; apply LamValid.intro1H? (H lctx') heq

def LamTerm.intro1? (t : LamTerm) : Option (LamSort × LamTerm) :=
  match t with
  | .app _ (.base (.forallE s)) p =>
    match p with
    | .lam _ t => .some (s, t)
    | _ => .some (s, .app s p.bvarLift (.bvar 0))
  | _ => .none

theorem LamTerm.maxEVarSucc_intro1? (heq : LamTerm.intro1? t = .some (s, t')) :
  t'.maxEVarSucc = t.maxEVarSucc := by
  cases t <;> try cases heq
  case app _ fn p =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        dsimp [intro1?] at heq;
        dsimp [maxEVarSucc]; rw [Nat.max, Nat.max_def]; simp [Nat.zero_le]
        cases p <;> cases heq <;> try rfl
        case app.refl =>
          dsimp [maxEVarSucc, bvarLift, bvarLiftIdx, bvarLiftsIdx]; rw [LamTerm.maxEVarSucc_mapBVarAt]; dsimp [maxEVarSucc]
          rw [Nat.max, Nat.max_comm, Nat.max_def]; simp [Nat.zero_le]

theorem LamValid.intro1? (H : LamValid lval lctx t)
  (heq : LamTerm.intro1? t = .some (s, p)) : LamValid lval (pushLCtx s lctx) p := by
  dsimp [LamTerm.intro1?] at heq
  cases t <;> try cases heq
  case app _ fn p =>
    cases fn <;> try cases heq
    case base b =>
      cases b <;> try cases heq
      case forallE s =>
        dsimp at heq
        cases p <;> try apply LamValid.intro1H? H heq
        apply LamValid.intro1F? H heq

theorem LamThmValid.intro1? (H : LamThmValid lval lctx t)
  (heq : LamTerm.intro1? t = .some (s, p)) : LamThmValid lval (s :: lctx) p :=
  fun lctx' => by rw [pushLCtxs_cons]; apply LamValid.intro1? (H lctx') heq

end Auto.Embedding.Lam
