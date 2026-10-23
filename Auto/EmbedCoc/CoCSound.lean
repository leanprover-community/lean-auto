module

public import Auto.EmbedCoc.CoCInterp
public import Auto.EmbedCoc.CoCJudge

@[expose] public section

/-!
  Soundness of the judgement with respect to the reference interpretation: a term
  that has a type in a context is interpreted, in every environment that fits the
  context, as an element of the interpretation of its type
-/

namespace Auto.Embedding.CoC

universe u v

/-! ## Renaming and substitution -/

/-- Renaming the bound variables under one more binder -/
theorem pushLCtx_comp_mapAt_succ {α : Sort _} (d : α) (ρ : Nat → α) (idx : Nat) (f : Nat → Nat) :
    pushLCtx d ρ ∘ mapAt (.succ idx) f = pushLCtx d (ρ ∘ mapAt idx f) := by
  funext n; cases n with
  | zero => rfl
  | succ n => simp only [Function.comp, mapAt_succ_succ]

/-- Renaming the bound variables of a term renames the environment it is interpreted in -/
theorem CoCTerm.interp_mapBVarAt (t : CoCTerm) (idx : Nat) (f : Nat → Nat) (ρ : Nat → DVal.{u, v}) :
    (t.mapBVarAt idx f).interp ρ = t.interp (ρ ∘ mapAt idx f) := by
  induction t generalizing idx ρ with
  | b n => rfl
  | t bt => rfl
  | a s' A B fn arg ihA ihB ihf iha =>
    simp only [CoCTerm.mapBVarAt, CoCTerm.interp, ihA, ihB, ihf, iha, pushLCtx_comp_mapAt_succ]
  | «λ» s' A B b ihA ihB ihb =>
    simp only [CoCTerm.mapBVarAt, CoCTerm.interp, ihA, ihB, ihb, pushLCtx_comp_mapAt_succ]
  | «∀» s' A B ihA ihB =>
    simp only [CoCTerm.mapBVarAt, CoCTerm.interp, ihA, ihB, pushLCtx_comp_mapAt_succ]

theorem CoCTerm.interp_bvarLifts (t : CoCTerm) (k : Nat) (ρ : Nat → DVal.{u, v}) :
    (t.bvarLifts k).interp ρ = t.interp (fun n => ρ (n + k)) := by
  rw [CoCTerm.bvarLifts, CoCTerm.bvarLiftsIdx, CoCTerm.interp_mapBVarAt, mapAt_zero]; rfl

theorem CoCTerm.sort?_mapBVarAt (t : CoCTerm) (idx : Nat) (f : Nat → Nat) :
    (t.mapBVarAt idx f).sort? = t.sort? := by
  cases t <;> rfl

theorem CoCTerm.interpTy_mapBVarAt (t : CoCTerm) (idx : Nat) (f : Nat → Nat)
    (ρ : Nat → DVal.{u, v}) : (t.mapBVarAt idx f).interpTy ρ = t.interpTy (ρ ∘ mapAt idx f) := by
  unfold CoCTerm.interpTy; rw [CoCTerm.sort?_mapBVarAt, CoCTerm.interp_mapBVarAt]

theorem CoCTerm.interpTy_bvarLifts (t : CoCTerm) (k : Nat) (ρ : Nat → DVal.{u, v}) :
    (t.bvarLifts k).interpTy ρ = t.interpTy (fun n => ρ (n + k)) := by
  rw [CoCTerm.bvarLifts, CoCTerm.bvarLiftsIdx, CoCTerm.interpTy_mapBVarAt, mapAt_zero]; rfl

/--
  Substituting `arg` for the bound variable `idx` of a term inserts the value `d` of
  `arg` into the environment it is interpreted in. `arg` is written in the context
  outside the `idx` binders, so its value is taken in the environment `ρ` shifted by `idx`
-/
theorem CoCTerm.interp_instantiateAt (t arg : CoCTerm) (idx : Nat) (ρ : Nat → DVal.{u, v})
    (d : DVal.{u, v}) (h : arg.interp (fun n => ρ (n + idx)) = some d) :
    (CoCTerm.instantiateAt idx arg t).interp ρ = t.interp (pushLCtxAt d idx ρ) := by
  induction t generalizing idx ρ with
  | b n =>
    rcases Nat.lt_trichotomy n idx with hlt | rfl | hgt
    · simp only [CoCTerm.instantiateAt, CoCTerm.interp_b, pushLCtxAt_lt _ _ _ hlt]
    · simp only [CoCTerm.instantiateAt, CoCTerm.interp_b, pushLCtxAt_eq, CoCTerm.interp_bvarLifts]
      exact h
    · simp only [CoCTerm.instantiateAt, CoCTerm.interp_b, pushLCtxAt_gt _ _ _ hgt]
  | t bt => rfl
  | a s' A B fn arg' ihA ihB ihf iha =>
    have ihB' := fun y => ihB (.succ idx) (pushLCtx y ρ) h
    simp only [CoCTerm.instantiateAt, CoCTerm.interp, ihA idx ρ h, ihB', ihf idx ρ h, iha idx ρ h,
      ← pushLCtx_pushLCtxAt]
  | «λ» s' A B b ihA ihB ihb =>
    have ihB' := fun y => ihB (.succ idx) (pushLCtx y ρ) h
    have ihb' := fun y => ihb (.succ idx) (pushLCtx y ρ) h
    simp only [CoCTerm.instantiateAt, CoCTerm.interp, ihA idx ρ h, ihB', ihb',
      ← pushLCtx_pushLCtxAt]
  | «∀» s' A B ihA ihB =>
    have ihB' := fun y => ihB (.succ idx) (pushLCtx y ρ) h
    simp only [CoCTerm.instantiateAt, CoCTerm.interp, ihA idx ρ h, ihB', ← pushLCtx_pushLCtxAt]

/-- Substituting `arg` for the innermost bound variable pushes the value of `arg` -/
theorem CoCTerm.interp_instantiate1 (t arg : CoCTerm) (ρ : Nat → DVal.{u, v}) (d : DVal.{u, v})
    (h : arg.interp ρ = some d) : (CoCTerm.instantiate1 arg t).interp ρ = t.interp (pushLCtx d ρ) := by
  rw [CoCTerm.instantiate1, CoCTerm.interp_instantiateAt t arg 0 ρ d h, pushLCtxAt_zero]

/-! ## Values, types and their readings -/

theorem DVal.ofTy_inj {s s' : CoCSort} {A : SemSort.Ty.{u, v} s.toSem}
    {A' : SemSort.Ty.{u, v} s'.toSem} (h : DVal.ofTy s A = DVal.ofTy s' A') : s = s' ∧ HEq A A' := by
  have e := congrArg DVal.toType? h
  rw [DVal.toType?_ofTy, DVal.toType?_ofTy, Option.some.injEq, Sigma.mk.injEq] at e
  exact e

/-- A value whose type and level are `Tv` and `l` is an element of `Tv` -/
theorem DVal.eq_mk_of_sigma {l : SemSort} {Tv : SemSort.Ty.{u, v} l} {d : DVal.{u, v}}
    (h : (⟨l, Tv⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨d.s, d.ty⟩) : ∃ x, d = ⟨l, Tv, x⟩ := by
  obtain ⟨ds, dty, x⟩ := d
  cases h
  exact ⟨x, rfl⟩

/-- A value whose type is `Sort s` is a type at sort `s` -/
theorem DVal.exists_ofTy {s : CoCSort} {d : DVal.{u, v}}
    (h : (⟨s.sortOf, s.sortCode⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨d.s, d.ty⟩) :
    ∃ A, d = DVal.ofTy s A := by
  obtain ⟨x, rfl⟩ := DVal.eq_mk_of_sigma h
  exact ⟨s.tyDown x, by rw [DVal.ofTy, CoCSort.tyUp_tyDown]⟩

theorem CoCTerm.sort?_eq_some {t : CoCTerm} {s : CoCSort} : t.sort? = some s ↔ t = .t (.sort s) := by
  constructor
  · intro h
    rcases t with _ | bt | _ | _ | _ <;> try cases h
    cases bt <;> cases h; rfl
  · rintro rfl; rfl

/-- The value of `Sort k` is the type `Sort k`, as `CoCTerm.interpTy` reads it -/
theorem CoCSort.sortVal_eq_ofTy {k s : CoCSort} {A : SemSort.Ty.{u, v} s.toSem}
    (h : k.sortVal = some (DVal.ofTy s A)) :
    (⟨k.sortOf, k.sortCode⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨s.toSem, A⟩ := by
  unfold CoCSort.sortVal at h
  split at h
  case h_1 s₁ hs =>
    have ⟨e₁, e₂⟩ := DVal.ofTy_inj (Option.some.inj h)
    subst e₁
    exact Sigma.ext (CoCSort.toSem_of_succ hs).symm ((cast_heq _ _).symm.trans e₂)
  case h_2 => cases h

/-- A term whose value is a type is read as that type, whether it is a sort or not -/
theorem CoCTerm.interpTy_of_ofTy {T : CoCTerm} {ρ : Nat → DVal.{u, v}} {s : CoCSort}
    {A : SemSort.Ty.{u, v} s.toSem} (h : T.interp ρ = some (DVal.ofTy s A)) :
    T.interpTy ρ = some ⟨s.toSem, A⟩ := by
  cases hs : T.sort? with
  | none => exact CoCTerm.interpTy_of_interp hs h
  | some k =>
    obtain rfl := CoCTerm.sort?_eq_some.mp hs
    rw [CoCTerm.interpTy_of_sort? hs]
    exact congrArg some (CoCSort.sortVal_eq_ofTy h)

/-- A term that is not a sort is read as a type only when its value is that type -/
theorem CoCTerm.interp_of_interpTy {T : CoCTerm} {ρ : Nat → DVal.{u, v}} {l : SemSort}
    {Tv : SemSort.Ty.{u, v} l} (hs : T.sort? = none) (h : T.interpTy ρ = some ⟨l, Tv⟩) :
    ∃ (s : CoCSort) (A : SemSort.Ty.{u, v} s.toSem), T.interp ρ = some (DVal.ofTy s A) ∧
      (⟨l, Tv⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨s.toSem, A⟩ := by
  unfold CoCTerm.interpTy at h
  rw [hs] at h
  obtain ⟨sA, hsA, e⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨d, hd, ht⟩ := Option.bind_eq_some_iff.mp hsA
  obtain ⟨s, A⟩ := sA
  exact ⟨s, A, by rw [hd, DVal.toType?_eq_some.mp ht], e.symm⟩

/-! ## Environments that fit a context -/

/--
  `ρ` fits `Γ`: each value `ρ n` has the type that the entry `Γ[n]` denotes, in the
  environment of the values after it. The values beyond `Γ` are unconstrained
-/
def EnvFits (ρ : Nat → DVal.{u, v}) : List CoCTerm → Prop
  | []     => True
  | A :: Γ => A.interpTy (fun n => ρ (n + 1)) = some ⟨(ρ 0).s, (ρ 0).ty⟩ ∧
      EnvFits (fun n => ρ (n + 1)) Γ

theorem EnvFits.push {ρ : Nat → DVal.{u, v}} {Γ : List CoCTerm} {A : CoCTerm} {d : DVal.{u, v}}
    (hA : A.interpTy ρ = some ⟨d.s, d.ty⟩) (hρ : EnvFits ρ Γ) : EnvFits (pushLCtx d ρ) (A :: Γ) :=
  ⟨hA, hρ⟩

/-- The value of a bound variable has the type of its entry, shifted past the entries before it -/
theorem EnvFits.get : ∀ {ρ : Nat → DVal.{u, v}} {Γ : List CoCTerm} {n : Nat} {A : CoCTerm},
    EnvFits ρ Γ → Γ[n]? = some A →
    A.interpTy (fun i => ρ (i + (n + 1))) = some ⟨(ρ n).s, (ρ n).ty⟩
  | _, _ :: _, 0,     _, hρ, h => by cases h; exact hρ.1
  | ρ, _ :: _, _ + 1, _, hρ, h => EnvFits.get (ρ := fun n => ρ (n + 1)) hρ.2 h

/-! ## Reduction preserves the interpretation -/

/-- A base term does not reduce -/
theorem CoCTerm.Red.eq_of_t {b : CoCBaseTerm} {C : CoCTerm} (h : CoCTerm.Red (.t b) C) :
    C = .t b := by
  cases h with
  | refl => rfl
  | step h₁ _ => cases h₁

/-- One step of `β`-reduction preserves the interpretation of a term that has one -/
theorem CoCTerm.Red1.interp {t t' : CoCTerm} (h : t.Red1 t') :
    ∀ {ρ : Nat → DVal.{u, v}} {d : DVal.{u, v}}, t.interp ρ = some d → t'.interp ρ = some d := by
  induction h with
  | beta s' A B b a =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ha, rfl⟩ := CoCTerm.interp_app_eq_some.mp hd
    obtain ⟨s₂, A₂, B₂, f₂, r₂, hj₂, hA₂, hB₂, hb₂, e⟩ := CoCTerm.interp_lam_eq_some.mp hf
    -- The abstraction is interpreted at the same type as the application expects
    obtain ⟨rfl, hAA⟩ := DVal.ofTy_inj (Option.some.inj (hA₂.symm.trans hA))
    cases eq_of_heq hAA
    have hBB : B₂ = B' := funext fun x =>
      eq_of_heq (DVal.ofTy_inj (Option.some.inj ((hB₂ x).symm.trans (hB x)))).2
    subst hBB
    cases Option.some.inj (hj₂.symm.trans hj)
    cases eq_of_heq (DVal.mk.inj e).2.2
    rw [CoCTerm.interp_instantiate1 b a ρ _ ha, hb₂ av, CoCSort.app_lam]
  | aArgTy _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ha, rfl⟩ := CoCTerm.interp_app_eq_some.mp hd
    exact CoCTerm.interp_app_eq_some.mpr ⟨s, A', B', r, hj, fv, av, ih hA, hB, hf, ha, rfl⟩
  | aResTy _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ha, rfl⟩ := CoCTerm.interp_app_eq_some.mp hd
    exact CoCTerm.interp_app_eq_some.mpr
      ⟨s, A', B', r, hj, fv, av, hA, fun x => ih (hB x), hf, ha, rfl⟩
  | aFn _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ha, rfl⟩ := CoCTerm.interp_app_eq_some.mp hd
    exact CoCTerm.interp_app_eq_some.mpr ⟨s, A', B', r, hj, fv, av, hA, hB, ih hf, ha, rfl⟩
  | aArg _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ha, rfl⟩ := CoCTerm.interp_app_eq_some.mp hd
    exact CoCTerm.interp_app_eq_some.mpr ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ih ha, rfl⟩
  | lamArgTy _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', f, r, hj, hA, hB, hb, rfl⟩ := CoCTerm.interp_lam_eq_some.mp hd
    exact CoCTerm.interp_lam_eq_some.mpr ⟨s, A', B', f, r, hj, ih hA, hB, hb, rfl⟩
  | lamResTy _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', f, r, hj, hA, hB, hb, rfl⟩ := CoCTerm.interp_lam_eq_some.mp hd
    exact CoCTerm.interp_lam_eq_some.mpr ⟨s, A', B', f, r, hj, hA, fun x => ih (hB x), hb, rfl⟩
  | lamBody _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', f, r, hj, hA, hB, hb, rfl⟩ := CoCTerm.interp_lam_eq_some.mp hd
    exact CoCTerm.interp_lam_eq_some.mpr ⟨s, A', B', f, r, hj, hA, hB, fun x => ih (hb x), rfl⟩
  | forallArgTy _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, hA, hB, rfl⟩ := CoCTerm.interp_forall_eq_some.mp hd
    exact CoCTerm.interp_forall_eq_some.mpr ⟨s, A', B', r, hj, ih hA, hB, rfl⟩
  | forallBodyTy _ ih =>
    intro ρ d hd
    obtain ⟨s, A', B', r, hj, hA, hB, rfl⟩ := CoCTerm.interp_forall_eq_some.mp hd
    exact CoCTerm.interp_forall_eq_some.mpr ⟨s, A', B', r, hj, hA, fun x => ih (hB x), rfl⟩

theorem CoCTerm.Red.interp {t t' : CoCTerm} (h : t.Red t') {ρ : Nat → DVal.{u, v}}
    {d : DVal.{u, v}} (hd : t.interp ρ = some d) : t'.interp ρ = some d := by
  induction h with
  | refl => exact hd
  | step h₁ _ ih => exact ih (h₁.interp hd)

/-- Joinable terms that are both interpreted have the same interpretation -/
theorem CoCTerm.Joinable.interp_eq {A B : CoCTerm} (h : A.Joinable B) {ρ : Nat → DVal.{u, v}}
    {dA dB : DVal.{u, v}} (hA : A.interp ρ = some dA) (hB : B.interp ρ = some dB) : dA = dB := by
  obtain ⟨C, hAC, hBC⟩ := h
  exact Option.some.inj ((hAC.interp hA).symm.trans (hBC.interp hB))

/-! ## Soundness -/

/--
  Soundness: in every environment that fits `Γ`, a term `t` with `Γ ⊢ t : T` is
  interpreted as an element of the type that `T` denotes. There is nothing to show
  for a well-formed context
-/
theorem Judge.sound {Γ : List CoCTerm} {j : JudgeForm} (h : Judge Γ j) :
    match j with
    | .wf => True
    | .hasType t T => ∀ ρ : Nat → DVal.{u, v}, EnvFits ρ Γ →
        ∃ d, t.interp ρ = some d ∧ T.interpTy ρ = some ⟨d.s, d.ty⟩ := by
  induction h with
  | nil | cons => trivial
  | base _ hb => exact fun ρ _ => CoCBaseTerm.interp_check hb ρ
  | @var Γ n A _ hA =>
    intro ρ hρ
    exact ⟨ρ n, rfl, by rw [CoCTerm.interpTy_bvarLifts]; exact hρ.get hA⟩
  | @pi Γ A B s s' r _ _ hj ihA ihB =>
    intro ρ hρ
    obtain ⟨dA, hA, hAty⟩ := ihA ρ hρ
    rw [CoCSort.interpTy_toCoCTerm, Option.some.injEq] at hAty
    obtain ⟨A', rfl⟩ := DVal.exists_ofTy hAty
    -- `B` is a type at sort `s'` for every value of the bound variable
    have hB : ∀ x, ∃ Bx, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' Bx) := by
      intro x
      obtain ⟨dB, hdB, hBty⟩ :=
        ihB _ (EnvFits.push (d := ⟨s.toSem, A', x⟩) (CoCTerm.interpTy_of_ofTy hA) hρ)
      rw [CoCSort.interpTy_toCoCTerm, Option.some.injEq] at hBty
      obtain ⟨Bx, rfl⟩ := DVal.exists_ofTy hBty
      exact ⟨Bx, hdB⟩
    exact ⟨_, CoCTerm.interp_forall_of (B' := fun x => (hB x).choose) hj hA
      (fun x => (hB x).choose_spec), by rw [CoCSort.interpTy_toCoCTerm]; rfl⟩
  | @lam Γ A B b s' r _ _ ihPi ihb =>
    intro ρ hρ
    obtain ⟨dPi, hPi, -⟩ := ihPi ρ hρ
    obtain ⟨s, A', B', r', hj, hA, hB, rfl⟩ := CoCTerm.interp_forall_eq_some.mp hPi
    -- `b` is an element of `B` for every value of the bound variable
    have hb : ∀ x, ∃ fx, b.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some ⟨s'.toSem, B' x, fx⟩ := by
      intro x
      obtain ⟨db, hdb, hbty⟩ :=
        ihb _ (EnvFits.push (d := ⟨s.toSem, A', x⟩) (CoCTerm.interpTy_of_ofTy hA) hρ)
      rw [CoCTerm.interpTy_of_ofTy (hB x), Option.some.injEq] at hbty
      obtain ⟨fx, rfl⟩ := DVal.eq_mk_of_sigma hbty
      exact ⟨fx, hdb⟩
    exact ⟨_, CoCTerm.interp_lam_eq_some.mpr ⟨s, A', B', fun x => (hb x).choose, r', hj, hA, hB,
      fun x => (hb x).choose_spec, rfl⟩, CoCTerm.interpTy_of_ofTy hPi⟩
  | @app Γ A B f a s' _ _ ihf iha =>
    intro ρ hρ
    obtain ⟨df, hf, hfty⟩ := ihf ρ hρ
    obtain ⟨da, ha, haty⟩ := iha ρ hρ
    -- The type of `f` is the interpretation of `∀ x : A, B`
    obtain ⟨r₀, P, hPi, e⟩ := CoCTerm.interp_of_interpTy rfl hfty
    obtain ⟨s, A', B', r, hj, hA, hB, hPiEq⟩ := CoCTerm.interp_forall_eq_some.mp hPi
    obtain ⟨rfl, hP⟩ := DVal.ofTy_inj hPiEq
    cases eq_of_heq hP
    obtain ⟨fv, rfl⟩ := DVal.eq_mk_of_sigma e.symm
    rw [CoCTerm.interpTy_of_ofTy hA, Option.some.injEq] at haty
    obtain ⟨av, rfl⟩ := DVal.eq_mk_of_sigma haty
    refine ⟨_, CoCTerm.interp_app_eq_some.mpr ⟨s, A', B', _, hj, fv, av, hA, hB, hf, ha, rfl⟩, ?_⟩
    exact CoCTerm.interpTy_of_ofTy (by rw [CoCTerm.interp_instantiate1 B a ρ _ ha]; exact hB av)
  | @conv Γ t A B s _ _ hAB iht ihB =>
    intro ρ hρ
    obtain ⟨d, ht, hAty⟩ := iht ρ hρ
    obtain ⟨dB, hB, hBty⟩ := ihB ρ hρ
    rw [CoCSort.interpTy_toCoCTerm, Option.some.injEq] at hBty
    obtain ⟨B', rfl⟩ := DVal.exists_ofTy hBty
    -- `A` has the interpretation of `B`: either it is not a sort, and it has one, or it
    -- is a sort, which does not reduce, so that `B` reduces to it
    have hAi : A.interp ρ = some (DVal.ofTy s B') := by
      obtain ⟨C, hAC, hBC⟩ := hAB
      cases hs : A.sort? with
      | none =>
        obtain ⟨sA, A', hAi, -⟩ := CoCTerm.interp_of_interpTy hs hAty
        rw [hAi]; exact (hAC.interp hAi).symm.trans (hBC.interp hB)
      | some k =>
        obtain rfl := CoCTerm.sort?_eq_some.mp hs
        rw [← CoCTerm.Red.eq_of_t hAC]; exact hBC.interp hB
    exact ⟨d, ht, (CoCTerm.interpTy_of_ofTy hB).trans
      ((CoCTerm.interpTy_of_ofTy hAi).symm.trans hAty)⟩

theorem HasType.sound {Γ : List CoCTerm} {t T : CoCTerm} (h : HasType Γ t T)
    (ρ : Nat → DVal.{u, v}) (hρ : EnvFits ρ Γ) :
    ∃ d, t.interp ρ = some d ∧ T.interpTy ρ = some ⟨d.s, d.ty⟩ :=
  Judge.sound h ρ hρ

/-! ## The interpretation of a derivation -/

/-- The value of `d` as an element of `Tv`, when `d` has the type `Tv` at level `l` -/
def DVal.castTo (d : DVal.{u, v}) {l : SemSort} {Tv : SemSort.Ty.{u, v} l}
    (h : (⟨d.s, d.ty⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨l, Tv⟩) : SemSort.El l Tv :=
  cast (congrArg (fun p : (l : SemSort) × SemSort.Ty.{u, v} l => SemSort.El p.1 p.2) h) d.val

theorem DVal.eq_castTo (d : DVal.{u, v}) {l : SemSort} {Tv : SemSort.Ty.{u, v} l}
    (h : (⟨d.s, d.ty⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨l, Tv⟩) : d = ⟨l, Tv, d.castTo h⟩ := by
  obtain ⟨s, T, x⟩ := d
  cases h
  rfl

/--
  The interpretation of a derivation of `Γ ⊢ t : T` in an environment `ρ` that fits `Γ`:
  an element of the type `Tv` at level `l` that `T` denotes. It is the value of the
  reference interpretation, see `HasType.interp_eq`
-/
noncomputable def HasType.interp {Γ : List CoCTerm} {t T : CoCTerm} (h : HasType Γ t T)
    (ρ : Nat → DVal.{u, v}) (hρ : EnvFits ρ Γ) {l : SemSort} {Tv : SemSort.Ty.{u, v} l}
    (hT : T.interpTy ρ = some ⟨l, Tv⟩) : SemSort.El l Tv :=
  (h.sound ρ hρ).choose.castTo
    (Option.some.inj ((h.sound ρ hρ).choose_spec.2.symm.trans hT))

theorem HasType.interp_eq {Γ : List CoCTerm} {t T : CoCTerm} (h : HasType Γ t T)
    (ρ : Nat → DVal.{u, v}) (hρ : EnvFits ρ Γ) {l : SemSort} {Tv : SemSort.Ty.{u, v} l}
    (hT : T.interpTy ρ = some ⟨l, Tv⟩) : t.interp ρ = some ⟨l, Tv, h.interp ρ hρ hT⟩ := by
  rw [(h.sound ρ hρ).choose_spec.1]
  exact congrArg some (DVal.eq_castTo _ _)

end Auto.Embedding.CoC
