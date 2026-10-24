module

public import Auto.EmbedCoC.CoCModel

@[expose] public section

/-!
  The reference interpretation of the embedded system on raw terms (cf.
  Streicher, *Semantics of Type Theory*, 1991). It is partial: `none` means that
  the term is ill-typed in the model. Where the types of two values must agree it
  decides so classically, so it is noncomputable and meant for proofs only.

  Environments are functions `Nat → DVal`, extended with `pushLCtx`, so that the
  de Bruijn operations of `CoCBase` can be related to them with `LCtx`
-/

namespace Auto.Embedding.CoC

universe u v w w'

/-- The values of a family at every point, when they are all defined -/
noncomputable def allSome {α : Type w} {β : α → Type w'} (F : (x : α) → Option (β x)) :
    Option ((x : α) → β x) :=
  open Classical in
  if h : ∀ x, (F x).isSome then some fun x => (F x).get (h x) else none

theorem allSome_eq_some {α : Type w} {β : α → Type w'} {F : (x : α) → Option (β x)}
    {g : (x : α) → β x} : allSome F = some g ↔ ∀ x, F x = some (g x) := by
  unfold allSome
  split
  case isTrue h =>
    rw [Option.some.injEq]
    constructor
    · rintro rfl x; exact (Option.some_get (h x)).symm
    · intro hg; funext x; exact (Option.eq_some_iff_get_eq.mp (hg x)).choose_spec
  case isFalse h =>
    constructor
    · intro hn; cases hn
    · intro hg; exact absurd (fun x => Option.isSome_iff_exists.mpr ⟨_, hg x⟩) h

/-- `d` as a type, at the sort that the level of `d` determines -/
noncomputable def DVal.toType? (d : DVal.{u, v}) :
    Option ((s : CoCSort) × SemSort.Ty.{u, v} s.toSem) :=
  d.s.pred?.bind fun s => (d.asTy s).map fun A => ⟨s, A⟩

theorem DVal.toType?_eq_some {d : DVal.{u, v}} {s : CoCSort} {A : SemSort.Ty.{u, v} s.toSem} :
    d.toType? = some ⟨s, A⟩ ↔ d = DVal.ofTy s A := by
  unfold DVal.toType?
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨s₀, -, h⟩
    rw [Option.map_eq_some_iff] at h
    obtain ⟨A₀, hA₀, heq⟩ := h
    cases heq
    exact DVal.asTy_eq_some.mp hA₀
  · intro hd
    refine ⟨s, ?_, ?_⟩
    · rw [hd]; exact CoCSort.pred?_sortOf s
    · rw [DVal.asTy_eq_some.mpr hd]; rfl

theorem DVal.toType?_ofTy (s : CoCSort) (A : SemSort.Ty.{u, v} s.toSem) :
    (DVal.ofTy s A).toType? = some ⟨s, A⟩ :=
  DVal.toType?_eq_some.mpr rfl

/-- `s.join s'`, together with the proof that it is the join -/
def CoCSort.joinWit (s s' : CoCSort) : Option {r : CoCSort // s.join s' = some r} :=
  go (s.join s') rfl
where
  go : (o : Option CoCSort) → s.join s' = o → Option {r : CoCSort // s.join s' = some r}
    | some r, h => some ⟨r, h⟩
    | none,   _ => none

/-- The join is unique, so any witness is the one `joinWit` finds -/
theorem CoCSort.joinWit_eq {s s' : CoCSort} (r : {r : CoCSort // s.join s' = some r}) :
    s.joinWit s' = some r := by
  obtain ⟨r, h⟩ := r
  cases s <;> cases s' <;>
    cases h <;> rfl

/--
  The value of `t` in the environment `ρ`, or `none` when `t` is ill-typed in the
  model. A type is interpreted as an element of its sort, see `DVal.ofTy`
  * `∀ x : A, B` is defined when `A` is a type at some sort `s`, and `B` is a type
    at the annotated sort `s'` for every value of `x`
  * `λ x : A, b`, annotated with `B`, is defined when `∀ x : A, B` is, and `b` is
    an element of `B` for every value of `x`
  * `f a`, annotated with `∀ x : A, B`, is defined when `∀ x : A, B` is, `f` is
    an element of it and `a` is an element of `A`
-/
noncomputable def CoCTerm.interp : CoCTerm → (Nat → DVal.{u, v}) → Option DVal.{u, v}
  | .b n, ρ => some (ρ n)
  | .t bt, _ => bt.interp
  | .«∀» s' A B, ρ =>
    (A.interp ρ).bind fun dA => dA.toType?.bind fun sA =>
    (allSome fun x => (B.interp (pushLCtx ⟨sA.1.toSem, sA.2, x⟩ ρ)).bind (·.asTy s')).bind
      fun B' =>
    (sA.1.joinWit s').map fun r => .ofTy r.1 (CoCSort.pi sA.1 s' r.2 sA.2 B')
  | .«λ» s' A B body, ρ =>
    (A.interp ρ).bind fun dA => dA.toType?.bind fun sA =>
    (allSome fun x => (B.interp (pushLCtx ⟨sA.1.toSem, sA.2, x⟩ ρ)).bind (·.asTy s')).bind
      fun B' =>
    (allSome fun x =>
      (body.interp (pushLCtx ⟨sA.1.toSem, sA.2, x⟩ ρ)).bind (·.get? s'.toSem (B' x))).bind
      fun f =>
    (sA.1.joinWit s').map fun r =>
      ⟨r.1.toSem, CoCSort.pi sA.1 s' r.2 sA.2 B', CoCSort.lam sA.1 s' r.2 sA.2 B' f⟩
  | .a s' A B fn arg, ρ =>
    (A.interp ρ).bind fun dA => dA.toType?.bind fun sA =>
    (allSome fun x => (B.interp (pushLCtx ⟨sA.1.toSem, sA.2, x⟩ ρ)).bind (·.asTy s')).bind
      fun B' =>
    (sA.1.joinWit s').bind fun r =>
    ((fn.interp ρ).bind (·.get? r.1.toSem (CoCSort.pi sA.1 s' r.2 sA.2 B'))).bind fun fv =>
    ((arg.interp ρ).bind (·.get? sA.1.toSem sA.2)).map fun av =>
      ⟨s'.toSem, B' av, CoCSort.app sA.1 s' r.2 sA.2 B' fv av⟩

theorem CoCTerm.interp_b (n : Nat) (ρ : Nat → DVal.{u, v}) :
    (CoCTerm.b n).interp ρ = some (ρ n) := rfl

theorem CoCTerm.interp_t (b : CoCBaseTerm) (ρ : Nat → DVal.{u, v}) :
    (CoCTerm.t b).interp ρ = b.interp := rfl

theorem CoCTerm.interp_forall_eq_some {s' : CoCSort} {A B : CoCTerm} {ρ : Nat → DVal.{u, v}}
    {d : DVal.{u, v}} :
    (CoCTerm.«∀» s' A B).interp ρ = some d ↔
    ∃ (s : CoCSort) (A' : SemSort.Ty.{u, v} s.toSem)
      (B' : SemSort.El s.toSem A' → SemSort.Ty.{u, v} s'.toSem)
      (r : CoCSort) (hj : s.join s' = some r),
      A.interp ρ = some (DVal.ofTy s A') ∧
      (∀ x, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' (B' x))) ∧
      d = DVal.ofTy r (CoCSort.pi s s' hj A' B') := by
  simp only [CoCTerm.interp, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨dA, hA, ⟨s, A'⟩, hT, B', hB, ⟨r, hj⟩, -, rfl⟩
    rw [allSome_eq_some] at hB
    refine ⟨s, A', B', r, hj, ?_, fun x => ?_, rfl⟩
    · rw [hA, DVal.toType?_eq_some.mp hT]
    · have ⟨dB, hdB, hasTy⟩ := Option.bind_eq_some_iff.mp (hB x)
      rw [hdB, DVal.asTy_eq_some.mp hasTy]
  · rintro ⟨s, A', B', r, hj, hA, hB, rfl⟩
    refine ⟨_, hA, ⟨s, A'⟩, DVal.toType?_ofTy s A', B', ?_, ⟨r, hj⟩, CoCSort.joinWit_eq _, rfl⟩
    rw [allSome_eq_some]; intro x
    rw [hB x, Option.bind_some, DVal.asTy_ofTy]

theorem CoCTerm.interp_lam_eq_some {s' : CoCSort} {A B b : CoCTerm} {ρ : Nat → DVal.{u, v}}
    {d : DVal.{u, v}} :
    (CoCTerm.«λ» s' A B b).interp ρ = some d ↔
    ∃ (s : CoCSort) (A' : SemSort.Ty.{u, v} s.toSem)
      (B' : SemSort.El s.toSem A' → SemSort.Ty.{u, v} s'.toSem)
      (f : (x : SemSort.El s.toSem A') → SemSort.El s'.toSem (B' x))
      (r : CoCSort) (hj : s.join s' = some r),
      A.interp ρ = some (DVal.ofTy s A') ∧
      (∀ x, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' (B' x))) ∧
      (∀ x, b.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some ⟨s'.toSem, B' x, f x⟩) ∧
      d = ⟨r.toSem, CoCSort.pi s s' hj A' B', CoCSort.lam s s' hj A' B' f⟩ := by
  simp only [CoCTerm.interp, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨dA, hA, ⟨s, A'⟩, hT, B', hB, f, hf, ⟨r, hj⟩, -, rfl⟩
    rw [allSome_eq_some] at hB hf
    refine ⟨s, A', B', f, r, hj, ?_, fun x => ?_, fun x => ?_, rfl⟩
    · rw [hA, DVal.toType?_eq_some.mp hT]
    · have ⟨dB, hdB, hasTy⟩ := Option.bind_eq_some_iff.mp (hB x)
      rw [hdB, DVal.asTy_eq_some.mp hasTy]
    · have ⟨db, hdb, hget⟩ := Option.bind_eq_some_iff.mp (hf x)
      rw [hdb, DVal.get?_eq_some.mp hget]
  · rintro ⟨s, A', B', f, r, hj, hA, hB, hb, rfl⟩
    refine ⟨_, hA, ⟨s, A'⟩, DVal.toType?_ofTy s A', B', ?_, f, ?_, ⟨r, hj⟩,
      CoCSort.joinWit_eq _, rfl⟩
    · rw [allSome_eq_some]; intro x
      rw [hB x, Option.bind_some, DVal.asTy_ofTy]
    · rw [allSome_eq_some]; intro x
      rw [hb x, Option.bind_some, DVal.get?_mk]

theorem CoCTerm.interp_app_eq_some {s' : CoCSort} {A B f a : CoCTerm} {ρ : Nat → DVal.{u, v}}
    {d : DVal.{u, v}} :
    (CoCTerm.a s' A B f a).interp ρ = some d ↔
    ∃ (s : CoCSort) (A' : SemSort.Ty.{u, v} s.toSem)
      (B' : SemSort.El s.toSem A' → SemSort.Ty.{u, v} s'.toSem)
      (r : CoCSort) (hj : s.join s' = some r)
      (fv : SemSort.El r.toSem (CoCSort.pi s s' hj A' B')) (av : SemSort.El s.toSem A'),
      A.interp ρ = some (DVal.ofTy s A') ∧
      (∀ x, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' (B' x))) ∧
      f.interp ρ = some ⟨r.toSem, CoCSort.pi s s' hj A' B', fv⟩ ∧
      a.interp ρ = some ⟨s.toSem, A', av⟩ ∧
      d = ⟨s'.toSem, B' av, CoCSort.app s s' hj A' B' fv av⟩ := by
  simp only [CoCTerm.interp, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨dA, hA, ⟨s, A'⟩, hT, B', hB, ⟨r, hj⟩, -, fv, ⟨df, hf, hfv⟩, av, ⟨da, ha, hav⟩, rfl⟩
    rw [allSome_eq_some] at hB
    refine ⟨s, A', B', r, hj, fv, av, ?_, fun x => ?_, ?_, ?_, rfl⟩
    · rw [hA, DVal.toType?_eq_some.mp hT]
    · have ⟨dB, hdB, hasTy⟩ := Option.bind_eq_some_iff.mp (hB x)
      rw [hdB, DVal.asTy_eq_some.mp hasTy]
    · rw [hf, DVal.get?_eq_some.mp hfv]
    · rw [ha, DVal.get?_eq_some.mp hav]
  · rintro ⟨s, A', B', r, hj, fv, av, hA, hB, hf, ha, rfl⟩
    refine ⟨_, hA, ⟨s, A'⟩, DVal.toType?_ofTy s A', B', ?_, ⟨r, hj⟩, CoCSort.joinWit_eq _,
      fv, ⟨_, hf, DVal.get?_mk _ _ _⟩, av, ⟨_, ha, DVal.get?_mk _ _ _⟩, rfl⟩
    rw [allSome_eq_some]; intro x
    rw [hB x, Option.bind_some, DVal.asTy_ofTy]

/-- `∀ x : A, B` is the Lean `∀` whenever its parts are interpreted as types -/
theorem CoCTerm.interp_forall_of {s s' r : CoCSort} (hj : s.join s' = some r) {A B : CoCTerm}
    {ρ : Nat → DVal.{u, v}} {A' : SemSort.Ty.{u, v} s.toSem}
    {B' : SemSort.El s.toSem A' → SemSort.Ty.{u, v} s'.toSem}
    (hA : A.interp ρ = some (DVal.ofTy s A'))
    (hB : ∀ x, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' (B' x))) :
    (CoCTerm.«∀» s' A B).interp ρ = some (DVal.ofTy r (CoCSort.pi s s' hj A' B')) :=
  CoCTerm.interp_forall_eq_some.mpr ⟨s, A', B', r, hj, hA, hB, rfl⟩

/-- `t`, if it is syntactically a sort -/
def CoCTerm.sort? : CoCTerm → Option CoCSort
  | .t (.sort s) => some s
  | _            => none

/--
  `T` read as a type: the level of `T`, together with the type at that level. A
  sort `Sort s` is read directly, since a top sort has no value
-/
noncomputable def CoCTerm.interpTy (T : CoCTerm) (ρ : Nat → DVal.{u, v}) :
    Option ((l : SemSort) × SemSort.Ty.{u, v} l) :=
  match T.sort? with
  | some s => some ⟨s.sortOf, s.sortCode⟩
  | none   => ((T.interp ρ).bind DVal.toType?).map fun sA => ⟨sA.1.toSem, sA.2⟩

theorem CoCTerm.interpTy_of_sort? {T : CoCTerm} {s : CoCSort} (h : T.sort? = some s)
    (ρ : Nat → DVal.{u, v}) : T.interpTy ρ = some ⟨s.sortOf, s.sortCode⟩ := by
  unfold CoCTerm.interpTy; rw [h]

theorem CoCTerm.interpTy_of_interp {T : CoCTerm} {ρ : Nat → DVal.{u, v}} {s : CoCSort}
    {A : SemSort.Ty.{u, v} s.toSem} (hs : T.sort? = none) (h : T.interp ρ = some (DVal.ofTy s A)) :
    T.interpTy ρ = some ⟨s.toSem, A⟩ := by
  unfold CoCTerm.interpTy; rw [hs, h, Option.bind_some, DVal.toType?_ofTy]; rfl

/-- `Sort s` is read as a type directly, see `CoCTerm.interpTy` -/
theorem CoCSort.interpTy_toCoCTerm (s : CoCSort) (ρ : Nat → DVal.{u, v}) :
    s.toCoCTerm.interpTy ρ = some ⟨s.sortOf, s.sortCode⟩ :=
  CoCTerm.interpTy_of_sort? rfl ρ

/-- The term of a `ConstTy` is closed, so de Bruijn operations leave it unchanged -/
theorem ConstTy.mapBVarAt_toCoCTerm (σ : ConstTy) (idx : Nat) (f : Nat → Nat) :
    σ.toCoCTerm.mapBVarAt idx f = σ.toCoCTerm := by
  induction σ generalizing idx f with
  | prop | bool | nat => rfl
  | func σ τ ihσ ihτ =>
    simp only [ConstTy.toCoCTerm, CoCTerm.mkFunc, CoCTerm.bvarLifts, CoCTerm.bvarLiftsIdx,
      CoCTerm.mapBVarAt, ihσ, ihτ]

/-- The term of a `ConstTy` is the Lean type it stands for, as a type in `Sort 1` -/
theorem ConstTy.interp_toCoCTerm (σ : ConstTy) (ρ : Nat → DVal.{u, v}) :
    σ.toCoCTerm.interp ρ = some (DVal.ofTy .«1» ⟨σ.interp⟩) := by
  induction σ generalizing ρ with
  | prop | bool | nat => rfl
  | func σ τ ihσ ihτ =>
    refine CoCTerm.interp_forall_of (s := .«1») (s' := .«1») (B' := fun _ => ⟨τ.interp⟩) rfl
      (ihσ ρ) fun _ => ?_
    rw [CoCTerm.bvarLifts, CoCTerm.bvarLiftsIdx, ConstTy.mapBVarAt_toCoCTerm]
    exact ihτ _

theorem ConstTy.interpTy_toCoCTerm (σ : ConstTy) (ρ : Nat → DVal.{u, v}) :
    σ.toCoCTerm.interpTy ρ = some ⟨.«1», ⟨σ.interp⟩⟩ := by
  cases σ
  case prop => exact CoCSort.interpTy_toCoCTerm .prop ρ
  all_goals exact CoCTerm.interpTy_of_interp rfl (ConstTy.interp_toCoCTerm _ ρ)

/-- `Sort s` has the type `Sort (s + 1)` that `CoCSort.succ` assigns it -/
theorem CoCSort.interp_check {s s₁ : CoCSort} (h : s.succ = some s₁) (ρ : Nat → DVal.{u, v}) :
    ∃ d, s.sortVal = some d ∧ s₁.toCoCTerm.interpTy ρ = some ⟨d.s, d.ty⟩ := by
  cases s <;> cases h <;> exact ⟨_, rfl, CoCSort.interpTy_toCoCTerm _ ρ⟩

/-- Each base term has the type that `CoCBaseTerm.check` assigns it, in every environment -/
theorem CoCBaseTerm.interp_check {b : CoCBaseTerm} {T : CoCTerm} (h : b.check = some T)
    (ρ : Nat → DVal.{u, v}) : ∃ d, b.interp = some d ∧ T.interpTy ρ = some ⟨d.s, d.ty⟩ := by
  cases b with
  | sort s =>
    obtain ⟨s₁, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact CoCSort.interp_check hs ρ
  | bool | nat => cases h; exact ⟨_, rfl, CoCSort.interpTy_toCoCTerm .«1» ρ⟩
  | pcst c | bcst c | ncst c => cases h; exact ⟨_, rfl, ConstTy.interpTy_toCoCTerm _ ρ⟩

end Auto.Embedding.CoC
