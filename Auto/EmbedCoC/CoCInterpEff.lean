module

public import Auto.EmbedCoC.CoCSound
public import Auto.EmbedCoC.CoCInfer

@[expose] public section

/-!
  The efficient interpretation of the embedded system: the value of a term whose
  reference interpretation is defined, computed by recursion on the term. Where the
  reference interpretation decides classically that a value has a type, the efficient
  one casts the value along a proof that it has. The kernel reduces such a cast as soon
  as both sides of the proof evaluate to the same type (by the `K`-like reduction of
  `Eq`), without looking at the proof. So the efficient interpretation of a term reified
  from a Lean expression evaluates to that expression, and it agrees with the reference
  interpretation by construction.

  It is noncomputable only because the value of `Bool.ofProp` is: it is meant to be
  evaluated by the kernel
-/

namespace Auto.Embedding.CoC

universe u v

/-- The value of `o`, when it has one -/
def getSome {α : Sort _} (o : Option α) (h : ∃ a, o = some a) : {a // o = some a} :=
  ⟨o.get (by obtain ⟨a, rfl⟩ := h; rfl), (Option.some_get _).symm⟩

/-! ## Casts -/

/-- `d` as a type at sort `s`, when it is one. See `DVal.asTy` -/
def DVal.castTy (d : DVal.{u, v}) (s : CoCSort) (h : ∃ A, d = DVal.ofTy s A) :
    {A : SemSort.Ty.{u, v} s.toSem // d = DVal.ofTy s A} :=
  ⟨s.tyDown (d.castTo (by obtain ⟨A, rfl⟩ := h; rfl)), by
    obtain ⟨A, rfl⟩ := h
    exact (congrArg (DVal.ofTy s) (CoCSort.tyDown_tyUp s A)).symm⟩

/--
  `d` as a type, at the sort that the level of `d` determines, when it is one. See
  `DVal.toType?`
-/
def DVal.castType (d : DVal.{u, v}) (h : ∃ s A, d = DVal.ofTy s A) :
    {sA : (s : CoCSort) × SemSort.Ty.{u, v} s.toSem // d = DVal.ofTy sA.1 sA.2} :=
  match hs : d.s.pred? with
  | some s =>
    let A := d.castTy s (by
      obtain ⟨s₀, A₀, rfl⟩ := h
      obtain rfl : s₀ = s := Option.some.inj ((CoCSort.pred?_sortOf s₀).symm.trans hs)
      exact ⟨A₀, rfl⟩)
    ⟨⟨s, A.1⟩, A.2⟩
  | none => False.elim (by
    obtain ⟨s₀, A₀, rfl⟩ := h
    cases (CoCSort.pred?_sortOf s₀).symm.trans hs)

/-- An evaluator for `t` in `ρ`: the value of `t`, whenever it has one -/
abbrev CoCTerm.Eval (t : CoCTerm) (ρ : Nat → DVal.{u, v}) : SemSortMax.{u, v} :=
  (∃ d, t.interp ρ = some d) → {d // t.interp ρ = some d}

/-- The value of `t` as an element of `T` at level `l`, when it is one. See `DVal.get?` -/
def CoCTerm.Eval.get {t : CoCTerm} {ρ : Nat → DVal.{u, v}} (ev : t.Eval ρ) {l : SemSort}
    {T : SemSort.Ty.{u, v} l} (h : ∃ x, t.interp ρ = some ⟨l, T, x⟩) :
    {x : SemSort.El l T // t.interp ρ = some ⟨l, T, x⟩} :=
  let d := ev (h.elim fun _ hx => ⟨_, hx⟩)
  let hT : (⟨d.1.s, d.1.ty⟩ : (l : SemSort) × SemSort.Ty.{u, v} l) = ⟨l, T⟩ :=
    h.elim fun _ hx => congrArg (fun d : DVal => (⟨d.s, d.ty⟩ : (l : SemSort) × SemSort.Ty l))
      (Option.some.inj (d.2.symm.trans hx))
  ⟨d.1.castTo hT, d.2.trans (congrArg some (d.1.eq_castTo hT))⟩

/-- The value of `t` as a type at sort `s`, when it is one. See `DVal.asTy` -/
def CoCTerm.Eval.asTy {t : CoCTerm} {ρ : Nat → DVal.{u, v}} (ev : t.Eval ρ) {s : CoCSort}
    (h : ∃ A, t.interp ρ = some (DVal.ofTy s A)) :
    {A : SemSort.Ty.{u, v} s.toSem // t.interp ρ = some (DVal.ofTy s A)} :=
  let d := ev (h.elim fun _ hA => ⟨_, hA⟩)
  let A := d.1.castTy s (h.elim fun _ hA => ⟨_, Option.some.inj (d.2.symm.trans hA)⟩)
  ⟨A.1, d.2.trans (congrArg some A.2)⟩

/-- The value of `t` as a type, at the sort that its level determines. See `DVal.toType?` -/
def CoCTerm.Eval.toType {t : CoCTerm} {ρ : Nat → DVal.{u, v}} (ev : t.Eval ρ)
    (h : ∃ s A, t.interp ρ = some (DVal.ofTy s A)) :
    {sA : (s : CoCSort) × SemSort.Ty.{u, v} s.toSem // t.interp ρ = some (DVal.ofTy sA.1 sA.2)} :=
  let d := ev (h.elim fun _ h => h.elim fun _ hA => ⟨_, hA⟩)
  let sA := d.1.castType (h.elim fun _ h => h.elim fun _ hA =>
    ⟨_, _, Option.some.inj (d.2.symm.trans hA)⟩)
  ⟨sA.1, d.2.trans (congrArg some sA.2)⟩

/-! ## Binders -/

/--
  The interpretation of a binder `x : A` whose body is a type `B` at sort `s'`, as the
  reference interpretations of `∀`, `λ` and application compute it. It is unique, so
  the efficient interpretation can compute it once and use what the reference
  interpretation says about any
-/
structure BinderVal (s' : CoCSort) (A B : CoCTerm) (ρ : Nat → DVal.{u, v}) : SemSortMax.{u, v} where
  /-- The sort of `A` -/
  s  : CoCSort
  /-- The value of `A` -/
  A' : SemSort.Ty.{u, v} s.toSem
  /-- The value of `B`, as a function of the value of `x` -/
  B' : SemSort.El s.toSem A' → SemSort.Ty.{u, v} s'.toSem
  /-- The sort of `∀_{s'} x : A, B` -/
  r  : CoCSort
  hj : s.join s' = some r
  hA : A.interp ρ = some (DVal.ofTy s A')
  hB : ∀ x, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' (B' x))

instance {s' : CoCSort} {A B : CoCTerm} {ρ : Nat → DVal.{u, v}} :
    Subsingleton (BinderVal s' A B ρ) where
  allEq := fun ⟨s₁, A₁, B₁, r₁, hj₁, hA₁, hB₁⟩ ⟨s₂, A₂, B₂, r₂, hj₂, hA₂, hB₂⟩ => by
    obtain ⟨rfl, hAA⟩ := DVal.ofTy_inj (Option.some.inj (hA₁.symm.trans hA₂))
    cases eq_of_heq hAA
    have hBB : B₁ = B₂ := funext fun x =>
      eq_of_heq (DVal.ofTy_inj (Option.some.inj ((hB₁ x).symm.trans (hB₂ x)))).2
    subst hBB
    cases Option.some.inj (hj₁.symm.trans hj₂)
    rfl

namespace BinderVal

variable {s' : CoCSort} {A B : CoCTerm} {ρ : Nat → DVal.{u, v}}

/-- `B` is a type at sort `s'` for every value of `x`, whichever way the value of `A` is computed -/
theorem exists_B (bv : BinderVal s' A B ρ) {s : CoCSort} {A' : SemSort.Ty.{u, v} s.toSem}
    (hA : A.interp ρ = some (DVal.ofTy s A')) (x : SemSort.El s.toSem A') :
    ∃ B₀, B.interp (pushLCtx ⟨s.toSem, A', x⟩ ρ) = some (DVal.ofTy s' B₀) := by
  obtain ⟨rfl, hAA⟩ := DVal.ofTy_inj (Option.some.inj (hA.symm.trans bv.hA))
  cases eq_of_heq hAA
  exact ⟨_, bv.hB x⟩

theorem joinWit_isSome (bv : BinderVal s' A B ρ) {s : CoCSort} {A' : SemSort.Ty.{u, v} s.toSem}
    (hA : A.interp ρ = some (DVal.ofTy s A')) : (s.joinWit s').isSome := by
  obtain ⟨rfl, -⟩ := DVal.ofTy_inj (Option.some.inj (hA.symm.trans bv.hA))
  rw [CoCSort.joinWit_eq ⟨bv.r, bv.hj⟩]; rfl

/--
  The interpretation of a binder, computed from evaluators for `A` and `B`. Its
  proofs appear only in casts
-/
def eval (h : Nonempty (BinderVal s' A B ρ)) (evA : A.Eval ρ)
    (evB : (s : CoCSort) → (A' : SemSort.Ty.{u, v} s.toSem) → (x : SemSort.El s.toSem A') →
      B.Eval (pushLCtx ⟨s.toSem, A', x⟩ ρ)) : BinderVal s' A B ρ :=
  let sA := evA.toType (h.elim fun bv => ⟨_, _, bv.hA⟩)
  let B' := fun x => (evB sA.1.1 sA.1.2 x).asTy (h.elim fun bv => bv.exists_B sA.2 x)
  let r := (sA.1.1.joinWit s').get (h.elim fun bv => bv.joinWit_isSome sA.2)
  ⟨sA.1.1, sA.1.2, fun x => (B' x).1, r.1, r.2, sA.2, fun x => (B' x).2⟩

theorem of_forall (h : ∃ d, (CoCTerm.«∀» s' A B).interp ρ = some d) :
    Nonempty (BinderVal s' A B ρ) := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨s, A', B', r, hj, hA, hB, -⟩ := CoCTerm.interp_forall_eq_some.mp hd
  exact ⟨⟨s, A', B', r, hj, hA, hB⟩⟩

theorem of_lam {b : CoCTerm} (h : ∃ d, (CoCTerm.«λ» s' A B b).interp ρ = some d) :
    Nonempty (BinderVal s' A B ρ) := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨s, A', B', f, r, hj, hA, hB, -⟩ := CoCTerm.interp_lam_eq_some.mp hd
  exact ⟨⟨s, A', B', r, hj, hA, hB⟩⟩

theorem of_app {f a : CoCTerm} (h : ∃ d, (CoCTerm.a s' A B f a).interp ρ = some d) :
    Nonempty (BinderVal s' A B ρ) := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨s, A', B', r, hj, fv, av, hA, hB, -⟩ := CoCTerm.interp_app_eq_some.mp hd
  exact ⟨⟨s, A', B', r, hj, hA, hB⟩⟩

/-- The body of an abstraction is an element of `B` for every value of `x` -/
theorem lam_body {b : CoCTerm} (h : ∃ d, (CoCTerm.«λ» s' A B b).interp ρ = some d)
    (bv : BinderVal s' A B ρ) (x : SemSort.El bv.s.toSem bv.A') :
    ∃ y, b.interp (pushLCtx ⟨bv.s.toSem, bv.A', x⟩ ρ) = some ⟨s'.toSem, bv.B' x, y⟩ := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨s, A', B', f, r, hj, hA, hB, hb, -⟩ := CoCTerm.interp_lam_eq_some.mp hd
  cases Subsingleton.elim (⟨s, A', B', r, hj, hA, hB⟩ : BinderVal s' A B ρ) bv
  exact ⟨f x, hb x⟩

/-- The function of an application is an element of `∀ x : A, B` -/
theorem app_fn {f a : CoCTerm} (h : ∃ d, (CoCTerm.a s' A B f a).interp ρ = some d)
    (bv : BinderVal s' A B ρ) :
    ∃ y, f.interp ρ = some ⟨bv.r.toSem, CoCSort.pi bv.s s' bv.hj bv.A' bv.B', y⟩ := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨s, A', B', r, hj, fv, av, hA, hB, hf, -⟩ := CoCTerm.interp_app_eq_some.mp hd
  cases Subsingleton.elim (⟨s, A', B', r, hj, hA, hB⟩ : BinderVal s' A B ρ) bv
  exact ⟨fv, hf⟩

/-- The argument of an application is an element of `A` -/
theorem app_arg {f a : CoCTerm} (h : ∃ d, (CoCTerm.a s' A B f a).interp ρ = some d)
    (bv : BinderVal s' A B ρ) : ∃ y, a.interp ρ = some ⟨bv.s.toSem, bv.A', y⟩ := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨s, A', B', r, hj, fv, av, hA, hB, -, ha, -⟩ := CoCTerm.interp_app_eq_some.mp hd
  cases Subsingleton.elim (⟨s, A', B', r, hj, hA, hB⟩ : BinderVal s' A B ρ) bv
  exact ⟨av, ha⟩

end BinderVal

/-! ## The efficient interpretation -/

/--
  The value of `t` in the environment `ρ`, whenever `t` has one: the efficient
  counterpart of `CoCTerm.interp`. Each binder is interpreted once, by
  `BinderVal.eval`, and the values of the subterms are cast to the types that the
  binder determines
-/
noncomputable def CoCTerm.interpEff : (t : CoCTerm) → (ρ : Nat → DVal.{u, v}) →
    (∃ d, t.interp ρ = some d) → {d // t.interp ρ = some d}
  | .b n, ρ, _ => ⟨ρ n, rfl⟩
  | .t bt, _, h => getSome bt.interp h
  | .a s' A B fn arg, ρ, h =>
    let bv := BinderVal.eval (BinderVal.of_app h) (A.interpEff ρ) fun _ A' x =>
      B.interpEff (pushLCtx ⟨_, A', x⟩ ρ)
    let fv := CoCTerm.Eval.get (fn.interpEff ρ) (bv.app_fn h)
    let av := CoCTerm.Eval.get (arg.interpEff ρ) (bv.app_arg h)
    ⟨⟨s'.toSem, bv.B' av.1, CoCSort.app bv.s s' bv.hj bv.A' bv.B' fv.1 av.1⟩,
      CoCTerm.interp_app_eq_some.mpr ⟨_, _, _, _, bv.hj, _, _, bv.hA, bv.hB, fv.2, av.2, rfl⟩⟩
  | .«λ» s' A B body, ρ, h =>
    let bv := BinderVal.eval (BinderVal.of_lam h) (A.interpEff ρ) fun _ A' x =>
      B.interpEff (pushLCtx ⟨_, A', x⟩ ρ)
    let f := fun x => CoCTerm.Eval.get (body.interpEff (pushLCtx ⟨bv.s.toSem, bv.A', x⟩ ρ))
      (bv.lam_body h x)
    ⟨⟨bv.r.toSem, CoCSort.pi bv.s s' bv.hj bv.A' bv.B',
        CoCSort.lam bv.s s' bv.hj bv.A' bv.B' fun x => (f x).1⟩,
      CoCTerm.interp_lam_eq_some.mpr ⟨_, _, _, _, _, bv.hj, bv.hA, bv.hB, fun x => (f x).2, rfl⟩⟩
  | .«∀» s' A B, ρ, h =>
    let bv := BinderVal.eval (BinderVal.of_forall h) (A.interpEff ρ) fun _ A' x =>
      B.interpEff (pushLCtx ⟨_, A', x⟩ ρ)
    ⟨.ofTy bv.r (CoCSort.pi bv.s s' bv.hj bv.A' bv.B'), CoCTerm.interp_forall_of bv.hj bv.hA bv.hB⟩

/--
  The efficient interpretation of a derivation of `Γ ⊢ t : T` in an environment `ρ`
  that fits `Γ`: an element of the type `Tv` at level `l` that `T` denotes
-/
noncomputable def HasType.interpEff {Γ : List CoCTerm} {t T : CoCTerm} (h : HasType Γ t T)
    (ρ : Nat → DVal.{u, v}) (hρ : EnvFits ρ Γ) {l : SemSort} {Tv : SemSort.Ty.{u, v} l}
    (hT : T.interpTy ρ = some ⟨l, Tv⟩) : SemSort.El l Tv :=
  (CoCTerm.Eval.get (t.interpEff ρ) ⟨_, h.interp_eq ρ hρ hT⟩).1

/-- The two interpretations of a derivation agree -/
theorem HasType.interpEff_eq {Γ : List CoCTerm} {t T : CoCTerm} (h : HasType Γ t T)
    (ρ : Nat → DVal.{u, v}) (hρ : EnvFits ρ Γ) {l : SemSort} {Tv : SemSort.Ty.{u, v} l}
    (hT : T.interpTy ρ = some ⟨l, Tv⟩) : h.interpEff ρ hρ hT = h.interp ρ hρ hT :=
  eq_of_heq (DVal.mk.inj (Option.some.inj
    ((CoCTerm.Eval.get (t.interpEff ρ) ⟨_, h.interp_eq ρ hρ hT⟩).2.symm.trans
      (h.interp_eq ρ hρ hT)))).2.2

-- Regression checks: the kernel evaluates the efficient interpretation of a checked
-- term to the Lean expression it stands for

/-- The polymorphic identity, with its type `∀ α : Type, α → α` -/
example (ρ : Nat → DVal.{u, v}) (T t : CoCTerm)
    (eT : T = .«∀» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1)))
    (et : t = .«λ» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1))
      (.«λ» .«1» (.b 0) (.b 1) (.b 0))) :
    ∃ (h : HasType [] t T) (hT : T.interpTy ρ = some ⟨.«2», ⟨∀ α : Type, α → α⟩⟩),
      h.interpEff ρ trivial hT = GLift.up fun (α : Type) (x : α) => x := by
  have hT : HasType [] T (CoCSort.toCoCTerm .«2») := by
    subst eT; exact infer_sound (fuel := 0) .nil rfl
  subst eT et
  exact ⟨infer_sound (fuel := 0) .nil rfl, CoCTerm.interpTy_of_ofTy
    (CoCTerm.interpEff _ ρ ((hT.sound ρ trivial).imp fun _ h => h.1)).2, rfl⟩

/-- `∀ p : α → Prop, ∀ x : α, p x → p x` in the context `α : Type`, where `α` is `Nat` -/
example (ρ : Nat → DVal.{u, v}) (t : CoCTerm)
    (et : t = .«∀» .prop (.«∀» .«1» (.b 0) sort0) (.«∀» .prop (.b 1)
      (.«∀» .prop (.a .«1» (.b 2) sort0 (.b 1) (.b 0)) (.a .«1» (.b 3) sort0 (.b 2) (.b 1))))) :
    ∃ h : HasType [CoCSort.toCoCTerm .«1»] t sort0,
      (t.interpEff (pushLCtx (DVal.ofTy .«1» ⟨Nat⟩) ρ)
        ((h.sound _ (EnvFits.push rfl trivial)).imp fun _ h => h.1)).1 =
      DVal.ofTy .prop ⟨∀ p : Nat → Prop, ∀ x : Nat, p x → p x⟩ := by
  subst et
  exact ⟨infer_sound (fuel := 0) (checkCtx_sound (fuel := 0) rfl) rfl, rfl⟩

end Auto.Embedding.CoC
