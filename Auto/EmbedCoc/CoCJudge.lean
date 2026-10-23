module

public import Auto.EmbedCoc.CoCBase

@[expose] public section

/-!
  The typing judgement of the embedded system, in the style of a pure type system
  (cf. Barendregt, *Lambda Calculi with Types*, 1992). A context is a list of types,
  innermost binder first, and the type of the de Bruijn index `n` is written in the
  context of the entries after it.

  Conversion is `β`-joinability: two types are convertible when they reduce to a
  common term. Reducing a term whose interpretation is defined preserves the
  interpretation, so the soundness of conversion needs neither confluence nor
  subject reduction. Without confluence, joinability need not be transitive, but the
  conversion rule can be applied repeatedly instead
-/

namespace Auto.Embedding.CoC

/--
  One step of `β`-reduction, anywhere in a term. A redex reduces only when the
  annotations of the application agree with those of the abstraction, as they do in
  a term reified from Lean
-/
inductive CoCTerm.Red1 : CoCTerm → CoCTerm → Prop
  | beta (s' : CoCSort) (A B b a : CoCTerm) :
    Red1 (.a s' A B (.«λ» s' A B b) a) (CoCTerm.instantiate1 a b)
  | aArgTy {s' : CoCSort} {A A' B f a : CoCTerm} :
    Red1 A A' → Red1 (.a s' A B f a) (.a s' A' B f a)
  | aResTy {s' : CoCSort} {A B B' f a : CoCTerm} :
    Red1 B B' → Red1 (.a s' A B f a) (.a s' A B' f a)
  | aFn {s' : CoCSort} {A B f f' a : CoCTerm} :
    Red1 f f' → Red1 (.a s' A B f a) (.a s' A B f' a)
  | aArg {s' : CoCSort} {A B f a a' : CoCTerm} :
    Red1 a a' → Red1 (.a s' A B f a) (.a s' A B f a')
  | lamArgTy {s' : CoCSort} {A A' B b : CoCTerm} :
    Red1 A A' → Red1 (.«λ» s' A B b) (.«λ» s' A' B b)
  | lamResTy {s' : CoCSort} {A B B' b : CoCTerm} :
    Red1 B B' → Red1 (.«λ» s' A B b) (.«λ» s' A B' b)
  | lamBody {s' : CoCSort} {A B b b' : CoCTerm} :
    Red1 b b' → Red1 (.«λ» s' A B b) (.«λ» s' A B b')
  | forallArgTy {s' : CoCSort} {A A' B : CoCTerm} :
    Red1 A A' → Red1 (.«∀» s' A B) (.«∀» s' A' B)
  | forallBodyTy {s' : CoCSort} {A B B' : CoCTerm} :
    Red1 B B' → Red1 (.«∀» s' A B) (.«∀» s' A B')

/-- Many steps of `β`-reduction: the reflexive transitive closure of `CoCTerm.Red1` -/
inductive CoCTerm.Red : CoCTerm → CoCTerm → Prop
  | refl (t : CoCTerm) : Red t t
  | step {t t' t'' : CoCTerm} : Red1 t t' → Red t' t'' → Red t t''

theorem CoCTerm.Red.single {t t' : CoCTerm} (h : Red1 t t') : Red t t' :=
  .step h (.refl _)

theorem CoCTerm.Red.trans {t t' t'' : CoCTerm} : Red t t' → Red t' t'' → Red t t''
  | .refl _,     h => h
  | .step h₁ h₂, h => .step h₁ (h₂.trans h)

/-- `A` and `B` reduce to a common term, which is when they are convertible -/
def CoCTerm.Joinable (A B : CoCTerm) : Prop := ∃ C, A.Red C ∧ B.Red C

theorem CoCTerm.Joinable.refl (t : CoCTerm) : Joinable t t := ⟨t, .refl t, .refl t⟩

theorem CoCTerm.Joinable.symm {A B : CoCTerm} : Joinable A B → Joinable B A
  | ⟨C, hA, hB⟩ => ⟨C, hB, hA⟩

theorem CoCTerm.Joinable.of_red {A B : CoCTerm} (h : Red A B) : Joinable A B :=
  ⟨B, h, .refl B⟩

/-- The two forms of judgement -/
inductive JudgeForm
  /-- The context is well formed -/
  | wf
  /-- `t : T` in the context -/
  | hasType (t T : CoCTerm)

/--
  The judgements of the embedded system, as one family indexed by their form rather
  than as two mutual inductive types, so that `induction` applies. See `WfCtx` and
  `HasType`, which name the two forms. In `Γ ⊢ t : T`, the type `T` can be a top sort,
  such as `Sort 2`, which has no type of its own; otherwise it is a type, see
  `Judge.conv`
-/
inductive Judge : List CoCTerm → JudgeForm → Prop
  /-- The empty context is well formed -/
  | nil : Judge [] .wf
  /-- `A :: Γ` is well formed when `A` is a type in `Γ` -/
  | cons {Γ : List CoCTerm} {A : CoCTerm} {s : CoCSort} :
    Judge Γ (.hasType A s.toCoCTerm) → Judge (A :: Γ) .wf
  /--
    ---------------   where `T` is the type of the base term `c`
      Γ ⊢ c : T
  -/
  | base {Γ : List CoCTerm} {b : CoCBaseTerm} {T : CoCTerm} :
    Judge Γ .wf → b.check = some T → Judge Γ (.hasType (.t b) T)
  /--
    ---------------------   where `A = Γ[n]`, written in the context `Γ.drop (n + 1)`
      Γ ⊢ xₙ : ↑ⁿ⁺¹ A
  -/
  | var {Γ : List CoCTerm} {n : Nat} {A : CoCTerm} :
    Judge Γ .wf → Γ[n]? = some A → Judge Γ (.hasType (.b n) (A.bvarLifts (n + 1)))
  /--
      Γ ⊢ A : Sort s    A :: Γ ⊢ B : Sort s'
    ------------------------------------------   where `join s s' = some r`
          Γ ⊢ (∀_{s'} x : A, B) : Sort r
  -/
  | pi {Γ : List CoCTerm} {A B : CoCTerm} {s s' r : CoCSort} :
    Judge Γ (.hasType A s.toCoCTerm) → Judge (A :: Γ) (.hasType B s'.toCoCTerm) →
    s.join s' = some r → Judge Γ (.hasType (.«∀» s' A B) r.toCoCTerm)
  /--
      Γ ⊢ (∀_{s'} x : A, B) : Sort r    A :: Γ ⊢ b : B
    ---------------------------------------------------
          Γ ⊢ (λ_{s'} x : A, B, b) : ∀_{s'} x : A, B
  -/
  | lam {Γ : List CoCTerm} {A B b : CoCTerm} {s' r : CoCSort} :
    Judge Γ (.hasType (.«∀» s' A B) r.toCoCTerm) → Judge (A :: Γ) (.hasType b B) →
    Judge Γ (.hasType (.«λ» s' A B b) (.«∀» s' A B))
  /--
      Γ ⊢ f : ∀_{s'} x : A, B    Γ ⊢ a : A
    ----------------------------------------
          Γ ⊢ f a : B[a / x]
  -/
  | app {Γ : List CoCTerm} {A B f a : CoCTerm} {s' : CoCSort} :
    Judge Γ (.hasType f (.«∀» s' A B)) → Judge Γ (.hasType a A) →
    Judge Γ (.hasType (.a s' A B f a) (CoCTerm.instantiate1 a B))
  /--
      Γ ⊢ t : A    Γ ⊢ B : Sort s
    -------------------------------   where `A` and `B` are joinable
              Γ ⊢ t : B
  -/
  | conv {Γ : List CoCTerm} {t A B : CoCTerm} {s : CoCSort} :
    Judge Γ (.hasType t A) → Judge Γ (.hasType B s.toCoCTerm) → A.Joinable B →
    Judge Γ (.hasType t B)

/-- `Γ` is a well-formed context: each entry is a type, in the context of the entries after it -/
abbrev WfCtx (Γ : List CoCTerm) : Prop := Judge Γ .wf

/-- `Γ ⊢ t : T` -/
abbrev HasType (Γ : List CoCTerm) (t T : CoCTerm) : Prop := Judge Γ (.hasType t T)

/-- A judgement lives in a well-formed context -/
theorem Judge.wfCtx {Γ : List CoCTerm} {j : JudgeForm} (h : Judge Γ j) : WfCtx Γ := by
  induction h with
  | nil => exact .nil
  | cons h => exact .cons h
  | base h | var h => exact h
  | pi _ _ _ ih | lam _ _ ih | app _ _ ih | conv _ _ _ ih => exact ih

theorem HasType.wfCtx {Γ : List CoCTerm} {t T : CoCTerm} (h : HasType Γ t T) : WfCtx Γ :=
  Judge.wfCtx h

/-! Derived rules, which build the well-formed contexts that the primitive rules take -/

/-- `Judge.var`, where `rfl` checks the type of the variable by computing it -/
theorem Judge.var' {Γ : List CoCTerm} {n : Nat} {T : CoCTerm} (hΓ : WfCtx Γ)
    (h : Γ[n]?.map (·.bvarLifts (n + 1)) = some T) : HasType Γ (.b n) T := by
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
  exact .var hΓ hA

/-- `Judge.pi`, where `B` is derived in the context `A :: Γ`, given that it is well formed -/
theorem Judge.pi' {Γ : List CoCTerm} {A B : CoCTerm} {s s' r : CoCSort}
    (hA : HasType Γ A s.toCoCTerm) (hj : s.join s' = some r)
    (hB : WfCtx (A :: Γ) → HasType (A :: Γ) B s'.toCoCTerm) :
    HasType Γ (.«∀» s' A B) r.toCoCTerm :=
  .pi hA (hB (.cons hA)) hj

/--
  `Judge.lam`, where `B` and `b` are derived in the context `A :: Γ`, given that it is
  well formed
-/
theorem Judge.lam' {Γ : List CoCTerm} {A B b : CoCTerm} {s s' r : CoCSort}
    (hA : HasType Γ A s.toCoCTerm) (hj : s.join s' = some r)
    (hB : WfCtx (A :: Γ) → HasType (A :: Γ) B s'.toCoCTerm)
    (hb : WfCtx (A :: Γ) → HasType (A :: Γ) b B) :
    HasType Γ (.«λ» s' A B b) (.«∀» s' A B) :=
  .lam (.pi' hA hj hB) (hb (.cons hA))


-- Regression checks: small derivations
section Examples

/-- The polymorphic identity `λ α : Type, λ x : α, x : ∀ α : Type, α → α` -/
example : HasType []
    (.«λ» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1)) (.«λ» .«1» (.b 0) (.b 1) (.b 0)))
    (.«∀» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1))) :=
  .lam' (.base .nil rfl) rfl (fun wf => .pi' (.var' wf rfl) rfl fun wf => .var' wf rfl)
    fun wf => .lam' (.var' wf rfl) rfl (fun wf => .var' wf rfl) fun wf => .var' wf rfl

/-- The type-level function `λ x : Nat, Nat`, of type `∀ x : Nat, Sort 1` -/
abbrev constNat : CoCTerm := .«λ» .«2» tyNat (CoCSort.toCoCTerm .«1») tyNat

/-- `3 : (λ x : Nat, Nat) 3`, by `β`-conversion -/
example : HasType [] (.t (.ncst (.natVal 3)))
    (.a .«2» tyNat (CoCSort.toCoCTerm .«1») constNat (.t (.ncst (.natVal 3)))) :=
  .conv (.base .nil rfl)
    (.app (.lam' (.base .nil rfl) rfl (fun wf => .base wf rfl) fun wf => .base wf rfl)
      (.base .nil rfl))
    ⟨tyNat, .refl _, .single (.beta _ _ _ _ _)⟩

/-- `Nat → Sort u`, the type of the motive of `Nat.rec` -/
abbrev natMotiveTy : CoCTerm := .«∀» .«u+1» tyNat (CoCSort.toCoCTerm .u)

/-- `motive x`, where the bound variable `k` is the motive `motive : Nat → Sort u` -/
abbrev natMotiveApp (k : Nat) (x : CoCTerm) : CoCTerm :=
  .a .«u+1» tyNat (CoCSort.toCoCTerm .u) (.b k) x

/-- `x + 1`, which is definitionally `Nat.succ x` -/
abbrev natSucc (x : CoCTerm) : CoCTerm :=
  .a .«1» tyNat tyNat (.a .«1» tyNat (.«∀» .«1» tyNat tyNat) (.t (.ncst .nadd)) x)
    (.t (.ncst (.natVal 1)))

/-- `∀ n : Nat, motive n → motive (n + 1)`, under the binders `motive` and `motive 0` -/
abbrev natRecStepTy : CoCTerm :=
  .«∀» .u tyNat (.«∀» .u (natMotiveApp 2 (.b 0)) (natMotiveApp 3 (natSucc (.b 1))))

/--
  The type of `@Nat.rec`, which is a type at `Sort (imax (u+1) u)`:
  `∀ motive : Nat → Sort u, motive 0 → (∀ n : Nat, motive n → motive (n + 1)) →
    ∀ t : Nat, motive t`.
  The embedding has no `Nat.succ`, so `n.succ` is written `n + 1`, which is
  definitionally equal to it
-/
example : HasType []
    (.«∀» .u natMotiveTy (.«∀» .u (natMotiveApp 0 (.t (.ncst (.natVal 0))))
      (.«∀» .u natRecStepTy (.«∀» .u tyNat (natMotiveApp 3 (.b 0))))))
    (CoCSort.toCoCTerm .«imax (u+1) u») :=
  -- `motive : Nat → Sort u`
  .pi' (.pi' (.base .nil rfl) rfl fun wf => .base wf rfl) rfl fun wf =>
  -- `motive 0`
  .pi' (.app (.var' wf rfl) (.base wf rfl)) rfl fun wf =>
  -- `∀ n : Nat, motive n → motive (n + 1)`
  .pi' (.pi' (.base wf rfl) rfl fun wf =>
      .pi' (.app (.var' wf rfl) (.var' wf rfl)) rfl fun wf =>
      .app (.var' wf rfl) (.app (.app (.base wf rfl) (.var' wf rfl)) (.base wf rfl))) rfl fun wf =>
  -- `∀ t : Nat, motive t`
  .pi' (.base wf rfl) rfl fun wf => .app (.var' wf rfl) (.var' wf rfl)

end Examples

end Auto.Embedding.CoC
