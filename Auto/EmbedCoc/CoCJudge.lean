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

-- Regression checks: small derivations

/-- The polymorphic identity `λ α : Type, λ x : α, x : ∀ α : Type, α → α` -/
example : HasType []
    (.«λ» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1)) (.«λ» .«1» (.b 0) (.b 1) (.b 0)))
    (.«∀» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1))) :=
  have hTy : HasType [] (CoCSort.toCoCTerm .«1») (CoCSort.toCoCTerm .«2») := .base .nil rfl
  have hα : HasType [CoCSort.toCoCTerm .«1»] (.b 0) (CoCSort.toCoCTerm .«1») :=
    .var (A := CoCSort.toCoCTerm .«1») (.cons hTy) rfl
  have wf : WfCtx [.b 0, CoCSort.toCoCTerm .«1»] := .cons hα
  have hPi : HasType [CoCSort.toCoCTerm .«1»] (.«∀» .«1» (.b 0) (.b 1)) (CoCSort.toCoCTerm .«1») :=
    .pi hα (.var (A := CoCSort.toCoCTerm .«1») wf rfl) rfl
  .lam (.pi hTy hPi rfl) (.lam hPi (.var (A := .b 0) wf rfl))

/-- The type-level function `λ x : Nat, Nat`, of type `∀ x : Nat, Sort 1` -/
abbrev constNat : CoCTerm := .«λ» .«2» tyNat (CoCSort.toCoCTerm .«1») tyNat

/-- `3 : (λ x : Nat, Nat) 3`, by `β`-conversion -/
example : HasType [] (.t (.ncst (.natVal 3)))
    (.a .«2» tyNat (CoCSort.toCoCTerm .«1») constNat (.t (.ncst (.natVal 3)))) :=
  have hNat : HasType [] tyNat (CoCSort.toCoCTerm .«1») := .base .nil rfl
  have h3 : HasType [] (.t (.ncst (.natVal 3))) tyNat := .base .nil rfl
  have hBody : HasType [tyNat] tyNat (CoCSort.toCoCTerm .«1») := .base (.cons hNat) rfl
  have hSort : HasType [tyNat] (CoCSort.toCoCTerm .«1») (CoCSort.toCoCTerm .«2») :=
    .base (.cons hNat) rfl
  have hPi : HasType [] (.«∀» .«2» tyNat (CoCSort.toCoCTerm .«1»)) (CoCSort.toCoCTerm .«2») :=
    .pi hNat hSort rfl
  have hApp : HasType [] (.a .«2» tyNat (CoCSort.toCoCTerm .«1») constNat (.t (.ncst (.natVal 3))))
      (CoCSort.toCoCTerm .«1») := .app (.lam hPi hBody) h3
  .conv h3 hApp ⟨tyNat, .refl _,
    .single (.beta .«2» tyNat (CoCSort.toCoCTerm .«1») tyNat (.t (.ncst (.natVal 3))))⟩

end Auto.Embedding.CoC
