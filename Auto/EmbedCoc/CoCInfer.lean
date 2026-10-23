module

public import Auto.EmbedCoc.CoCJudge

@[expose] public section

/-!
  A type checker for the embedded system, sound with respect to the judgement. Terms
  carry their annotations, so a type is inferred by structural recursion on the term.
  Conversion is checked by comparing normal forms, computed with a bound `fuel` on
  the number of nested contractions, so that the checker terminates even on terms
  without a normal form. The checker is meant to be run by the kernel
-/

namespace Auto.Embedding.CoC

/-! ## Normalization -/

theorem CoCTerm.Red.congr {F : CoCTerm → CoCTerm} (hF : ∀ {t t'}, Red1 t t' → Red1 (F t) (F t'))
    {t t' : CoCTerm} (h : Red t t') : Red (F t) (F t') := by
  induction h with
  | refl => exact .refl _
  | step h₁ _ ih => exact .step (hF h₁) ih

theorem CoCTerm.Red.app_congr {s' : CoCSort} {A A' B B' f f' a a' : CoCTerm} (hA : Red A A')
    (hB : Red B B') (hf : Red f f') (ha : Red a a') : Red (.a s' A B f a) (.a s' A' B' f' a') :=
  (Red.congr (F := (.a s' · B f a)) .aArgTy hA).trans <|
  (Red.congr (F := (.a s' A' · f a)) .aResTy hB).trans <|
  (Red.congr (F := (.a s' A' B' · a)) .aFn hf).trans <|
  Red.congr (F := (.a s' A' B' f' ·)) .aArg ha

theorem CoCTerm.Red.lam_congr {s' : CoCSort} {A A' B B' b b' : CoCTerm} (hA : Red A A')
    (hB : Red B B') (hb : Red b b') : Red (.«λ» s' A B b) (.«λ» s' A' B' b') :=
  (Red.congr (F := (.«λ» s' · B b)) .lamArgTy hA).trans <|
  (Red.congr (F := (.«λ» s' A' · b)) .lamResTy hB).trans <|
  Red.congr (F := (.«λ» s' A' B' ·)) .lamBody hb

theorem CoCTerm.Red.forall_congr {s' : CoCSort} {A A' B B' : CoCTerm} (hA : Red A A')
    (hB : Red B B') : Red (.«∀» s' A B) (.«∀» s' A' B') :=
  (Red.congr (F := (.«∀» s' · B)) .forallArgTy hA).trans <|
  Red.congr (F := (.«∀» s' A' ·)) .forallBodyTy hB

/--
  `f a`, annotated with `∀_{s'} x : A, B`, where a redex at the root is contracted and
  the contractum passed to `k`. As in `CoCTerm.Red1.beta`, a redex is contracted only
  when the annotations of the application agree with those of the abstraction
-/
def CoCTerm.normApp (k : CoCTerm → CoCTerm) (s' : CoCSort) (A B f a : CoCTerm) : CoCTerm :=
  match f with
  | .«λ» s₂ A₂ B₂ body =>
    if s₂ = s' ∧ A₂ = A ∧ B₂ = B then k (CoCTerm.instantiate1 a body) else .a s' A B f a
  | _ => .a s' A B f a

/-- One pass of normalization: the subterms are normalized, and each contractum is passed to `k` -/
def CoCTerm.normWith (k : CoCTerm → CoCTerm) : CoCTerm → CoCTerm
  | .b n                     => .b n
  | .t bt                    => .t bt
  | .a s' argTy resTy fn arg =>
    normApp k s' (argTy.normWith k) (resTy.normWith k) (fn.normWith k) (arg.normWith k)
  | .«λ» s' argTy resTy body =>
    .«λ» s' (argTy.normWith k) (resTy.normWith k) (body.normWith k)
  | .«∀» s' argTy bodyTy     => .«∀» s' (argTy.normWith k) (bodyTy.normWith k)

/--
  The normal form of `T`, when it is reached within `fuel` nested contractions: each
  contractum is normalized with one less
-/
def CoCTerm.norm : Nat → CoCTerm → CoCTerm
  | 0,        T => T
  | fuel + 1, T => T.normWith (norm fuel)

theorem CoCTerm.normApp_red {k : CoCTerm → CoCTerm} (hk : ∀ t, Red t (k t)) (s' : CoCSort)
    (A B f a : CoCTerm) : Red (.a s' A B f a) (normApp k s' A B f a) := by
  unfold normApp
  split
  · split
    · next h =>
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .step (.beta _ _ _ _ _) (hk _)
    · exact .refl _
  · exact .refl _

theorem CoCTerm.normWith_red {k : CoCTerm → CoCTerm} (hk : ∀ t, Red t (k t)) (t : CoCTerm) :
    Red t (t.normWith k) := by
  induction t with
  | b n => exact .refl _
  | t bt => exact .refl _
  | a s' A B f a ihA ihB ihf iha =>
    exact (Red.app_congr ihA ihB ihf iha).trans (normApp_red hk _ _ _ _ _)
  | «λ» s' A B b ihA ihB ihb => exact Red.lam_congr ihA ihB ihb
  | «∀» s' A B ihA ihB => exact Red.forall_congr ihA ihB

theorem CoCTerm.norm_red : (fuel : Nat) → (T : CoCTerm) → Red T (T.norm fuel)
  | 0,        T => .refl T
  | fuel + 1, T => normWith_red (norm_red fuel) T

/-- Whether `A` and `B` are convertible: equal, or with the same normal form within `fuel` -/
def CoCTerm.conv (fuel : Nat) (A B : CoCTerm) : Bool :=
  decide (A = B) || decide (A.norm fuel = B.norm fuel)

theorem CoCTerm.conv_sound {fuel : Nat} {A B : CoCTerm} (h : A.conv fuel B = true) :
    A.Joinable B := by
  simp only [conv, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | h
  · exact .refl A
  · exact ⟨_, norm_red fuel A, h ▸ norm_red fuel B⟩

/-! ## Type inference -/

/--
  `T` as a sort: `T` itself when it is one, or else its normal form, as long as that
  sort has a type, so that `Judge.conv` can convert `T` to it
-/
def CoCTerm.asSort? (fuel : Nat) (T : CoCTerm) : Option CoCSort :=
  match T with
  | .t (.sort s) => some s
  | _ =>
    match T.norm fuel with
    | .t (.sort s) => if s.succ.isSome then some s else none
    | _            => none

theorem CoCTerm.asSort?_sound {fuel : Nat} {Γ : List CoCTerm} {t T : CoCTerm} {s : CoCSort}
    (hs : T.asSort? fuel = some s) (h : HasType Γ t T) : HasType Γ t s.toCoCTerm := by
  unfold asSort? at hs
  split at hs
  · cases hs; exact h
  · split at hs
    · next hn =>
      split at hs
      · next hsucc =>
        cases hs
        obtain ⟨s₁, hs₁⟩ := Option.isSome_iff_exists.mp hsucc
        exact .conv (s := s₁) h (.base h.wfCtx (by rw [CoCBaseTerm.check, hs₁]; rfl))
          ⟨.t (.sort s), hn ▸ norm_red fuel T, .refl _⟩
      · cases hs
    · cases hs

/--
  The sort of `∀_{s'} x : A, B`, given the types `TA` and `TB` inferred for `A` and
  `B`: the join of their sorts, when the sort of `B` is the annotated one
-/
def piSort? (fuel : Nat) (s' : CoCSort) (TA TB : Option CoCTerm) : Option CoCSort :=
  (TA.bind (CoCTerm.asSort? fuel)).bind fun s =>
  (TB.bind (CoCTerm.asSort? fuel)).bind fun s₂ =>
  if s₂ = s' then s.join s' else none

theorem piSort?_sound {fuel : Nat} {Γ : List CoCTerm} {A B : CoCTerm} {s' r : CoCSort}
    {TA TB : Option CoCTerm} (hTA : ∀ {T}, TA = some T → HasType Γ A T)
    (hTB : WfCtx (A :: Γ) → ∀ {T}, TB = some T → HasType (A :: Γ) B T)
    (h : piSort? fuel s' TA TB = some r) :
    ∃ s : CoCSort, HasType Γ A s.toCoCTerm ∧ HasType (A :: Γ) B s'.toCoCTerm ∧
      s.join s' = some r := by
  simp only [piSort?, Option.bind_eq_some_iff] at h
  obtain ⟨s, ⟨T, hT, hs⟩, s₂, ⟨T', hT', hs₂⟩, hj⟩ := h
  split at hj
  · next e =>
    subst e
    have hA := CoCTerm.asSort?_sound hs (hTA hT)
    exact ⟨s, hA, CoCTerm.asSort?_sound hs₂ (hTB (.cons hA) hT'), hj⟩
  · cases hj

/--
  The type of `t` in the context `Γ`, or `none` when the checker finds none. `fuel`
  bounds the normalization in conversions, see `CoCTerm.conv`
-/
def infer (fuel : Nat) : List CoCTerm → CoCTerm → Option CoCTerm
  | Γ, .b n => Γ[n]?.map (·.bvarLifts (n + 1))
  | _, .t bt => bt.check
  | Γ, .a s' A B f a =>
    (piSort? fuel s' (infer fuel Γ A) (infer fuel (A :: Γ) B)).bind fun _ =>
    (infer fuel Γ f).bind fun Tf => (infer fuel Γ a).bind fun Ta =>
    if Tf.conv fuel (.«∀» s' A B) && Ta.conv fuel A then some (CoCTerm.instantiate1 a B) else none
  | Γ, .«λ» s' A B b =>
    (piSort? fuel s' (infer fuel Γ A) (infer fuel (A :: Γ) B)).bind fun _ =>
    (infer fuel (A :: Γ) b).bind fun Tb =>
    if Tb.conv fuel B then some (.«∀» s' A B) else none
  | Γ, .«∀» s' A B =>
    (piSort? fuel s' (infer fuel Γ A) (infer fuel (A :: Γ) B)).map CoCSort.toCoCTerm

/-- Soundness of the checker: the type it infers is a type of the term -/
theorem infer_sound {fuel : Nat} {Γ : List CoCTerm} {t T : CoCTerm} (hΓ : WfCtx Γ)
    (h : infer fuel Γ t = some T) : HasType Γ t T := by
  induction t generalizing Γ T with
  | b n =>
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .var hΓ hA
  | t bt => exact .base hΓ h
  | a s' A B f a ihA ihB ihf iha =>
    simp only [infer, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, Tf, hTf, Ta, hTa, hc⟩ := h
    obtain ⟨s, hA, hB, hj⟩ := piSort?_sound (ihA hΓ) (fun hΓ' => ihB hΓ') hr
    split at hc
    · next hconv =>
      cases hc
      rw [Bool.and_eq_true] at hconv
      exact .app (.conv (ihf hΓ hTf) (.pi hA hB hj) (CoCTerm.conv_sound hconv.1))
        (.conv (iha hΓ hTa) hA (CoCTerm.conv_sound hconv.2))
    · cases hc
  | «λ» s' A B b ihA ihB ihb =>
    simp only [infer, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, Tb, hTb, hc⟩ := h
    obtain ⟨s, hA, hB, hj⟩ := piSort?_sound (ihA hΓ) (fun hΓ' => ihB hΓ') hr
    split at hc
    · next hconv =>
      cases hc
      exact .lam (.pi hA hB hj) (.conv (ihb (.cons hA) hTb) hB (CoCTerm.conv_sound hconv))
    · cases hc
  | «∀» s' A B ihA ihB =>
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨s, hA, hB, hj⟩ := piSort?_sound (ihA hΓ) (fun hΓ' => ihB hΓ') hr
    exact .pi hA hB hj

/-- Whether each entry of `Γ` is a type in the context of the entries after it -/
def checkCtx (fuel : Nat) : List CoCTerm → Bool
  | []     => true
  | A :: Γ => checkCtx fuel Γ && ((infer fuel Γ A).bind (CoCTerm.asSort? fuel)).isSome

theorem checkCtx_sound {fuel : Nat} : {Γ : List CoCTerm} → checkCtx fuel Γ = true → WfCtx Γ
  | [],     _ => .nil
  | _ :: _, h => by
    simp only [checkCtx, Bool.and_eq_true, Option.isSome_iff_exists, Option.bind_eq_some_iff] at h
    obtain ⟨hΓ, s, T, hT, hs⟩ := h
    exact .cons (CoCTerm.asSort?_sound hs (infer_sound (checkCtx_sound hΓ) hT))

-- Regression checks: the derivations of `CoCJudge`, found by the checker

/-- The polymorphic identity `λ α : Type, λ x : α, x : ∀ α : Type, α → α` -/
example : infer 0 []
    (.«λ» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1))
      (.«λ» .«1» (.b 0) (.b 1) (.b 0))) =
    some (.«∀» .«1» (CoCSort.toCoCTerm .«1») (.«∀» .«1» (.b 0) (.b 1))) := rfl

/--
  `(λ y : R, y) 3 : R`, where `R` is the redex `(λ x : Nat, Nat) 3`. Checking the
  argument converts its type `Nat` to `R`, which takes one contraction
-/
example (R : CoCTerm)
    (hR : R = .a .«2» tyNat (CoCSort.toCoCTerm .«1») constNat (.t (.ncst (.natVal 3)))) :
    infer 1 [] (.a .«1» R R (.«λ» .«1» R R (.b 0)) (.t (.ncst (.natVal 3)))) = some R := by
  subst hR; rfl

/-- Without fuel, the conversion fails -/
example (R : CoCTerm)
    (hR : R = .a .«2» tyNat (CoCSort.toCoCTerm .«1») constNat (.t (.ncst (.natVal 3)))) :
    infer 0 [] (.a .«1» R R (.«λ» .«1» R R (.b 0)) (.t (.ncst (.natVal 3)))) = none := by
  subst hR; rfl

end Auto.Embedding.CoC
