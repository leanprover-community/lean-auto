module

public import Auto.EmbedLam.LamConv

@[expose] public section

namespace Auto.Embedding.Lam

structure IndInfo where
  type  : LamSort
  ctors : List (LamSort × LamTerm)
  projs : Option (List (LamSort × LamTerm))

def IndInfo.toString (i : IndInfo) :=
  s!"IndInfo ⦗⦗ {i.type} || " ++
    String.intercalate ", " (i.ctors.map (fun (s, t) => s!"{t} : {s}")) ++
    (match i.projs with
     | .some arr => " || " ++ String.intercalate ", " (arr.map (fun (s, t) => s!"{t} : {s}"))
     | .none => "") ++ " ⦘⦘"

instance : ToString IndInfo where
  toString := IndInfo.toString

def IndInfo.mpAll?Aux (rw : LamTerm) : List (LamSort × LamTerm) → Option (List (LamSort × LamTerm))
| [] => .some []
| .cons (s, t) tail =>
  match LamTerm.mpAll? rw t, mpAll?Aux rw tail with
  | .some t', .some tail' => .some (.cons (s, t') tail')
  | _,        _           => .none

def IndInfo.mpAll? (rw : LamTerm) (ii : IndInfo) : Option IndInfo :=
  match mpAll?Aux rw ii.ctors with
  | .some ii' => .some ⟨ii.type, ii', ii.projs.bind (mpAll?Aux rw)⟩
  | .none     => .none

abbrev MutualIndInfo := List IndInfo

def MutualIndInfo.mpAll? (rw : LamTerm) : MutualIndInfo → Option MutualIndInfo
| [] => .some []
| .cons ii tail =>
  match ii.mpAll? rw, mpAll? rw tail with
  | .some ii', .some tail' => .some (.cons ii' tail')
  | _,         _           => .none

/-!
  Characterization of mutual inductive types. A constructor `c : A₁ → ⋯ → Aₙ → T` applied
    to the variables bound by `∀ x₁ ⋯ xₙ` is `(c.bvarLifts n).bvarAppsRev [A₁, ⋯, Aₙ]`
-/

/-- `∀ x₁ ⋯ xₙ y₁ ⋯ yₘ, ¬ (c₁ x₁ ⋯ xₙ = c₂ y₁ ⋯ yₘ)`, where `c₁ c₂` are constructors of `ty` -/
def IndInfo.distinctTerm (ty : LamSort) (c₁ c₂ : LamSort × LamTerm) : LamTerm :=
  let (s₁, t₁) := c₁
  let (s₂, t₂) := c₂
  let as₁ := s₁.getArgTys
  let as₂ := s₂.getArgTys
  let n := as₁.length + as₂.length
  LamTerm.mkForallEFN (.mkNot (.mkEq ty
    (((t₁.bvarLifts as₁.length).bvarAppsRev as₁).bvarLifts as₂.length) ((t₂.bvarLifts n).bvarAppsRev as₂)))
    (as₁ ++ as₂)

/-- Different constructors of `ii.type` produce different values -/
def IndInfo.distinctTerms (ii : IndInfo) : List LamTerm := go ii.ctors
where
  go : List (LamSort × LamTerm) → List LamTerm
  | [] => []
  | c :: cs => cs.map (distinctTerm ii.type c) ++ go cs

/--
  `∀ x₁ ⋯ xₙ y₁ ⋯ yₙ, c x₁ ⋯ xₙ = c y₁ ⋯ yₙ → x₁ = y₁ ∧ ⋯ ∧ xₙ = yₙ`,
    where `c` is a constructor of `ty` with `n ≥ 1` arguments
-/
def IndInfo.injectTerm? (ty : LamSort) (c : LamSort × LamTerm) : Option LamTerm :=
  let (s, t) := c
  let as := s.getArgTys
  let n := as.length
  if n == 0 then
    .none
  else
    let eqs := as.zipIdx.map fun (a, i) => LamTerm.mkEq a (.bvar (2 * n - 1 - i)) (.bvar (n - 1 - i))
    let cx := ((t.bvarLifts n).bvarAppsRev as).bvarLifts n
    let cy := (t.bvarLifts (2 * n)).bvarAppsRev as
    .some (LamTerm.mkForallEFN (.mkImp (.mkEq ty cx cy) (.mkAndN eqs)) (as ++ as))

/-- The constructors of `ii.type` are injective -/
def IndInfo.injectTerms (ii : IndInfo) : List LamTerm := ii.ctors.filterMap (injectTerm? ii.type)

/-- If `ii.type` is a structure, `∀ x₁ ⋯ xₙ, projᵢ (mk x₁ ⋯ xₙ) = xᵢ` for each projection `projᵢ` -/
def IndInfo.projTerms (ii : IndInfo) : List LamTerm :=
  match ii.ctors, ii.projs with
  | [(s, c)], .some projs =>
    let as := s.getArgTys
    let n := as.length
    if projs.length != n then
      []
    else
      let c := (c.bvarLifts n).bvarAppsRev as
      (projs.zip as).zipIdx.map fun (((_, proj), a), i) =>
        LamTerm.mkForallEFN (.mkEq a (.app ii.type (proj.bvarLifts n) c) (.bvar (n - 1 - i))) as
  | _, _ => []

/--
  The characterization of the inductive type `ii` that does not depend on the other types of
    its mutual block: distinctness and injectivity of the constructors, and the projections
-/
def IndInfo.specTerms (ii : IndInfo) : List LamTerm := ii.distinctTerms ++ ii.injectTerms ++ ii.projTerms

/--
  If `a` is `B₁ → ⋯ → Bₘ → Tₗ`, where `Tₗ` is the `l`-th type of `mind` and `B₁ ⋯ Bₘ`
    do not mention the types of `mind`, return `l`. These are the sorts of the arguments
    of constructors that have induction hypotheses
-/
def MutualIndInfo.recArg? (mind : MutualIndInfo) (a : LamSort) : Option Nat :=
  let tys := mind.map (·.type)
  if a.getArgTys.any fun b => tys.any b.contains then
    .none
  else
    tys.findIdx? (· == a.getResTy)

/-- `Pⱼ₊₁` under `off` binders, inside the binders `P₁ ⋯ Pₖ` of `MutualIndInfo.inductionTerm` -/
abbrev MutualIndInfo.motive (mind : MutualIndInfo) (j off : Nat) : LamTerm := .bvar (off + mind.length - 1 - j)

/--
  The induction hypothesis `∀ b₁ ⋯ bₘ, Pₗ₊₁ (xᵢ₊₁ b₁ ⋯ bₘ)` for the argument `xᵢ₊₁ : a` of a
    constructor with `n` arguments, if `a` is `B₁ → ⋯ → Bₘ → Tₗ₊₁` (see `MutualIndInfo.recArg?`)
-/
def MutualIndInfo.indHypTerm? (mind : MutualIndInfo) (n : Nat) (a : LamSort) (i : Nat) : Option LamTerm :=
  let bs := a.getArgTys
  let m := bs.length
  (mind.recArg? a).map fun l => LamTerm.mkForallEFN
    (.app a.getResTy (mind.motive l (n + m)) ((LamTerm.bvar (m + n - 1 - i)).bvarAppsRev bs)) bs

/--
  `∀ x₁ ⋯ xₙ, IH₁ → ⋯ → IHᵣ → Pⱼ₊₁ (c x₁ ⋯ xₙ)` for the constructor `c : s` of the
    `j`-th type `ty` of `mind`, where `IH₁ ⋯ IHᵣ` are given by `MutualIndInfo.indHypTerm?`
-/
def MutualIndInfo.ctorHypTerm (mind : MutualIndInfo) (ty : LamSort) (j : Nat) (s : LamSort) (c : LamTerm) : LamTerm :=
  let as := s.getArgTys
  let n := as.length
  let ihs := as.zipIdx.filterMap fun (a, i) => mind.indHypTerm? n a i
  LamTerm.mkForallEFN (.mkImpN ihs (.app ty (mind.motive j n) ((c.bvarLifts (mind.length + n)).bvarAppsRev as))) as

/-- The sorts of the motives `P₁ ⋯ Pₖ` of `MutualIndInfo.inductionTerm` -/
abbrev MutualIndInfo.motiveTys (mind : MutualIndInfo) : List LamSort :=
  mind.map fun ii => .func ii.type (.base .prop)

/--
  Induction over the mutual inductive types `T₁ ⋯ Tₖ` of `mind`:
    `∀ (P₁ : T₁ → Prop) ⋯ (Pₖ : Tₖ → Prop), H₁ → ⋯ → Hₘ → (∀ t, P₁ t) ∧ ⋯ ∧ (∀ t, Pₖ t)`,
  with one hypothesis `∀ x₁ ⋯ xₙ, IH₁ → ⋯ → IHᵣ → Pⱼ (c x₁ ⋯ xₙ)` for each constructor
    `c : A₁ → ⋯ → Aₙ → Tⱼ`. The induction hypotheses are `∀ b₁ ⋯ bₘ, Pₗ (xᵢ b₁ ⋯ bₘ)`
    for the arguments `xᵢ : B₁ → ⋯ → Bₘ → Tₗ` such that `B₁ ⋯ Bₘ` do not mention the
    types of `mind` (which is `Pₗ xᵢ` if `m = 0`), as in `IndSig.induction`
-/
def MutualIndInfo.inductionTerm (mind : MutualIndInfo) : LamTerm :=
  let hyps := mind.zipIdx.flatMap fun (ii, j) => ii.ctors.map fun (s, c) => mind.ctorHypTerm ii.type j s c
  let concl := LamTerm.mkAndN (mind.zipIdx.map fun (ii, j) =>
    .mkForallEF ii.type (.app ii.type (mind.motive j 1) (.bvar 0)))
  LamTerm.mkForallEFN (.mkImpN hyps concl) mind.motiveTys

/--
  The characterization of the mutual inductive types `mind` (see `MutualIndInfo.Spec`):
    the characterizations of the types of `mind` (see `IndInfo.specTerms`), and induction
-/
def MutualIndInfo.specTerms (mind : MutualIndInfo) : List LamTerm :=
  mind.flatMap IndInfo.specTerms ++ [mind.inductionTerm]

/--
  `lval` interprets `mind` as mutual inductive types:
  · Different constructors of the same type produce different values
  · The constructors are injective
  · The projections of structures project the arguments of the constructors
  · Induction over the types of `mind`
  For simple mutual inductive types, these characterize the types of `mind` up to isomorphism,
    given the interpretations of the other sorts of the arguments of the constructors
    (see `MutualIndInfo.isomType_of_spec`).
  Arguments whose sorts mention the types of `mind` only in other sorts (e.g. `List T`, if
    `List T` is not a type of `mind`) have no induction hypotheses, so the characterization
    is weaker but still holds for such types
-/
def MutualIndInfo.Spec (lval : LamValuation) (mind : MutualIndInfo) : Prop :=
  ∀ t ∈ mind.specTerms, LamThmValid lval [] t

/--
  `MutualIndInfo.Spec` is the characterizations of the types of `mind`, which do not depend on
    the other types of `mind`, together with induction
-/
theorem MutualIndInfo.spec_iff {lval : LamValuation} {mind : MutualIndInfo} :
  mind.Spec lval ↔ (∀ ii ∈ mind, ∀ t ∈ ii.specTerms, LamThmValid lval [] t) ∧
    LamThmValid lval [] mind.inductionTerm := by
  constructor
  · intro h
    exact ⟨fun ii hii t ht => h t (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ii, hii, ht⟩)),
      h _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · intro ⟨hty, hind⟩ t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨ii, hii, ht⟩ := List.mem_flatMap.mp ht
      exact hty ii hii t ht
    · rw [List.mem_singleton.mp ht]; exact hind

/-!
  Proof that `MutualIndInfo.SemSpec`, a statement in Lean about the interpretations of the
    constructors and projections, is equivalent to `MutualIndInfo.Spec`
-/

/-- The sorts of the arguments of the `c`-th constructor of `ii` -/
abbrev IndInfo.argTys (ii : IndInfo) (c : Fin ii.ctors.length) : List LamSort := ii.ctors[c].1.getArgTys

/-- Well-formedness of the `c`-th constructor of `ii`, as a function of its arguments -/
abbrev IndInfo.CtorWF (ltv : LamTyVal) (lctx : Nat → LamSort) (ii : IndInfo) (c : Fin ii.ctors.length) :=
  LamWF ltv ⟨lctx, ii.ctors[c].2, .mkFuncs ii.type (ii.argTys c)⟩

/--
  The meaning of `MutualIndInfo.Spec`, with the constructors of `mind` interpreted as
    functions on tuples of arguments
-/
structure MutualIndInfo.SemSpec (lval : LamValuation.{u}) (mind : MutualIndInfo) : Prop where
  /-- The constructors are well-formed -/
  wfCtor : ∀ lctx (j : Fin mind.length) (c : Fin mind[j].ctors.length),
    Nonempty (mind[j].CtorWF lval.toLamTyVal lctx c)
  /-- The projections of structures are well-formed -/
  wfProj : ∀ lctx (j : Fin mind.length) s c ps, mind[j].ctors = [(s, c)] → mind[j].projs = .some ps →
    ∀ (hlen : ps.length = s.getArgTys.length) (i : Fin ps.length),
    Nonempty (LamWF lval.toLamTyVal ⟨lctx, ps[i].2, .func mind[j].type (s.getArgTys[i.val]'(hlen ▸ i.isLt))⟩)
  /-- Different constructors of the same type produce different values -/
  distinct : ∀ lctx lctxTerm (j : Fin mind.length) (c₁ c₂ : Fin mind[j].ctors.length), c₁ ≠ c₂ →
    ∀ (wf₁ : mind[j].CtorWF lval.toLamTyVal lctx c₁) (wf₂ : mind[j].CtorWF lval.toLamTyVal lctx c₂) xs ys,
      LamSort.uncurry (wf₁.interp lval lctx lctxTerm) xs ≠ LamSort.uncurry (wf₂.interp lval lctx lctxTerm) ys
  /-- The constructors are injective -/
  inject : ∀ lctx lctxTerm (j : Fin mind.length) (c : Fin mind[j].ctors.length)
    (wf : mind[j].CtorWF lval.toLamTyVal lctx c) xs ys,
      LamSort.uncurry (wf.interp lval lctx lctxTerm) xs = LamSort.uncurry (wf.interp lval lctx lctxTerm) ys → xs = ys
  /-- The projections of structures project the arguments of the constructors -/
  proj : ∀ lctx lctxTerm (j : Fin mind.length) s c ps, mind[j].ctors = [(s, c)] → mind[j].projs = .some ps →
    ∀ (hlen : ps.length = s.getArgTys.length) (i : Fin ps.length)
      (wfp : LamWF lval.toLamTyVal ⟨lctx, ps[i].2, .func mind[j].type (s.getArgTys[i.val]'(hlen ▸ i.isLt))⟩)
      (wfc : LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs mind[j].type s.getArgTys⟩) xs,
      wfp.interp lval lctx lctxTerm (LamSort.uncurry (wfc.interp lval lctx lctxTerm) xs) = xs.get ⟨i, hlen ▸ i.isLt⟩
  /--
    Induction over the types of `mind`. The induction hypothesis `∀ ys, P l (xs.get i ys)`
      of the `i`-th argument is stated for every `f` that is `HEq` to `xs.get i`, which
      avoids casting `xs.get i` to the sort `B₁ → ⋯ → Bₘ → Tₗ` (see `MutualIndInfo.recArg?`)
  -/
  induction : ∀ lctx lctxTerm (P : (j : Fin mind.length) → mind[j].type.interp lval.tyVal → Prop),
    (∀ (j : Fin mind.length) (c : Fin mind[j].ctors.length) (wf : mind[j].CtorWF lval.toLamTyVal lctx c)
      (xs : HList (LamSort.interp lval.tyVal) (mind[j].argTys c)),
      (∀ (i : Fin (mind[j].argTys c).length) (l : Fin mind.length), mind.recArg? (mind[j].argTys c)[i] = .some l →
        ∀ (f : (LamSort.mkFuncs mind[l].type (mind[j].argTys c)[i].getArgTys).interp lval.tyVal),
          HEq f (xs.get i) → ∀ ys, P l (LamSort.uncurry f ys)) →
      P j (LamSort.uncurry (wf.interp lval lctx lctxTerm) xs)) →
    ∀ j x, P j x

theorem IndInfo.distinctTerm_eq :
  IndInfo.distinctTerm ty (s₁, t₁) (s₂, t₂) = LamTerm.mkForallEFN (LamTerm.mkForallEFN (.mkNot (.mkEq ty
    (((t₁.bvarLifts s₁.getArgTys.length).bvarAppsRev s₁.getArgTys).bvarLifts s₂.getArgTys.length)
    (((t₂.bvarLifts s₁.getArgTys.length).bvarLifts s₂.getArgTys.length).bvarAppsRev s₂.getArgTys)))
    s₂.getArgTys) s₁.getArgTys := by
  dsimp only [distinctTerm]
  rw [LamTerm.mkForallEFN_append, Nat.add_comm, LamTerm.bvarLifts, LamTerm.bvarLifts_add]

/-- `IndInfo.distinctTerm ty c₁ c₂` is valid iff `c₁` and `c₂` produce different values -/
theorem IndInfo.distinctTerm_valid {lval : LamValuation.{u}} {ty : LamSort} {c₁ c₂ : LamSort × LamTerm}
  (hwf₁ : ∀ lctx, Nonempty (LamWF lval.toLamTyVal ⟨lctx, c₁.2, .mkFuncs ty c₁.1.getArgTys⟩))
  (hwf₂ : ∀ lctx, Nonempty (LamWF lval.toLamTyVal ⟨lctx, c₂.2, .mkFuncs ty c₂.1.getArgTys⟩)) :
  LamThmValid lval [] (IndInfo.distinctTerm ty c₁ c₂) ↔ ∀ lctx lctxTerm
    (wf₁ : LamWF lval.toLamTyVal ⟨lctx, c₁.2, .mkFuncs ty c₁.1.getArgTys⟩)
    (wf₂ : LamWF lval.toLamTyVal ⟨lctx, c₂.2, .mkFuncs ty c₂.1.getArgTys⟩) xs ys,
    LamSort.uncurry (wf₁.interp lval lctx lctxTerm) xs ≠ LamSort.uncurry (wf₂.interp lval lctx lctxTerm) ys := by
  obtain ⟨s₁, t₁⟩ := c₁; obtain ⟨s₂, t₂⟩ := c₂
  dsimp only at hwf₁ hwf₂ ⊢
  have key : ∀ lctx (wf₁ : LamWF lval.toLamTyVal ⟨lctx, t₁, .mkFuncs ty s₁.getArgTys⟩)
    (wf₂ : LamWF lval.toLamTyVal ⟨lctx, t₂, .mkFuncs ty s₂.getArgTys⟩),
    LamValid lval lctx (IndInfo.distinctTerm ty (s₁, t₁) (s₂, t₂)) ↔ ∀ lctxTerm xs ys,
      LamSort.uncurry (wf₁.interp lval lctx lctxTerm) xs ≠ LamSort.uncurry (wf₂.interp lval lctx lctxTerm) ys := by
    intro lctx wf₁ wf₂
    let wfX := LamWF.bvarLifts (xs := s₂.getArgTys.reverse) List.length_reverse _
      (LamWF.bvarAppsRev (LamWF.bvarLifts (xs := s₁.getArgTys.reverse) List.length_reverse _ wf₁))
    let wfY := LamWF.bvarAppsRev (LamWF.bvarLifts (xs := s₂.getArgTys.reverse) List.length_reverse _
      (LamWF.bvarLifts (xs := s₁.getArgTys.reverse) List.length_reverse _ wf₂))
    rw [distinctTerm_eq, LamValid.iff_of_wf (LamWF.mkForallEFN (LamWF.mkForallEFN (.mkNot (.mkEq wfX wfY))))]
    apply forall_congr'; intro lctxTerm
    rw [LamWF.interp_eqForallEFN_reverse]; apply forall_congr'; intro xs
    rw [LamWF.interp_eqForallEFN_reverse]; apply forall_congr'; intro ys
    rw [LamWF.interp_eqNot, LamWF.interp_eqEq]
    rw [← LamWF.interp_bvarLifts, LamWF.interp_bvarLifts_bvarAppsRev wf₁]
    rw [LamWF.interp_bvarLifts_bvarAppsRev (LamWF.bvarLifts List.length_reverse _ wf₂), ← LamWF.interp_bvarLifts]
  refine ⟨fun hv lctx lctxTerm wf₁ wf₂ => (key lctx wf₁ wf₂).mp (hv lctx) lctxTerm, fun hsem lctx => ?_⟩
  obtain ⟨wf₁⟩ := hwf₁ lctx; obtain ⟨wf₂⟩ := hwf₂ lctx
  exact (key lctx wf₁ wf₂).mpr (hsem lctx · wf₁ wf₂)

theorem IndInfo.injectTerm?_eq_some (ht : IndInfo.injectTerm? ty (s, c) = .some t) :
  t = LamTerm.mkForallEFN (LamTerm.mkForallEFN (.mkImp (.mkEq ty
    (((c.bvarLifts s.getArgTys.length).bvarAppsRev s.getArgTys).bvarLifts s.getArgTys.length)
    (((c.bvarLifts s.getArgTys.length).bvarLifts s.getArgTys.length).bvarAppsRev s.getArgTys))
    (.mkAndN (s.getArgTys.zipIdx.map fun (a, i) => LamTerm.mkEq a
      (.bvar (s.getArgTys.length + s.getArgTys.length - 1 - i)) (.bvar (s.getArgTys.length - 1 - i)))))
    s.getArgTys) s.getArgTys := by
  unfold injectTerm? at ht; dsimp only at ht
  split at ht
  case isTrue => cases ht
  case isFalse =>
    cases ht
    rw [LamTerm.mkForallEFN_append, Nat.two_mul, LamTerm.bvarLifts, LamTerm.bvarLifts_add]

theorem IndInfo.injectTerm?_isSome (h : s.getArgTys ≠ []) : ∃ t, IndInfo.injectTerm? ty (s, c) = .some t := by
  unfold injectTerm?; simp [h]

theorem IndInfo.injectTerm_lctx {lctx : Nat → LamSort} {as : List LamSort} (i : Fin as.length) :
  pushLCtxs as.reverse (pushLCtxs as.reverse lctx) (as.length + as.length - 1 - i) = as[i] := by
  rw [show as.length + as.length - 1 - i = as.reverse.length + (as.length - 1 - i) by simp; omega,
    pushLCtxs_length_add, pushLCtxs_reverse_get]

theorem IndInfo.injectTerm_val {lval : LamValuation.{u}} {lctx : Nat → LamSort}
  {lctxTerm : ∀ n, (lctx n).interp lval.tyVal} {as : List LamSort}
  (xs ys : HList (LamSort.interp lval.tyVal) as) (i : Fin as.length) :
  HEq (pushLCtxsDep ys.reverse (pushLCtxsDep xs.reverse lctxTerm) (as.length + as.length - 1 - i)) (xs.get i) := by
  rw [show as.length + as.length - 1 - i = as.reverse.length + (as.length - 1 - i) by simp; omega]
  exact (pushLCtxsDep_length_add _ _ _).trans (pushLCtxsDep_reverse_get _ _ _)

/-- `IndInfo.injectTerm? ty c` is valid iff `c` is injective -/
theorem IndInfo.injectTerm?_valid {lval : LamValuation.{u}} {ty : LamSort} {c : LamSort × LamTerm}
  (ht : IndInfo.injectTerm? ty c = .some t)
  (hwf : ∀ lctx, Nonempty (LamWF lval.toLamTyVal ⟨lctx, c.2, .mkFuncs ty c.1.getArgTys⟩)) :
  LamThmValid lval [] t ↔ ∀ lctx lctxTerm (wf : LamWF lval.toLamTyVal ⟨lctx, c.2, .mkFuncs ty c.1.getArgTys⟩) xs ys,
    LamSort.uncurry (wf.interp lval lctx lctxTerm) xs = LamSort.uncurry (wf.interp lval lctx lctxTerm) ys → xs = ys := by
  obtain ⟨s, c⟩ := c
  dsimp only at hwf ⊢
  have ht := injectTerm?_eq_some ht
  generalize s.getArgTys = as at hwf ht ⊢
  have key : ∀ lctx (wf : LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs ty as⟩), LamValid lval lctx t ↔
    ∀ lctxTerm xs ys, LamSort.uncurry (wf.interp lval lctx lctxTerm) xs =
      LamSort.uncurry (wf.interp lval lctx lctxTerm) ys → xs = ys := by
    intro lctx wf
    have hwfeqs : Nonempty (HList (fun t => LamWF lval.toLamTyVal ⟨pushLCtxs as.reverse (pushLCtxs as.reverse lctx), t, .base .prop⟩)
      (as.zipIdx.map fun (a, i) => LamTerm.mkEq a (.bvar (as.length + as.length - 1 - i)) (.bvar (as.length - 1 - i)))) := by
      apply HList.nonempty_of_forall_mem; intro e he
      obtain ⟨⟨a, i⟩, hmem, rfl⟩ := List.mem_map.mp he
      obtain ⟨hi, ha⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
      dsimp only at hi ha; subst ha
      exact ⟨LamWF.mkEq (LamWF.ofBVar' _ _ (injectTerm_lctx ⟨i, hi⟩)) (LamWF.ofBVar' _ _ (pushLCtxs_reverse_get _ ⟨i, hi⟩))⟩
    obtain ⟨wfeqs⟩ := hwfeqs
    let wfX := LamWF.bvarLifts (xs := as.reverse) List.length_reverse _
      (LamWF.bvarAppsRev (LamWF.bvarLifts (xs := as.reverse) List.length_reverse _ wf))
    let wfY := LamWF.bvarAppsRev (LamWF.bvarLifts (xs := as.reverse) List.length_reverse _
      (LamWF.bvarLifts (xs := as.reverse) List.length_reverse _ wf))
    rw [ht, LamValid.iff_of_wf (LamWF.mkForallEFN (LamWF.mkForallEFN (.mkImp (.mkEq wfX wfY) (.mkAndN wfeqs))))]
    apply forall_congr'; intro lctxTerm
    rw [LamWF.interp_eqForallEFN_reverse]; apply forall_congr'; intro xs
    rw [LamWF.interp_eqForallEFN_reverse]; apply forall_congr'; intro ys
    rw [LamWF.interp_eqImp, LamWF.interp_eqEq, LamWF.interp_eqAndN]
    rw [← LamWF.interp_bvarLifts, LamWF.interp_bvarLifts_bvarAppsRev wf]
    rw [LamWF.interp_bvarLifts_bvarAppsRev (LamWF.bvarLifts List.length_reverse _ wf), ← LamWF.interp_bvarLifts]
    apply imp_congr_right; intro _
    constructor
    · intro heqs; apply HList.ext; intro i
      have := heqs _ (List.mem_map.mpr ⟨(as[i], i.val), List.mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩)
        (LamWF.mkEq (LamWF.ofBVar' _ _ (injectTerm_lctx i)) (LamWF.ofBVar' _ _ (pushLCtxs_reverse_get _ i)))
      rw [LamWF.interp_eqEq] at this
      apply eq_of_heq
      apply HEq.trans (injectTerm_val (lctxTerm := lctxTerm) xs ys i).symm
      apply HEq.trans (LamWF.interp_bvar _).symm
      apply HEq.trans (heq_of_eq this)
      exact (LamWF.interp_bvar _).trans (pushLCtxsDep_reverse_get _ _ _)
    · intro hxy; cases hxy
      intro e he wfe
      obtain ⟨⟨a, i⟩, hmem, rfl⟩ := List.mem_map.mp he
      obtain ⟨hi, ha⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
      dsimp only at hi ha; subst ha
      have ⟨wf₁, wf₂, hwfe⟩ : ∃ (wf₁ : LamWF lval.toLamTyVal ⟨_, _, as[i]⟩) (wf₂ : LamWF lval.toLamTyVal ⟨_, _, as[i]⟩),
        wfe = LamWF.mkEq wf₁ wf₂ := match wfe with | .ofApp _ (.ofApp _ (.ofBase (.ofEq _)) wf₁) wf₂ => ⟨wf₁, wf₂, rfl⟩
      rw [hwfe, LamWF.interp_eqEq]
      apply eq_of_heq; apply (LamWF.interp_bvar _).trans; apply HEq.symm; apply (LamWF.interp_bvar _).trans
      exact (pushLCtxsDep_reverse_get _ _ ⟨i, hi⟩).trans (injectTerm_val (lctxTerm := lctxTerm) xs xs ⟨i, hi⟩).symm
  refine ⟨fun hv lctx lctxTerm wf => (key lctx wf).mp (hv lctx) lctxTerm, fun hsem lctx => ?_⟩
  obtain ⟨wf⟩ := hwf lctx
  exact (key lctx wf).mpr (hsem lctx · wf)

/-- The term `∀ x₁ ⋯ xₙ, projᵢ (c x₁ ⋯ xₙ) = xᵢ` of `IndInfo.projTerms` is valid iff `proj` projects the `i`-th argument of `c` -/
theorem IndInfo.projTerm_valid {lval : LamValuation.{u}} {ty : LamSort} {c proj : LamTerm} {as : List LamSort}
  (i : Fin as.length)
  (hwfc : ∀ lctx, Nonempty (LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs ty as⟩))
  (hwfp : ∀ lctx, Nonempty (LamWF lval.toLamTyVal ⟨lctx, proj, .func ty as[i]⟩)) :
  LamThmValid lval [] (LamTerm.mkForallEFN (.mkEq as[i]
    (.app ty (proj.bvarLifts as.length) ((c.bvarLifts as.length).bvarAppsRev as)) (.bvar (as.length - 1 - i))) as) ↔
  ∀ lctx lctxTerm (wfc : LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs ty as⟩)
    (wfp : LamWF lval.toLamTyVal ⟨lctx, proj, .func ty as[i]⟩) xs,
    wfp.interp lval lctx lctxTerm (LamSort.uncurry (wfc.interp lval lctx lctxTerm) xs) = xs.get i := by
  have key : ∀ lctx (wfc : LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs ty as⟩)
    (wfp : LamWF lval.toLamTyVal ⟨lctx, proj, .func ty as[i]⟩),
    LamValid lval lctx (LamTerm.mkForallEFN (.mkEq as[i]
      (.app ty (proj.bvarLifts as.length) ((c.bvarLifts as.length).bvarAppsRev as)) (.bvar (as.length - 1 - i))) as) ↔
    ∀ lctxTerm xs, wfp.interp lval lctx lctxTerm (LamSort.uncurry (wfc.interp lval lctx lctxTerm) xs) = xs.get i := by
    intro lctx wfc wfp
    let wfP := LamWF.bvarLifts (xs := as.reverse) List.length_reverse _ wfp
    let wfC := LamWF.bvarAppsRev (LamWF.bvarLifts (xs := as.reverse) List.length_reverse _ wfc)
    rw [LamValid.iff_of_wf (LamWF.mkForallEFN (.mkEq (.ofApp _ wfP wfC) (LamWF.ofBVar' _ _ (pushLCtxs_reverse_get lctx i))))]
    apply forall_congr'; intro lctxTerm
    rw [LamWF.interp_eqForallEFN_reverse]; apply forall_congr'; intro xs
    rw [LamWF.interp_eqEq, LamWF.interp_ofApp, ← LamWF.interp_bvarLifts, LamWF.interp_bvarLifts_bvarAppsRev wfc]
    rw [eq_of_heq ((LamWF.interp_bvar _).trans (pushLCtxsDep_reverse_get xs lctxTerm i))]
  refine ⟨fun hv lctx lctxTerm wfc wfp => (key lctx wfc wfp).mp (hv lctx) lctxTerm, fun hsem lctx => ?_⟩
  obtain ⟨wfc⟩ := hwfc lctx; obtain ⟨wfp⟩ := hwfp lctx
  exact (key lctx wfc wfp).mpr (hsem lctx · wfc wfp)

theorem IndInfo.projTerm_wf {lval : LamValuation.{u}} {ty : LamSort} {c proj : LamTerm} {as : List LamSort}
  (i : Fin as.length) (hv : LamThmValid lval [] (LamTerm.mkForallEFN (.mkEq as[i]
    (.app ty (proj.bvarLifts as.length) ((c.bvarLifts as.length).bvarAppsRev as)) (.bvar (as.length - 1 - i))) as))
  (lctx : Nat → LamSort) : Nonempty (LamWF lval.toLamTyVal ⟨lctx, proj, .func ty as[i]⟩) :=
  have ⟨wf, _⟩ := hv lctx
  ⟨LamWF.fromBVarLifts (xs := as.reverse) List.length_reverse _ (LamWF.fromMkForallEFN wf).getFn.getArg.getFn⟩

theorem MutualIndInfo.recArg?_eq_some {mind : MutualIndInfo} (h : mind.recArg? a = .some l) :
  ∃ (hl : l < mind.length), mind[l].type = a.getResTy := by
  unfold recArg? at h; dsimp only at h
  split at h
  case isTrue => cases h
  case isFalse =>
    obtain ⟨hl, heq, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    rw [List.length_map] at hl
    exact ⟨hl, by rw [beq_iff_eq, List.getElem_map] at heq; exact heq⟩

theorem MutualIndInfo.motiveTys_lctx (mind : MutualIndInfo) (lctx : Nat → LamSort) (j : Nat) (hj : j < mind.length) :
  pushLCtxs mind.motiveTys.reverse lctx (mind.length - 1 - j) = .func mind[j].type (.base .prop) := by
  have := pushLCtxs_reverse_get (xs := mind.motiveTys) lctx ⟨j, by simp [hj]⟩
  simp only [List.length_map, Fin.getElem_fin, List.getElem_map] at this; exact this

theorem MutualIndInfo.indHypTerm?_motive_lctx {mind : MutualIndInfo} {lctx : Nat → LamSort} {as bs : List LamSort}
  (hl : l < mind.length) (hty : mind[l].type = s) :
  pushLCtxs bs.reverse (pushLCtxs as.reverse (pushLCtxs mind.motiveTys.reverse lctx))
    (as.length + bs.length + mind.length - 1 - l) = .func s (.base .prop) := by
  rw [show as.length + bs.length + mind.length - 1 - l = bs.reverse.length + (as.reverse.length + (mind.length - 1 - l))
    by simp; omega, pushLCtxs_length_add, pushLCtxs_length_add, motiveTys_lctx _ _ _ hl, hty]

theorem MutualIndInfo.indHypTerm?_arg_lctx {lctx : Nat → LamSort} {as : List LamSort} (i : Fin as.length) :
  pushLCtxs as[i].getArgTys.reverse (pushLCtxs as.reverse lctx) (as[i].getArgTys.length + as.length - 1 - i) =
    .mkFuncs as[i].getResTy as[i].getArgTys := by
  rw [show as[i].getArgTys.length + as.length - 1 - i = as[i].getArgTys.reverse.length + (as.length - 1 - i)
    by simp; omega, pushLCtxs_length_add, pushLCtxs_reverse_get, LamSort.getArgTys_getResTy_eq]

theorem MutualIndInfo.indHypTerm?_wf {ltv : LamTyVal} {mind : MutualIndInfo} {lctx : Nat → LamSort} {as : List LamSort}
  (i : Fin as.length) (hh : mind.indHypTerm? as.length as[i] i = .some h) :
  Nonempty (LamWF ltv ⟨pushLCtxs as.reverse (pushLCtxs mind.motiveTys.reverse lctx), h, .base .prop⟩) := by
  unfold indHypTerm? at hh; dsimp only at hh
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨hlt, hty⟩ := recArg?_eq_some hl
  exact ⟨LamWF.mkForallEFN (.ofApp _ (LamWF.ofBVar' _ _ (indHypTerm?_motive_lctx hlt hty))
    (LamWF.bvarAppsRev (LamWF.ofBVar' _ _ (indHypTerm?_arg_lctx i))))⟩

theorem MutualIndInfo.indHypTerm?_interp {lval : LamValuation.{u}} {mind : MutualIndInfo} {lctx : Nat → LamSort}
  {lctxTerm : ∀ n, (lctx n).interp lval.tyVal} {as : List LamSort} (i : Fin as.length)
  (hh : mind.indHypTerm? as.length as[i] i = .some h)
  (Ps : HList (LamSort.interp lval.tyVal) mind.motiveTys) (xs : HList (LamSort.interp lval.tyVal) as)
  (wf : LamWF lval.toLamTyVal ⟨pushLCtxs as.reverse (pushLCtxs mind.motiveTys.reverse lctx), h, .base .prop⟩) :
  GLift.down (wf.interp lval _ (pushLCtxsDep xs.reverse (pushLCtxsDep Ps.reverse lctxTerm))) ↔
  ∀ (l : Nat) (hl : l < mind.length), mind.recArg? as[i] = .some l →
    ∀ (f : (LamSort.mkFuncs mind[l].type as[i].getArgTys).interp lval.tyVal), HEq f (xs.get i) →
    ∀ ys (g : (LamSort.func mind[l].type (.base .prop)).interp lval.tyVal),
      HEq g (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - l)) → GLift.down (g (LamSort.uncurry f ys)) := by
  unfold indHypTerm? at hh; dsimp only at hh
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨hlt, hty⟩ := recArg?_eq_some hl
  let wfm := LamWF.ofBVar' (ltv := lval.toLamTyVal) _ _
    (indHypTerm?_motive_lctx (lctx := lctx) (as := as) (bs := as[i].getArgTys) hlt hty)
  let wfx := LamWF.ofBVar' (ltv := lval.toLamTyVal) _ _
    (indHypTerm?_arg_lctx (lctx := pushLCtxs mind.motiveTys.reverse lctx) i)
  rw [LamWF.interp_substWF (wf' := LamWF.mkForallEFN (.ofApp _ wfm (LamWF.bvarAppsRev wfx)))]
  rw [LamWF.interp_eqForallEFN_reverse]
  have hfx : ∀ (ys : HList (LamSort.interp lval.tyVal) as[i].getArgTys),
    HEq (wfx.interp lval _ (pushLCtxsDep ys.reverse (pushLCtxsDep xs.reverse (pushLCtxsDep Ps.reverse lctxTerm))))
    (xs.get i) := by
    intro ys; apply (LamWF.interp_bvar _).trans
    rw [show as[i].getArgTys.length + as.length - 1 - i = as[i].getArgTys.reverse.length + (as.length - 1 - i)
      by simp; omega]
    exact (pushLCtxsDep_length_add _ _ _).trans (pushLCtxsDep_reverse_get _ _ _)
  have hgm : ∀ (ys : HList (LamSort.interp lval.tyVal) as[i].getArgTys),
    HEq (wfm.interp lval _ (pushLCtxsDep ys.reverse (pushLCtxsDep xs.reverse (pushLCtxsDep Ps.reverse lctxTerm))))
    (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - l)) := by
    intro ys; apply (LamWF.interp_bvar _).trans
    rw [show as.length + as[i].getArgTys.length + mind.length - 1 - l =
      as[i].getArgTys.reverse.length + (as.reverse.length + (mind.length - 1 - l)) by simp; omega]
    exact (pushLCtxsDep_length_add _ _ _).trans (pushLCtxsDep_length_add _ _ _)
  constructor
  · intro hb l' _ hl' f hf ys g hg
    rw [hl] at hl'; cases hl'
    have hb := hb ys
    rw [LamWF.interp_ofApp, LamWF.interp_bvarAppsRev_uncurry wfx] at hb
    rwa [congr_heq (hg.trans (hgm ys).symm) (LamSort.uncurry_heq hty (hf.trans (hfx ys).symm) ys)]
  · intro hsem ys
    rw [LamWF.interp_ofApp, LamWF.interp_bvarAppsRev_uncurry wfx]
    have hsem := hsem l hlt hl
    rw [hty] at hsem
    exact hsem _ (hfx ys) ys _ (hgm ys)

theorem MutualIndInfo.ctorHypTerm_motive_lctx {mind : MutualIndInfo} {lctx : Nat → LamSort} {as : List LamSort}
  (hj : j < mind.length) :
  pushLCtxs as.reverse (pushLCtxs mind.motiveTys.reverse lctx) (as.length + mind.length - 1 - j) =
    .func mind[j].type (.base .prop) := by
  rw [show as.length + mind.length - 1 - j = as.reverse.length + (mind.length - 1 - j) by simp; omega,
    pushLCtxs_length_add, motiveTys_lctx _ _ _ hj]

theorem MutualIndInfo.ctorHypTerm_eq {mind : MutualIndInfo} :
  mind.ctorHypTerm ty j s c = LamTerm.mkForallEFN (.mkImpN (s.getArgTys.zipIdx.filterMap fun (a, i) =>
    mind.indHypTerm? s.getArgTys.length a i) (.app ty (mind.motive j s.getArgTys.length)
      (((c.bvarLifts mind.length).bvarLifts s.getArgTys.length).bvarAppsRev s.getArgTys))) s.getArgTys := by
  unfold ctorHypTerm; dsimp only
  rw [Nat.add_comm mind.length, LamTerm.bvarLifts, LamTerm.bvarLifts_add]

theorem MutualIndInfo.ctorHypTerm_ihs_wf {ltv : LamTyVal} {mind : MutualIndInfo} {lctx : Nat → LamSort} {as : List LamSort} :
  Nonempty (HList (fun h => LamWF ltv ⟨pushLCtxs as.reverse (pushLCtxs mind.motiveTys.reverse lctx), h, .base .prop⟩)
    (as.zipIdx.filterMap fun (a, i) => mind.indHypTerm? as.length a i)) := by
  apply HList.nonempty_of_forall_mem; intro h hh
  obtain ⟨⟨a, i⟩, hmem, hh⟩ := List.mem_filterMap.mp hh
  obtain ⟨hi, ha⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
  dsimp only at hi ha hh; subst ha
  exact indHypTerm?_wf ⟨i, hi⟩ hh

theorem MutualIndInfo.ctorHypTerm_wf {ltv : LamTyVal} {mind : MutualIndInfo} {lctx : Nat → LamSort}
  (hj : j < mind.length) (wfc : LamWF ltv ⟨lctx, c, .mkFuncs mind[j].type s.getArgTys⟩) :
  Nonempty (LamWF ltv ⟨pushLCtxs mind.motiveTys.reverse lctx, mind.ctorHypTerm mind[j].type j s c, .base .prop⟩) := by
  rw [ctorHypTerm_eq]
  obtain ⟨wfihs⟩ := ctorHypTerm_ihs_wf (ltv := ltv) (mind := mind) (lctx := lctx) (as := s.getArgTys)
  exact ⟨LamWF.mkForallEFN (.mkImpN wfihs (.ofApp _ (LamWF.ofBVar' _ _ (ctorHypTerm_motive_lctx hj))
    (LamWF.bvarAppsRev (LamWF.bvarLifts (xs := s.getArgTys.reverse) List.length_reverse _
      (LamWF.bvarLifts (xs := mind.motiveTys.reverse) (by simp) _ wfc)))))⟩

theorem MutualIndInfo.ctorHypTerm_interp {lval : LamValuation.{u}} {mind : MutualIndInfo} {lctx : Nat → LamSort}
  {lctxTerm : ∀ n, (lctx n).interp lval.tyVal} (hj : j < mind.length)
  (wfc : LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs mind[j].type s.getArgTys⟩)
  (Ps : HList (LamSort.interp lval.tyVal) mind.motiveTys)
  (wf : LamWF lval.toLamTyVal ⟨pushLCtxs mind.motiveTys.reverse lctx, mind.ctorHypTerm mind[j].type j s c, .base .prop⟩) :
  GLift.down (wf.interp lval _ (pushLCtxsDep Ps.reverse lctxTerm)) ↔
  ∀ (xs : HList (LamSort.interp lval.tyVal) s.getArgTys),
    (∀ (i : Fin s.getArgTys.length) (l : Nat) (hl : l < mind.length), mind.recArg? s.getArgTys[i] = .some l →
      ∀ (f : (LamSort.mkFuncs mind[l].type s.getArgTys[i].getArgTys).interp lval.tyVal), HEq f (xs.get i) →
      ∀ ys (g : (LamSort.func mind[l].type (.base .prop)).interp lval.tyVal),
        HEq g (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - l)) → GLift.down (g (LamSort.uncurry f ys))) →
    ∀ (g : (LamSort.func mind[j].type (.base .prop)).interp lval.tyVal),
      HEq g (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j)) →
      GLift.down (g (LamSort.uncurry (wfc.interp lval lctx lctxTerm) xs)) := by
  obtain ⟨wfihs⟩ := ctorHypTerm_ihs_wf (ltv := lval.toLamTyVal) (mind := mind) (lctx := lctx) (as := s.getArgTys)
  let wfm := LamWF.ofBVar' (ltv := lval.toLamTyVal) _ _ (ctorHypTerm_motive_lctx (lctx := lctx) (as := s.getArgTys) hj)
  let wfc' := LamWF.bvarLifts (lvl := mind.length) (xs := mind.motiveTys.reverse) (by simp) _ wfc
  let wf' := LamWF.mkForallEFN (.mkImpN wfihs (.ofApp _ wfm
    (LamWF.bvarAppsRev (LamWF.bvarLifts (xs := s.getArgTys.reverse) List.length_reverse _ wfc'))))
  rw [LamWF.interp_eq lval HEq.rfl wf wf' ctorHypTerm_eq, LamWF.interp_eqForallEFN_reverse]
  apply forall_congr'; intro xs
  rw [LamWF.interp_eqImpN, LamWF.interp_ofApp, LamWF.interp_bvarLifts_bvarAppsRev wfc', ← LamWF.interp_bvarLifts]
  have hm : HEq (wfm.interp lval _ (pushLCtxsDep xs.reverse (pushLCtxsDep Ps.reverse lctxTerm)))
    (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j)) := by
    apply (LamWF.interp_bvar _).trans
    rw [show s.getArgTys.length + mind.length - 1 - j = s.getArgTys.reverse.length + (mind.length - 1 - j)
      by simp; omega]
    exact pushLCtxsDep_length_add _ _ _
  apply imp_congr
  · constructor
    · intro hihs i l hl hrec
      obtain ⟨h, hh⟩ : ∃ h, mind.indHypTerm? s.getArgTys.length s.getArgTys[i] i = .some h :=
        ⟨_, by unfold indHypTerm?; rw [hrec]; rfl⟩
      obtain ⟨wfh⟩ := indHypTerm?_wf (ltv := lval.toLamTyVal) (lctx := lctx) i hh
      exact (indHypTerm?_interp i hh Ps xs wfh).mp (hihs _ (List.mem_filterMap.mpr
        ⟨(s.getArgTys[i], i.val), List.mem_zipIdx_iff_getElem?.mpr (by simp), hh⟩) wfh) l hl hrec
    · intro hih h hh wfh
      obtain ⟨⟨a, i⟩, hmem, hh⟩ := List.mem_filterMap.mp hh
      obtain ⟨hi, ha⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
      dsimp only at hi ha hh; subst ha
      exact (indHypTerm?_interp ⟨i, hi⟩ hh Ps xs wfh).mpr (hih ⟨i, hi⟩)
  · exact ⟨fun hb g hg => by rwa [congr_heq (hg.trans hm.symm) HEq.rfl], fun h => h _ hm⟩

/-- `∀ P₁ ⋯ Pₖ, H₁ → ⋯ → Hₘ → C₁ ∧ ⋯ ∧ Cᵣ`, as in `MutualIndInfo.inductionTerm` -/
theorem MutualIndInfo.inductionTerm_valid_aux {lval : LamValuation.{u}} {ms : List LamSort} {hyps concls : List LamTerm}
  (hwfh : ∀ lctx, ∀ h ∈ hyps, Nonempty (LamWF lval.toLamTyVal ⟨pushLCtxs ms.reverse lctx, h, .base .prop⟩))
  (hwfc : ∀ lctx, ∀ e ∈ concls, Nonempty (LamWF lval.toLamTyVal ⟨pushLCtxs ms.reverse lctx, e, .base .prop⟩)) :
  LamThmValid lval [] (LamTerm.mkForallEFN (.mkImpN hyps (.mkAndN concls)) ms) ↔
  ∀ lctx lctxTerm (Ps : HList (LamSort.interp lval.tyVal) ms),
    (∀ h ∈ hyps, ∀ (wf : LamWF lval.toLamTyVal ⟨pushLCtxs ms.reverse lctx, h, .base .prop⟩),
      GLift.down (wf.interp lval _ (pushLCtxsDep Ps.reverse lctxTerm))) →
    ∀ e ∈ concls, ∀ (wf : LamWF lval.toLamTyVal ⟨pushLCtxs ms.reverse lctx, e, .base .prop⟩),
      GLift.down (wf.interp lval _ (pushLCtxsDep Ps.reverse lctxTerm)) := by
  have key : ∀ lctx, LamValid lval lctx (LamTerm.mkForallEFN (.mkImpN hyps (.mkAndN concls)) ms) ↔
    ∀ lctxTerm (Ps : HList (LamSort.interp lval.tyVal) ms),
      (∀ h ∈ hyps, ∀ (wf : LamWF lval.toLamTyVal ⟨pushLCtxs ms.reverse lctx, h, .base .prop⟩),
        GLift.down (wf.interp lval _ (pushLCtxsDep Ps.reverse lctxTerm))) →
      ∀ e ∈ concls, ∀ (wf : LamWF lval.toLamTyVal ⟨pushLCtxs ms.reverse lctx, e, .base .prop⟩),
        GLift.down (wf.interp lval _ (pushLCtxsDep Ps.reverse lctxTerm)) := by
    intro lctx
    obtain ⟨wfh⟩ := HList.nonempty_of_forall_mem (hwfh lctx)
    obtain ⟨wfc⟩ := HList.nonempty_of_forall_mem (hwfc lctx)
    rw [LamValid.iff_of_wf (LamWF.mkForallEFN (.mkImpN wfh (.mkAndN wfc)))]
    apply forall_congr'; intro lctxTerm
    rw [LamWF.interp_eqForallEFN_reverse]; apply forall_congr'; intro Ps
    rw [LamWF.interp_eqImpN, LamWF.interp_eqAndN]
  exact ⟨fun hv lctx => (key lctx).mp (hv lctx), fun h lctx => (key lctx).mpr (h lctx)⟩

theorem MutualIndInfo.inductionTerm_wfCtor {lval : LamValuation.{u}} {mind : MutualIndInfo}
  (hv : LamThmValid lval [] mind.inductionTerm) (lctx : Nat → LamSort) (j : Fin mind.length)
  (c : Fin mind[j].ctors.length) : Nonempty (mind[j].CtorWF lval.toLamTyVal lctx c) := by
  obtain ⟨wf, _⟩ := hv lctx
  unfold inductionTerm at wf; dsimp only at wf
  have ⟨hhyps, _⟩ := LamWF.fromMkImpN (LamWF.fromMkForallEFN wf)
  obtain ⟨wfh⟩ := hhyps (mind.ctorHypTerm mind[j].type j mind[j].ctors[c].1 mind[j].ctors[c].2)
    (List.mem_flatMap.mpr ⟨(mind[j], j.val), List.mem_zipIdx_iff_getElem?.mpr (by simp),
      List.mem_map.mpr ⟨mind[j].ctors[c], List.getElem_mem _, rfl⟩⟩)
  rw [ctorHypTerm_eq] at wfh
  obtain ⟨_, ⟨wfb⟩⟩ := LamWF.fromMkImpN (LamWF.fromMkForallEFN wfh)
  exact ⟨LamWF.fromBVarLifts (lvl := mind.length) (xs := mind.motiveTys.reverse) (by simp) _
    (LamWF.fromBVarLifts (xs := mind[j].ctors[c].1.getArgTys.reverse) List.length_reverse _
      (LamWF.fromBVarAppsRev wfb.getArg))⟩

/-- `MutualIndInfo.inductionTerm` is valid iff induction holds for the interpretations of the constructors -/
theorem MutualIndInfo.inductionTerm_valid {lval : LamValuation.{u}} {mind : MutualIndInfo}
  (hwf : ∀ lctx (j : Fin mind.length) (c : Fin mind[j].ctors.length), Nonempty (mind[j].CtorWF lval.toLamTyVal lctx c)) :
  LamThmValid lval [] mind.inductionTerm ↔
  ∀ lctx lctxTerm (P : (j : Fin mind.length) → mind[j].type.interp lval.tyVal → Prop),
    (∀ (j : Fin mind.length) (c : Fin mind[j].ctors.length) (wf : mind[j].CtorWF lval.toLamTyVal lctx c)
      (xs : HList (LamSort.interp lval.tyVal) (mind[j].argTys c)),
      (∀ (i : Fin (mind[j].argTys c).length) (l : Fin mind.length), mind.recArg? (mind[j].argTys c)[i] = .some l →
        ∀ (f : (LamSort.mkFuncs mind[l].type (mind[j].argTys c)[i].getArgTys).interp lval.tyVal),
          HEq f (xs.get i) → ∀ ys, P l (LamSort.uncurry f ys)) →
      P j (LamSort.uncurry (wf.interp lval lctx lctxTerm) xs)) →
    ∀ j x, P j x := by
  refine (inductionTerm_valid_aux ?_ ?_).trans ?_
  · intro lctx h hh
    obtain ⟨⟨ii, j⟩, hmem, hh⟩ := List.mem_flatMap.mp hh
    obtain ⟨hj, hii⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
    dsimp only at hj hii hh; subst hii
    obtain ⟨⟨s, c⟩, hsc, rfl⟩ := List.mem_map.mp hh
    obtain ⟨c', hc', hsc'⟩ := List.mem_iff_getElem.mp hsc
    have hwfc := hwf lctx ⟨j, hj⟩ ⟨c', hc'⟩
    simp only [IndInfo.CtorWF, IndInfo.argTys, Fin.getElem_fin, hsc'] at hwfc
    obtain ⟨wfc⟩ := hwfc
    exact ctorHypTerm_wf hj wfc
  · intro lctx e he
    obtain ⟨⟨ii, j⟩, hmem, rfl⟩ := List.mem_map.mp he
    obtain ⟨hj, hii⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
    dsimp only at hj hii; subst hii
    exact ⟨LamWF.mkForallEF (.ofApp _ (LamWF.ofBVar' _ _
      ((pushLCtxs_singleton _ _).symm ▸ ctorHypTerm_motive_lctx (as := [mind[j].type]) hj)) (.ofBVar 0))⟩
  -- The motive `Pⱼ` applied to `x`, where `x` is bound by the conclusion `∀ x, Pⱼ x`
  have hconcl : ∀ lctx lctxTerm (Ps : HList (LamSort.interp lval.tyVal) mind.motiveTys) (j : Fin mind.length)
    (wfe : LamWF lval.toLamTyVal ⟨pushLCtxs mind.motiveTys.reverse lctx,
      .mkForallEF mind[j].type (.app mind[j].type (mind.motive j 1) (.bvar 0)), .base .prop⟩),
    GLift.down (wfe.interp lval _ (pushLCtxsDep Ps.reverse lctxTerm)) ↔ ∀ (x : mind[j].type.interp lval.tyVal),
      ∀ g : (LamSort.func mind[j].type (.base .prop)).interp lval.tyVal,
        HEq g (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j)) → GLift.down (g x) := by
    intro lctx lctxTerm Ps j wfe
    let wfm := LamWF.ofBVar' (ltv := lval.toLamTyVal) _ _
      ((pushLCtxs_singleton _ _).symm ▸ ctorHypTerm_motive_lctx (lctx := lctx) (as := [mind[j].type]) j.isLt)
    rw [LamWF.interp_substWF (wf' := LamWF.mkForallEF (.ofApp _ wfm (.ofBVar 0))), LamWF.interp_eqForallEF]
    apply forall_congr'; intro x
    rw [LamWF.interp_ofApp]
    have hm : HEq (wfm.interp lval _ (pushLCtxDep x (pushLCtxsDep Ps.reverse lctxTerm)))
      (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j)) := by
      apply (LamWF.interp_bvar _).trans
      rw [show [mind[j].type].length + mind.length - 1 - j = (mind.length - 1 - j) + 1 by simp; omega]
      rfl
    exact ⟨fun hb g hg => by rwa [congr_heq (hg.trans hm.symm) HEq.rfl], fun h => h _ hm⟩
  constructor
  · intro hL lctx lctxTerm P H j x
    have hPs : ∀ (i : Fin mind.motiveTys.length), (LamSort.func (mind[i.val]'(by simpa using i.isLt)).type
      (.base .prop)).interp lval.tyVal = mind.motiveTys[i].interp lval.tyVal := fun i => by
      simp only [motiveTys, Fin.getElem_fin, List.getElem_map]
    let Ps : HList (LamSort.interp lval.tyVal) mind.motiveTys := HList.ofFn fun i =>
      cast (hPs i) (fun y => GLift.up (P ⟨i.val, by simpa using i.isLt⟩ y))
    have hval : ∀ (j : Fin mind.length), HEq (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j))
      (fun y : mind[j].type.interp lval.tyVal => (GLift.up (P j y) : (LamSort.base .prop).interp lval.tyVal)) := by
      intro j
      have := pushLCtxsDep_reverse_get Ps lctxTerm ⟨j, by simp⟩
      rw [show mind.motiveTys.length - 1 - j = mind.length - 1 - j by simp] at this
      apply this.trans
      rw [HList.get_ofFn]; exact cast_heq _ _
    have hP : ∀ (j : Fin mind.length) y, (∀ g : (LamSort.func mind[j].type (.base .prop)).interp lval.tyVal,
      HEq g (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j)) → GLift.down (g y)) ↔ P j y := fun j y =>
      ⟨fun h => h _ (hval j).symm, fun hp g hg => by rw [eq_of_heq (hg.trans (hval j))]; exact hp⟩
    refine (hP j x).mp ((hconcl lctx lctxTerm Ps j _).mp (hL lctx lctxTerm Ps ?_ _ (List.mem_map.mpr
      ⟨(mind[j], j.val), List.mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩) ?wfe) x)
    case wfe =>
      exact LamWF.mkForallEF (.ofApp _ (LamWF.ofBVar' _ _
        ((pushLCtxs_singleton _ _).symm ▸ ctorHypTerm_motive_lctx (as := [mind[j].type]) j.isLt)) (.ofBVar 0))
    intro h hh wfh
    obtain ⟨⟨ii, j'⟩, hmem, hh⟩ := List.mem_flatMap.mp hh
    obtain ⟨hj', hii⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
    dsimp only at hj' hii hh; subst hii
    obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hh
    obtain ⟨c', hc', rfl⟩ := List.mem_iff_getElem.mp hsc
    obtain ⟨wfc⟩ := hwf lctx ⟨j', hj'⟩ ⟨c', hc'⟩
    exact (ctorHypTerm_interp (s := mind[j'].ctors[c'].1) (c := mind[j'].ctors[c'].2) hj' wfc Ps wfh).mpr
      fun xs hih g hg => (hP ⟨j', hj'⟩ _).mpr (H ⟨j', hj'⟩ ⟨c', hc'⟩ wfc xs fun i l hrec f hf ys =>
        (hP l _).mp fun g hg => hih i l l.isLt hrec f hf ys g hg) g hg
  · intro hsem lctx lctxTerm Ps hhyps e he wfe
    obtain ⟨⟨ii, j⟩, hmem, rfl⟩ := List.mem_map.mp he
    obtain ⟨hj, hii⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
    dsimp only at hj hii; subst hii
    let P : (j : Fin mind.length) → mind[j].type.interp lval.tyVal → Prop := fun j y =>
      ∀ g : (LamSort.func mind[j].type (.base .prop)).interp lval.tyVal,
        HEq g (pushLCtxsDep Ps.reverse lctxTerm (mind.length - 1 - j)) → GLift.down (g y)
    have hall := hsem lctx lctxTerm P (fun j c wfc xs hih g hg => by
      obtain ⟨wfh⟩ := ctorHypTerm_wf j.isLt wfc
      exact (ctorHypTerm_interp j.isLt wfc Ps wfh).mp (hhyps _ (List.mem_flatMap.mpr ⟨(mind[j], j.val),
        List.mem_zipIdx_iff_getElem?.mpr (by simp), List.mem_map.mpr ⟨mind[j].ctors[c], List.getElem_mem _, rfl⟩⟩) wfh) xs
        (fun i l hl hrec f hf ys g hg => hih i ⟨l, hl⟩ hrec f hf ys g hg) g hg)
    exact (hconcl lctx lctxTerm Ps ⟨j, hj⟩ wfe).mpr (hall ⟨j, hj⟩)

theorem IndInfo.mem_distinctTerms {ii : IndInfo} (ht : t ∈ ii.distinctTerms) :
  ∃ (c₁ c₂ : Fin ii.ctors.length), c₁ ≠ c₂ ∧ t = IndInfo.distinctTerm ii.type ii.ctors[c₁] ii.ctors[c₂] := by
  suffices h : ∀ l, t ∈ distinctTerms.go ii l → ∃ (i₁ i₂ : Nat) (h₁ : i₁ < l.length) (h₂ : i₂ < l.length),
      i₁ ≠ i₂ ∧ t = distinctTerm ii.type l[i₁] l[i₂] by
    obtain ⟨i₁, i₂, h₁, h₂, hne, rfl⟩ := h _ ht
    exact ⟨⟨i₁, h₁⟩, ⟨i₂, h₂⟩, fun h => hne (Fin.val_eq_of_eq h), rfl⟩
  intro l hl
  induction l with
  | nil => cases hl
  | cons c cs IH =>
    rw [distinctTerms.go, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hl
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc'
      exact ⟨0, k + 1, by simp, by simp; omega, by omega, rfl⟩
    · obtain ⟨i₁, i₂, h₁, h₂, hne, rfl⟩ := IH hl
      exact ⟨i₁ + 1, i₂ + 1, by simp; omega, by simp; omega, by omega, rfl⟩

theorem IndInfo.distinctTerm_mem {ii : IndInfo} {c₁ c₂ : Fin ii.ctors.length} (h : c₁ < c₂) :
  IndInfo.distinctTerm ii.type ii.ctors[c₁] ii.ctors[c₂] ∈ ii.distinctTerms := by
  suffices key : ∀ l (i₁ i₂ : Nat) (h₁ : i₁ < l.length) (h₂ : i₂ < l.length), i₁ < i₂ →
      distinctTerm ii.type l[i₁] l[i₂] ∈ distinctTerms.go ii l from key _ _ _ c₁.isLt c₂.isLt h
  intro l
  induction l with
  | nil => intro _ _ h₁; simp at h₁
  | cons c cs IH =>
    intro i₁ i₂ h₁ h₂ hlt
    rw [distinctTerms.go, List.mem_append]
    cases i₂ with
    | zero => omega
    | succ k =>
      cases i₁ with
      | zero => exact .inl (List.mem_map.mpr ⟨cs[k]'(by simp at h₂; omega), List.getElem_mem _, rfl⟩)
      | succ a => exact .inr (IH a k (by simp at h₁; omega) (by simp at h₂; omega) (by omega))

theorem IndInfo.mem_injectTerms {ii : IndInfo} (ht : t ∈ ii.injectTerms) :
  ∃ (c : Fin ii.ctors.length), IndInfo.injectTerm? ii.type ii.ctors[c] = .some t := by
  obtain ⟨c, hc, ht⟩ := List.mem_filterMap.mp ht
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
  exact ⟨⟨k, hk⟩, ht⟩

theorem IndInfo.injectTerm_mem {ii : IndInfo} {c : Fin ii.ctors.length}
  (ht : IndInfo.injectTerm? ii.type ii.ctors[c] = .some t) : t ∈ ii.injectTerms :=
  List.mem_filterMap.mpr ⟨ii.ctors[c], List.getElem_mem _, ht⟩

theorem IndInfo.mem_projTerms {ii : IndInfo} (ht : t ∈ ii.projTerms) :
  ∃ s c ps, ii.ctors = [(s, c)] ∧ ii.projs = .some ps ∧
    ∃ (hlen : ps.length = s.getArgTys.length) (i : Fin ps.length),
      t = LamTerm.mkForallEFN (.mkEq (s.getArgTys[i.val]'(hlen ▸ i.isLt))
        (.app ii.type (ps[i].2.bvarLifts s.getArgTys.length) ((c.bvarLifts s.getArgTys.length).bvarAppsRev s.getArgTys))
        (.bvar (s.getArgTys.length - 1 - i))) s.getArgTys := by
  unfold projTerms at ht
  split at ht
  case h_2 => cases ht
  case h_1 s c ps hc hp =>
  dsimp only at ht
  split at ht
  case isTrue => cases ht
  case isFalse hlen =>
  rw [bne_iff_ne, ne_eq, Classical.not_not] at hlen
  obtain ⟨⟨⟨⟨sp, proj⟩, a⟩, i⟩, hmem, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hmem)
  dsimp only at hi he
  rw [List.getElem_zip, Prod.mk.injEq] at he
  obtain ⟨hps, rfl⟩ := he
  have hi' : i < ps.length := by rw [List.length_zip] at hi; omega
  refine ⟨s, c, ps, hc, hp, hlen, ⟨i, hi'⟩, ?_⟩
  simp only [Fin.getElem_fin, hps]

theorem IndInfo.projTerm_mem {ii : IndInfo} (hc : ii.ctors = [(s, c)]) (hp : ii.projs = .some ps)
  (hlen : ps.length = s.getArgTys.length) (i : Fin ps.length) :
  LamTerm.mkForallEFN (.mkEq (s.getArgTys[i.val]'(hlen ▸ i.isLt))
    (.app ii.type (ps[i].2.bvarLifts s.getArgTys.length) ((c.bvarLifts s.getArgTys.length).bvarAppsRev s.getArgTys))
    (.bvar (s.getArgTys.length - 1 - i))) s.getArgTys ∈ ii.projTerms := by
  unfold projTerms; rw [hc, hp]; dsimp only
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine List.mem_map.mpr ⟨((ps[i], s.getArgTys[i.val]'(hlen ▸ i.isLt)), i.val), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_getElem (by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨i.isLt, show (i : Nat) < _ from hlen ▸ i.isLt⟩), List.getElem_zip]
  rfl

theorem MutualIndInfo.wfCtor_single {lval : LamValuation.{u}} {mind : MutualIndInfo}
  (hwf : ∀ lctx (j : Fin mind.length) (c : Fin mind[j].ctors.length), Nonempty (mind[j].CtorWF lval.toLamTyVal lctx c))
  (hj : j < mind.length) (hc : mind[j].ctors = [(s, c)]) (lctx : Nat → LamSort) :
  Nonempty (LamWF lval.toLamTyVal ⟨lctx, c, .mkFuncs mind[j].type s.getArgTys⟩) := by
  have hwfc := hwf lctx ⟨j, hj⟩ ⟨0, by simp [hc]⟩
  simp only [IndInfo.CtorWF, IndInfo.argTys, Fin.getElem_fin] at hwfc
  rwa [show mind[j].ctors[0]'(by simp [hc]) = (s, c) by simp [hc]] at hwfc

/-- `MutualIndInfo.Spec` is equivalent to `MutualIndInfo.SemSpec` -/
theorem MutualIndInfo.spec_iff_semSpec {lval : LamValuation.{u}} {mind : MutualIndInfo} :
  mind.Spec lval ↔ mind.SemSpec lval := by
  constructor
  · intro h
    obtain ⟨hty, hind⟩ := spec_iff.mp h
    have wfCtor := inductionTerm_wfCtor hind
    have hmem : ∀ (j : Fin mind.length) {t}, t ∈ mind[j].specTerms → LamThmValid lval [] t :=
      fun j _ ht => hty mind[j] (List.getElem_mem _) _ ht
    have hproj : ∀ (j : Fin mind.length) s c ps (hc : mind[j].ctors = [(s, c)]) (hp : mind[j].projs = .some ps)
      (hlen : ps.length = s.getArgTys.length) (i : Fin ps.length), LamThmValid lval [] _ :=
      fun j s c ps hc hp hlen i => hmem j (List.mem_append_right _ (IndInfo.projTerm_mem hc hp hlen i))
    refine ⟨wfCtor, ?_, ?_, ?_, ?_, (inductionTerm_valid wfCtor).mp hind⟩
    · intro lctx j s c ps hc hp hlen i
      exact IndInfo.projTerm_wf ⟨i, hlen ▸ i.isLt⟩ (hproj j s c ps hc hp hlen i) lctx
    · intro lctx lctxTerm j c₁ c₂ hne
      have key : ∀ c₁ c₂ : Fin mind[j].ctors.length, c₁ < c₂ →
        ∀ (wf₁ : mind[j].CtorWF lval.toLamTyVal lctx c₁) (wf₂ : mind[j].CtorWF lval.toLamTyVal lctx c₂) xs ys,
          LamSort.uncurry (wf₁.interp lval lctx lctxTerm) xs ≠ LamSort.uncurry (wf₂.interp lval lctx lctxTerm) ys :=
        fun c₁ c₂ hlt => (IndInfo.distinctTerm_valid (wfCtor · j c₁) (wfCtor · j c₂)).mp
          (hmem j (List.mem_append_left _ (List.mem_append_left _ (IndInfo.distinctTerm_mem hlt)))) lctx lctxTerm
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · exact key c₁ c₂ hlt
      · exact fun wf₁ wf₂ xs ys heq => key c₂ c₁ hlt wf₂ wf₁ ys xs heq.symm
    · intro lctx lctxTerm j c wf xs ys heq
      by_cases has : mind[j].ctors[c].1.getArgTys = []
      · have : ∀ {as : List LamSort} (_ : as = []) (xs ys : HList (LamSort.interp lval.tyVal) as), xs = ys := by
          intro as h xs ys; subst h; cases xs; cases ys; rfl
        exact this has xs ys
      · obtain ⟨t, ht⟩ := IndInfo.injectTerm?_isSome (ty := mind[j].type) (c := mind[j].ctors[c].2) has
        exact (IndInfo.injectTerm?_valid ht (wfCtor · j c)).mp (hmem j (List.mem_append_left _
          (List.mem_append_right _ (IndInfo.injectTerm_mem ht)))) lctx lctxTerm wf xs ys heq
    · intro lctx lctxTerm j s c ps hc hp hlen i wfp wfc xs
      exact (IndInfo.projTerm_valid ⟨i, hlen ▸ i.isLt⟩ (wfCtor_single wfCtor j.isLt hc)
        (IndInfo.projTerm_wf ⟨i, hlen ▸ i.isLt⟩ (hproj j s c ps hc hp hlen i))).mp
        (hproj j s c ps hc hp hlen i) lctx lctxTerm wfc wfp xs
  · intro h
    refine spec_iff.mpr ⟨fun ii hii t ht => ?_, (inductionTerm_valid h.wfCtor).mpr h.induction⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hii
    rw [IndInfo.specTerms, List.mem_append, List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · obtain ⟨c₁, c₂, hne, rfl⟩ := IndInfo.mem_distinctTerms ht
      exact (IndInfo.distinctTerm_valid (h.wfCtor · ⟨j, hj⟩ c₁) (h.wfCtor · ⟨j, hj⟩ c₂)).mpr
        (h.distinct · · ⟨j, hj⟩ c₁ c₂ hne)
    · obtain ⟨c, hc⟩ := IndInfo.mem_injectTerms ht
      exact (IndInfo.injectTerm?_valid hc (h.wfCtor · ⟨j, hj⟩ c)).mpr (h.inject · · ⟨j, hj⟩ c)
    · obtain ⟨s, c, ps, hc, hp, hlen, i, rfl⟩ := IndInfo.mem_projTerms ht
      exact (IndInfo.projTerm_valid ⟨i, hlen ▸ i.isLt⟩ (wfCtor_single h.wfCtor hj hc)
        (h.wfProj · ⟨j, hj⟩ s c ps hc hp hlen i)).mpr
        (fun lctx lctxTerm wfc wfp xs => h.proj lctx lctxTerm ⟨j, hj⟩ s c ps hc hp hlen i wfp wfc xs)

/--
  The W type: well-founded trees whose nodes are labelled by `a : α`,
    with one child for each element of `β a`
-/
inductive W (α : Type u) (β : α → Type v) where
  | mk (a : α) (f : β a → W α β) : W α β

/-!
  A model of simple mutual inductive types by the W type, which interprets
    `MutualIndInfo` (see `MutualIndInfo.toIndSig?`)
-/

universe u

/-- An argument of a constructor of simple mutual inductive types `T₀ ⋯ Tₖ₋₁` -/
inductive IndArg (k : Nat) where
  /-- An argument of sort `s`, which does not mention `T₀ ⋯ Tₖ₋₁` -/
  | plain (s : LamSort)
  /-- An argument of sort `B₁ → ⋯ → Bₘ → Tₗ`, where `bs = [B₁, ⋯, Bₘ]` do not mention `T₀ ⋯ Tₖ₋₁` -/
  | recur (bs : List LamSort) (l : Fin k)

/-- Simple mutual inductive types `T₀ ⋯ Tₖ₋₁`, given by the arguments of the constructors of each `Tⱼ` -/
abbrev IndSig (k : Nat) := Fin k → List (List (IndArg k))

namespace IndArg

variable (tyVal : TyVal.{u})

/-- The type of the argument, given the interpretation `T` of `T₀ ⋯ Tₖ₋₁` -/
def type (T : Fin k → Type u) : IndArg k → Type u
| plain s => s.interp tyVal
| recur bs l => HList.Funcs (LamSort.interp tyVal) bs (T l)

/-- The part of the argument stored in the label of a node of the W type -/
def shape : IndArg k → Type u
| plain s => s.interp tyVal
| recur _ _ => PUnit

/-- The children of a node of the W type for the argument, one for each element of `B₁ × ⋯ × Bₘ` -/
def child : IndArg k → Type u
| plain _ => PEmpty
| recur bs _ => HList (LamSort.interp tyVal) bs

/-- The type `Tₗ` of a child -/
def target : (x : IndArg k) → x.child tyVal → Fin k
| plain _, e => e.elim
| recur _ l, _ => l

/-- The induction hypotheses for the argument `x` with value `v`, for the motive `P` on `T` -/
def IH {T : Fin k → Type u} (P : (j : Fin k) → T j → Prop) : (x : IndArg k) → x.type tyVal T → Prop
| plain _, _ => True
| recur _ l, v => ∀ xs, P l (HList.uncurry v xs)

/-- Apply `g` to the elements of `T₀ ⋯ Tₖ₋₁` in the argument `x` with value `v` -/
def fmap {T A : Fin k → Type u} (g : ∀ l, T l → A l) : (x : IndArg k) → x.type tyVal T → x.type tyVal A
| plain _, v => v
| recur _ l, v => HList.curry fun xs => g l (HList.uncurry v xs)

/-- The value in `A` of the argument `x` with label `s`, where `rec b` is the value of the child `b` -/
def foldArg {A : Fin k → Type u} : (x : IndArg k) → x.shape tyVal → ((b : x.child tyVal) → A (x.target tyVal b)) →
  x.type tyVal A
| plain _, s, _ => s
| recur _ _, _, rec => HList.curry rec

theorem eq_of_fmap_eq {T A : Fin k → Type u} {g : ∀ l, T l → A l} : (x : IndArg k) → (v w : x.type tyVal T) →
  x.IH tyVal (fun l t => ∀ t', g l t = g l t' → t = t') v → x.fmap tyVal g v = x.fmap tyVal g w → v = w
| plain _, _, _, _, h => h
| recur _ _, _, _, ih, h => HList.uncurry_inj (funext fun xs =>
    ih xs _ (congrFun ((HList.uncurry_curry _).symm.trans ((congrArg HList.uncurry h).trans (HList.uncurry_curry _))) xs))

theorem exists_fmap_eq {T A : Fin k → Type u} (g : ∀ l, T l → A l) : (x : IndArg k) → (v : x.type tyVal A) →
  x.IH tyVal (fun l a => ∃ t, g l t = a) v → ∃ w, x.fmap tyVal g w = v
| plain _, v, _ => ⟨v, rfl⟩
| recur _ _, v, ih =>
  have ⟨f, hf⟩ := Classical.axiomOfChoice ih
  ⟨HList.curry f, by
    show HList.curry (fun xs => _) = v
    conv => rhs; rw [← HList.curry_uncurry v]
    apply congrArg; funext xs; rw [HList.uncurry_curry]; exact hf xs⟩

end IndArg

namespace IndSig

variable (tyVal : TyVal.{u}) (cs : IndSig k)

/--
  Labels of the nodes of the W type: a type `Tⱼ`, a constructor `c` of `Tⱼ`,
    and the non-recursive parts of the arguments of `c`
-/
abbrev Shape := (j : Fin k) × (c : Fin (cs j).length) × HList (IndArg.shape tyVal) (cs j)[c]

/-- Children of a node: an argument of the constructor, with an element of `B₁ × ⋯ × Bₘ` -/
abbrev Child (a : cs.Shape tyVal) := (i : Fin (cs a.1)[a.2.1].length) × ((cs a.1)[a.2.1][i]).child tyVal

/-- The type `Tₗ` of a child -/
def target (a : cs.Shape tyVal) (b : cs.Child tyVal a) : Fin k := ((cs a.1)[a.2.1][b.1]).target tyVal b.2

abbrev Tree := W (cs.Shape tyVal) (cs.Child tyVal)

/-- `t` is a well-typed element of `Tⱼ` -/
def WT : cs.Tree tyVal → Fin k → Prop
| .mk a f, j => a.1 = j ∧ ∀ b, WT (f b) (cs.target tyVal a b)

theorem WT_mk {a : cs.Shape tyVal} {f : cs.Child tyVal a → cs.Tree tyVal} :
  cs.WT tyVal (.mk a f) j ↔ a.1 = j ∧ ∀ b, cs.WT tyVal (f b) (cs.target tyVal a b) := Iff.rfl

/-- The interpretation of `Tⱼ` -/
def T (j : Fin k) := { t : cs.Tree tyVal // cs.WT tyVal t j }

end IndSig

namespace IndArg

variable (tyVal : TyVal.{u}) (cs : IndSig k)

/-- The children of the node for the argument `x` with value `v` -/
def children : (x : IndArg k) → x.type tyVal (cs.T tyVal) → x.child tyVal → cs.Tree tyVal
| plain _, _, e => e.elim
| recur _ _, v, xs => (HList.uncurry v xs).val

theorem wt_children : (x : IndArg k) → (v : x.type tyVal (cs.T tyVal)) → (b : x.child tyVal) →
  cs.WT tyVal (x.children tyVal cs v b) (x.target tyVal b)
| plain _, _, e => e.elim
| recur _ _, v, xs => (HList.uncurry v xs).property

/-- The part of the argument `x` with value `v` stored in the label of the node -/
def toShape : (x : IndArg k) → x.type tyVal (cs.T tyVal) → x.shape tyVal
| plain _, v => v
| recur _ _, _ => ⟨⟩

/-- The value of the argument `x` with the given label and children -/
def ofShapeChildren : (x : IndArg k) → x.shape tyVal → (f : x.child tyVal → cs.Tree tyVal) →
  (∀ b, cs.WT tyVal (f b) (x.target tyVal b)) → x.type tyVal (cs.T tyVal)
| plain _, s, _, _ => s
| recur bs _, _, f, hf => HList.curry fun (xs : HList (LamSort.interp tyVal) bs) => ⟨f xs, hf xs⟩

theorem eq_of_toShape_children : (x : IndArg k) → {v w : x.type tyVal (cs.T tyVal)} →
  x.toShape tyVal cs v = x.toShape tyVal cs w → (∀ b, x.children tyVal cs v b = x.children tyVal cs w b) → v = w
| plain _, _, _, hs, _ => hs
| recur _ _, _, _, _, hc => HList.uncurry_inj (funext fun xs => Subtype.ext (hc xs))

theorem toShape_ofShapeChildren : (x : IndArg k) → (s : x.shape tyVal) → (f : x.child tyVal → cs.Tree tyVal) →
  (hf : ∀ b, cs.WT tyVal (f b) (x.target tyVal b)) → x.toShape tyVal cs (x.ofShapeChildren tyVal cs s f hf) = s
| plain _, _, _, _ => rfl
| recur _ _, ⟨⟩, _, _ => rfl

theorem children_ofShapeChildren : (x : IndArg k) → (s : x.shape tyVal) → (f : x.child tyVal → cs.Tree tyVal) →
  (hf : ∀ b, cs.WT tyVal (f b) (x.target tyVal b)) → x.children tyVal cs (x.ofShapeChildren tyVal cs s f hf) = f
| plain _, _, _, _ => funext fun e => e.elim
| recur _ _, _, _, _ => funext fun xs => congrArg Subtype.val (congrFun (HList.uncurry_curry _) xs)

theorem ofShapeChildren_toShape_children : (x : IndArg k) → (v : x.type tyVal (cs.T tyVal)) →
  (h : ∀ b, cs.WT tyVal (x.children tyVal cs v b) (x.target tyVal b)) →
  x.ofShapeChildren tyVal cs (x.toShape tyVal cs v) (x.children tyVal cs v) h = v
| plain _, _, _ => rfl
| recur _ _, v, _ => HList.curry_uncurry v

theorem foldArg_toShape {A : Fin k → Type u} (g : ∀ l, cs.T tyVal l → A l) : (x : IndArg k) →
  (v : x.type tyVal (cs.T tyVal)) → (rec : (b : x.child tyVal) → A (x.target tyVal b)) →
  (∀ b, rec b = g (x.target tyVal b) ⟨x.children tyVal cs v b, x.wt_children tyVal cs v b⟩) →
  x.foldArg tyVal (x.toShape tyVal cs v) rec = x.fmap tyVal g v
| plain _, _, _, _ => rfl
| recur _ _, _, _, h => congrArg HList.curry (funext h)

theorem IH_ofShapeChildren (P : (j : Fin k) → cs.T tyVal j → Prop) : (x : IndArg k) → (s : x.shape tyVal) →
  (f : x.child tyVal → cs.Tree tyVal) → (hf : ∀ b, cs.WT tyVal (f b) (x.target tyVal b)) →
  (∀ b, P (x.target tyVal b) ⟨f b, hf b⟩) → x.IH tyVal P (x.ofShapeChildren tyVal cs s f hf)
| plain _, _, _, _, _ => True.intro
| recur _ _, _, _, _, h => fun xs => (congrArg (P _) (congrFun (HList.uncurry_curry _) xs)).mpr (h xs)

end IndArg

namespace IndSig

variable (tyVal : TyVal.{u}) (cs : IndSig k)

/-- The arguments of the constructor `c` of `Tⱼ` -/
abbrev Args (j : Fin k) (c : Fin (cs j).length) := HList (IndArg.type tyVal (cs.T tyVal)) (cs j)[c]

/-- The element of `Tⱼ` built by the constructor `c` from the arguments `xs` -/
def mkVal (j : Fin k) (c : Fin (cs j).length) (xs : cs.Args tyVal j c) : cs.T tyVal j :=
  ⟨.mk ⟨j, c, xs.map (IndArg.toShape tyVal cs)⟩ (fun b => IndArg.children tyVal cs _ (xs.get b.1) b.2),
   (cs.WT_mk tyVal).mpr ⟨rfl, fun b => IndArg.wt_children tyVal cs _ _ b.2⟩⟩

/-- The constructor `c` of `Tⱼ`, as a curried function -/
def ctor (j : Fin k) (c : Fin (cs j).length) : HList.Funcs (IndArg.type tyVal (cs.T tyVal)) (cs j)[c] (cs.T tyVal j) :=
  HList.curry (cs.mkVal tyVal j c)

theorem mk_congr {j : Fin k} {c : Fin (cs j).length} {s₁ s₂ : HList (IndArg.shape tyVal) (cs j)[c]} (hs : s₁ = s₂)
  {f₁ : cs.Child tyVal ⟨j, c, s₁⟩ → cs.Tree tyVal} {f₂ : cs.Child tyVal ⟨j, c, s₂⟩ → cs.Tree tyVal}
  (hf : ∀ b, f₁ b = f₂ b) : (W.mk ⟨j, c, s₁⟩ f₁ : cs.Tree tyVal) = W.mk ⟨j, c, s₂⟩ f₂ := by
  subst hs; rw [funext hf]

/-- The arguments of the element `.mk a f` of a type, which is built by the constructor `a.2.1` of `T a.1` -/
def argsOf (a : cs.Shape tyVal) (f : cs.Child tyVal a → cs.Tree tyVal)
  (hf : ∀ b, cs.WT tyVal (f b) (cs.target tyVal a b)) : cs.Args tyVal a.1 a.2.1 :=
  HList.ofFn fun i => IndArg.ofShapeChildren tyVal cs _ (a.2.2.get i) (fun b => f ⟨i, b⟩) (fun b => hf ⟨i, b⟩)

theorem mkVal_argsOf (a : cs.Shape tyVal) (f : cs.Child tyVal a → cs.Tree tyVal)
  (hf : ∀ b, cs.WT tyVal (f b) (cs.target tyVal a b)) :
  (cs.mkVal tyVal a.1 a.2.1 (cs.argsOf tyVal a f hf)).val = .mk a f := by
  cases a with
  | mk j cs' =>
    cases cs' with
    | mk c s =>
      apply mk_congr
      · apply HList.ext; intro i
        dsimp only [argsOf]
        rw [HList.get_map, HList.get_ofFn]
        exact IndArg.toShape_ofShapeChildren tyVal cs _ _ _ _
      · intro ⟨i, b⟩
        show IndArg.children tyVal cs _ ((cs.argsOf tyVal ⟨j, c, s⟩ f hf).get i) b = f ⟨i, b⟩
        dsimp only [argsOf]
        rw [HList.get_ofFn]
        exact congrFun (IndArg.children_ofShapeChildren tyVal cs _ _ _ _) b

/-- Different constructors of the same type build different elements -/
theorem mkVal_ne {j : Fin k} {c₁ c₂ : Fin (cs j).length} (h : c₁ ≠ c₂) (xs : cs.Args tyVal j c₁)
  (ys : cs.Args tyVal j c₂) : cs.mkVal tyVal j c₁ xs ≠ cs.mkVal tyVal j c₂ ys := by
  intro heq
  have heq := congrArg Subtype.val heq
  injection heq with heq _
  exact h (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj heq).right)).left

/-- The constructors are injective -/
theorem mkVal_inj {j : Fin k} {c : Fin (cs j).length} {xs ys : cs.Args tyVal j c}
  (heq : cs.mkVal tyVal j c xs = cs.mkVal tyVal j c ys) : xs = ys := by
  have heq := congrArg Subtype.val heq
  injection heq with hs hc
  have hs := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hs).right)).right
  apply HList.ext; intro i
  apply IndArg.eq_of_toShape_children tyVal cs
  · have := congrArg (fun s => HList.get s i) hs
    simpa only [HList.get_map] using this
  · intro b; exact congrFun hc ⟨i, b⟩

/--
  Induction over `T₀ ⋯ Tₖ₋₁`, with induction hypotheses for all the recursive arguments
    of the constructors, including the arguments of sort `B₁ → ⋯ → Bₘ → Tₗ`
-/
theorem induction (P : (j : Fin k) → cs.T tyVal j → Prop)
  (H : ∀ (j : Fin k) (c : Fin (cs j).length) (xs : cs.Args tyVal j c),
    (∀ i, IndArg.IH tyVal P (cs j)[c][i] (xs.get i)) → P j (cs.mkVal tyVal j c xs)) :
  ∀ j (t : cs.T tyVal j), P j t := by
  intro j ⟨t, ht⟩
  induction t generalizing j with
  | mk a f IH =>
    obtain ⟨hj, hf⟩ := (cs.WT_mk tyVal).mp ht
    subst hj
    have key := H a.1 a.2.1 (cs.argsOf tyVal a f hf) fun i => by
      dsimp only [argsOf]; rw [HList.get_ofFn]
      exact IndArg.IH_ofShapeChildren tyVal cs P _ _ _ _ fun b => IH ⟨i, b⟩ _ (hf ⟨i, b⟩)
    have heq : cs.mkVal tyVal a.1 a.2.1 (cs.argsOf tyVal a f hf) = ⟨.mk a f, ht⟩ :=
      Subtype.ext (cs.mkVal_argsOf tyVal a f hf)
    rwa [heq] at key

/-- The `i`-th argument of the elements of `Tⱼ`, whose only constructor is `c` -/
def proj (j : Fin k) (c : Fin (cs j).length) (hc : ∀ c', c' = c) (i : Fin (cs j)[c].length) :
  cs.T tyVal j → IndArg.type tyVal (cs.T tyVal) (cs j)[c][i]
| ⟨.mk a f, ht⟩ =>
  match a, f, ht, ((cs.WT_mk tyVal).mp ht).1 with
  | ⟨_, c', s⟩, f, ht, rfl =>
    match c', s, f, ht, hc c' with
    | _, s, f, ht, rfl => (cs.argsOf tyVal ⟨j, c, s⟩ f ((cs.WT_mk tyVal).mp ht).2).get i

theorem proj_mkVal (j : Fin k) (c : Fin (cs j).length) (hc : ∀ c', c' = c) (i : Fin (cs j)[c].length)
  (xs : cs.Args tyVal j c) : cs.proj tyVal j c hc i (cs.mkVal tyVal j c xs) = xs.get i := by
  let a : cs.Shape tyVal := ⟨j, c, xs.map (IndArg.toShape tyVal cs)⟩
  let f : cs.Child tyVal a → cs.Tree tyVal := fun b => IndArg.children tyVal cs _ (xs.get b.1) b.2
  have h : ∀ hf : (∀ b, cs.WT tyVal (f b) (cs.target tyVal a b)), (cs.argsOf tyVal a f hf).get i = xs.get i := by
    intro hf
    dsimp only [argsOf, a, f]
    rw [HList.get_ofFn, HList.get_map]
    exact IndArg.ofShapeChildren_toShape_children tyVal cs _ _ _
  exact h _

/-- The values in `A` of the well-typed trees, where `alg` interprets the constructors -/
def foldTree (A : Fin k → Type u) (alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j) :
  (t : cs.Tree tyVal) → (j : Fin k) → cs.WT tyVal t j → A j
| .mk a f, _, ht =>
  ((cs.WT_mk tyVal).mp ht).1 ▸ alg a.1 a.2.1 (HList.ofFn fun i =>
    IndArg.foldArg tyVal _ (a.2.2.get i) fun b => foldTree A alg (f ⟨i, b⟩) _ (((cs.WT_mk tyVal).mp ht).2 ⟨i, b⟩))

/-- The unique homomorphism from `T` to `A`, where `alg` interprets the constructors -/
def fold (A : Fin k → Type u) (alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j)
  (j : Fin k) (t : cs.T tyVal j) : A j := cs.foldTree tyVal A alg t.1 j t.2

theorem fold_mkVal (A : Fin k → Type u) (alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j)
  (j : Fin k) (c : Fin (cs j).length) (xs : cs.Args tyVal j c) :
  cs.fold tyVal A alg j (cs.mkVal tyVal j c xs) = alg j c (xs.map (IndArg.fmap tyVal (cs.fold tyVal A alg))) := by
  show alg j c _ = _
  apply congrArg; apply HList.ext; intro i
  simp only [HList.get_ofFn, HList.get_map]
  exact IndArg.foldArg_toShape tyVal cs (cs.fold tyVal A alg) _ _ _ fun _ => rfl

theorem eq_mkVal (j : Fin k) (t : cs.T tyVal j) : ∃ c xs, t = cs.mkVal tyVal j c xs :=
  cs.induction tyVal (fun j t => ∃ c xs, t = cs.mkVal tyVal j c xs) (fun _ c xs _ => ⟨c, xs, rfl⟩) j t

/--
  `alg` interprets the constructors of `cs` as the constructors of the mutual inductive types `A`:
    they are distinct and injective, and induction holds
-/
structure IsInductive (A : Fin k → Type u)
  (alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j) : Prop where
  distinct : ∀ j (c₁ c₂ : Fin (cs j).length), c₁ ≠ c₂ → ∀ xs ys, alg j c₁ xs ≠ alg j c₂ ys
  inject : ∀ j c xs ys, alg j c xs = alg j c ys → xs = ys
  induction : ∀ (P : (j : Fin k) → A j → Prop),
    (∀ j c xs, (∀ i, IndArg.IH tyVal P (cs j)[c][i] (xs.get i)) → P j (alg j c xs)) → ∀ j a, P j a

theorem fold_injective {A : Fin k → Type u} {alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j}
  (h : cs.IsInductive tyVal A alg) : ∀ j (t t' : cs.T tyVal j), cs.fold tyVal A alg j t = cs.fold tyVal A alg j t' → t = t' := by
  apply cs.induction tyVal (fun j t => ∀ t', cs.fold tyVal A alg j t = cs.fold tyVal A alg j t' → t = t')
  intro j c xs ih t' heq
  obtain ⟨c', ys, rfl⟩ := cs.eq_mkVal tyVal j t'
  rw [fold_mkVal, fold_mkVal] at heq
  by_cases hc : c = c'
  · subst hc
    have hmap := h.inject j c _ _ heq
    apply congrArg; apply HList.ext; intro i
    have hi := congrArg (fun zs => HList.get zs i) hmap
    simp only [HList.get_map] at hi
    exact IndArg.eq_of_fmap_eq tyVal _ _ _ (ih i) hi
  · exact absurd heq (h.distinct j c c' hc _ _)

theorem fold_surjective {A : Fin k → Type u} {alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j}
  (h : cs.IsInductive tyVal A alg) : ∀ j (a : A j), ∃ t, cs.fold tyVal A alg j t = a := by
  apply h.induction (fun j a => ∃ t, cs.fold tyVal A alg j t = a)
  intro j c xs ih
  have hex := fun i => IndArg.exists_fmap_eq tyVal (cs.fold tyVal A alg) _ (xs.get i) (ih i)
  refine ⟨cs.mkVal tyVal j c (HList.ofFn fun i => Classical.choose (hex i)), ?_⟩
  rw [fold_mkVal]; apply congrArg; apply HList.ext; intro i
  rw [HList.get_map, HList.get_ofFn]
  exact Classical.choose_spec (hex i)

/-- Mutual inductive types `A` with the signature `cs` are isomorphic to `T` -/
theorem exists_isomType {A : Fin k → Type u} {alg : ∀ j (c : Fin (cs j).length), HList (IndArg.type tyVal A) (cs j)[c] → A j}
  (h : cs.IsInductive tyVal A alg) :
  ∃ (φ : ∀ j, IsomType (cs.T tyVal j) (A j)), ∀ j, (φ j).f = cs.fold tyVal A alg j :=
  ⟨fun j => ⟨cs.fold tyVal A alg j, fun a => Classical.choose (cs.fold_surjective tyVal h j a),
    fun _ => cs.fold_injective tyVal h j _ _ (Classical.choose_spec (cs.fold_surjective tyVal h j _)),
    fun a => Classical.choose_spec (cs.fold_surjective tyVal h j a)⟩, fun _ => rfl⟩

end IndSig

/--
  The argument of sort `s` of a constructor of `mind`: `.plain s` if `s` does not mention the types
    of `mind`, and `.recur [B₁, ⋯, Bₘ] l` if `s` is `B₁ → ⋯ → Bₘ → Tₗ`, where `B₁ ⋯ Bₘ` do not
    mention the types of `mind`
-/
def MutualIndInfo.indArg? (mind : MutualIndInfo) (s : LamSort) : Option (IndArg mind.length) :=
  let tys := mind.map (·.type)
  let isInd (s : LamSort) : Bool := tys.any s.contains
  if !isInd s then
    .some (.plain s)
  else if s.getArgTys.any isInd then
    .none
  else
    ((tys.findFinIdx? (· == s.getResTy)).map (Fin.cast (List.length_map _))).map (.recur s.getArgTys)

/-- The arguments of the constructors of `mind[j]` -/
def MutualIndInfo.ctorArgs? (mind : MutualIndInfo) (j : Fin mind.length) : Option (List (List (IndArg mind.length))) :=
  mind[j].ctors.mapM fun (s, _) => if s.getResTy != mind[j].type then .none else s.getArgTys.mapM mind.indArg?

/--
  The simple mutual inductive types described by `mind`. The sort of each argument of a
    constructor should either not mention the types of `mind`, or be `B₁ → ⋯ → Bₘ → Tₗ`,
    where `B₁ ⋯ Bₘ` do not mention the types of `mind`
-/
def MutualIndInfo.toIndSig? (mind : MutualIndInfo) : Option (IndSig mind.length) :=
  if h : (List.finRange mind.length).all fun j => (mind.ctorArgs? j).isSome then
    .some fun j => (mind.ctorArgs? j).get (List.all_eq_true.mp h j (List.mem_finRange j))
  else
    .none

theorem MutualIndInfo.toIndSig?_ctorArgs? {mind : MutualIndInfo} {cs : IndSig mind.length} (hcs : mind.toIndSig? = .some cs)
  (j : Fin mind.length) : mind.ctorArgs? j = .some (cs j) := by
  unfold toIndSig? at hcs
  split at hcs
  case isTrue => cases hcs; exact (Option.some_get _).symm
  case isFalse => cases hcs

theorem MutualIndInfo.toIndSig?_ctors_length {mind : MutualIndInfo} {cs : IndSig mind.length} (hcs : mind.toIndSig? = .some cs)
  (j : Fin mind.length) : (cs j).length = mind[j].ctors.length :=
  (List.mapM_option_eq_some (MutualIndInfo.toIndSig?_ctorArgs? hcs j)).1

theorem MutualIndInfo.toIndSig?_ctor {mind : MutualIndInfo} {cs : IndSig mind.length} (hcs : mind.toIndSig? = .some cs)
  (j : Fin mind.length) (c : Fin (cs j).length) :
  (mind[j].ctors[c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j)]).1.getResTy = mind[j].type ∧
    (mind[j].argTys (c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j))).mapM mind.indArg? = .some (cs j)[c] := by
  obtain ⟨_, hall⟩ := List.mapM_option_eq_some (MutualIndInfo.toIndSig?_ctorArgs? hcs j)
  have h := hall c.val c.isLt
  simp only [IndInfo.argTys, Fin.getElem_fin, Fin.val_cast]
  generalize mind[j].ctors[c.val] = p at h ⊢
  obtain ⟨s, t⟩ := p
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i hres
    rw [bne_iff_ne, ne_eq, Classical.not_not] at hres
    exact ⟨hres, h⟩

theorem MutualIndInfo.toIndSig?_args_length {mind : MutualIndInfo} {cs : IndSig mind.length} (hcs : mind.toIndSig? = .some cs)
  (j : Fin mind.length) (c : Fin (cs j).length) :
  (cs j)[c].length = (mind[j].argTys (c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j))).length :=
  (List.mapM_option_eq_some (MutualIndInfo.toIndSig?_ctor hcs j c).2).1

theorem MutualIndInfo.toIndSig?_indArg? {mind : MutualIndInfo} {cs : IndSig mind.length} (hcs : mind.toIndSig? = .some cs)
  (j : Fin mind.length) (c : Fin (cs j).length) (i : Fin (mind[j].argTys (c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j))).length) :
  mind.indArg? (mind[j].argTys (c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j)))[i] =
    .some (cs j)[c][i.cast (MutualIndInfo.toIndSig?_args_length hcs j c).symm] :=
  (List.mapM_option_eq_some (MutualIndInfo.toIndSig?_ctor hcs j c).2).2 i.val
    (by rw [MutualIndInfo.toIndSig?_args_length hcs j c]; exact i.isLt)

theorem MutualIndInfo.indArg?_plain {mind : MutualIndInfo} (h : mind.indArg? s = .some (.plain s')) : s' = s := by
  unfold indArg? at h; dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h; cases h

theorem MutualIndInfo.indArg?_recur {mind : MutualIndInfo} {l : Fin mind.length}
  (h : mind.indArg? s = .some (.recur bs l)) :
  bs = s.getArgTys ∧ mind[l].type = s.getResTy ∧ mind.recArg? s = .some l.val := by
  unfold indArg? at h; dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hargs
      obtain ⟨l', hl', h⟩ := Option.map_eq_some_iff.mp h
      cases h
      obtain ⟨l'', hl'', rfl⟩ := Option.map_eq_some_iff.mp hl'
      obtain ⟨hp, _⟩ := List.findFinIdx?_eq_some_iff.mp hl''
      refine ⟨rfl, by simpa using hp, ?_⟩
      unfold recArg?; dsimp only
      simp only [hargs, Bool.false_eq_true, ↓reduceIte]
      rw [List.findIdx?_eq_map_findFinIdx?_val, hl'']; rfl

theorem MutualIndInfo.indArg?_type {tyVal : TyVal.{u}} {mind : MutualIndInfo} {x : IndArg mind.length}
  (h : mind.indArg? s = .some x) : x.type tyVal (fun l => mind[l].type.interp tyVal) = s.interp tyVal := by
  cases x with
  | plain s' => cases mind.indArg?_plain h; rfl
  | recur bs l =>
    obtain ⟨rfl, hty, _⟩ := mind.indArg?_recur h
    show HList.Funcs _ _ _ = _
    rw [← LamSort.interp_mkFuncs, hty, LamSort.getArgTys_getResTy_eq]

theorem MutualIndInfo.toIndSig?_argType {tyVal : TyVal.{u}} {mind : MutualIndInfo} {cs : IndSig mind.length}
  (hcs : mind.toIndSig? = .some cs) (j : Fin mind.length) (c : Fin (cs j).length)
  (i : Fin (mind[j].argTys (c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j))).length) :
  IndArg.type tyVal (fun l => mind[l].type.interp tyVal) (cs j)[c][i.cast (MutualIndInfo.toIndSig?_args_length hcs j c).symm] =
    (mind[j].argTys (c.cast (MutualIndInfo.toIndSig?_ctors_length hcs j)))[i].interp tyVal :=
  indArg?_type (toIndSig?_indArg? hcs j c i)

/--
  The interpretation of the constructors of `mind` in the context `lctx`, as functions on the
    arguments of the constructors of `cs`, whose recursive arguments are in the types of `mind`
-/
noncomputable def MutualIndInfo.ctorAlg (lval : LamValuation.{u}) {mind : MutualIndInfo} {cs : IndSig mind.length}
  (hcs : mind.toIndSig? = .some cs) (lctx : Nat → LamSort) (lctxTerm : ∀ n, (lctx n).interp lval.tyVal)
  (wf : ∀ (j : Fin mind.length) (c : Fin mind[j].ctors.length), mind[j].CtorWF lval.toLamTyVal lctx c)
  (j : Fin mind.length) (c : Fin (cs j).length)
  (xs : HList (IndArg.type lval.tyVal fun l => mind[l].type.interp lval.tyVal) (cs j)[c]) :
  mind[j].type.interp lval.tyVal :=
  LamSort.uncurry ((wf j (c.cast (toIndSig?_ctors_length hcs j))).interp lval lctx lctxTerm)
    (HList.recast (toIndSig?_args_length hcs j c) (toIndSig?_argType hcs j c) xs)

theorem MutualIndInfo.IH_of_semIH {tyVal : TyVal.{u}} {mind : MutualIndInfo}
  {P : (j : Fin mind.length) → mind[j].type.interp tyVal → Prop} {a : LamSort} :
  {x : IndArg mind.length} → mind.indArg? a = .some x →
  (v : x.type tyVal (fun l => mind[l].type.interp tyVal)) → (vL : a.interp tyVal) → HEq v vL →
  (∀ (l : Fin mind.length), mind.recArg? a = .some l.val →
    ∀ (f : (LamSort.mkFuncs mind[l].type a.getArgTys).interp tyVal), HEq f vL → ∀ ys, P l (LamSort.uncurry f ys)) →
  x.IH tyVal P v
  | .plain _, _, _, _, _, _ => True.intro
  | .recur _ l, hx, v, _, hv, hsem => by
    obtain ⟨rfl, _, hrec⟩ := mind.indArg?_recur hx
    intro ys
    have h := hsem l hrec (cast LamSort.interp_mkFuncs.symm v) ((cast_heq _ _).trans hv) ys
    have huncurry : LamSort.uncurry (cast LamSort.interp_mkFuncs.symm v) ys =
      HList.uncurry (γ := mind[l].type.interp tyVal) v ys := LamSort.uncurry_eq_uncurry (cast_heq _ _) ys
    rw [huncurry] at h; exact h

theorem MutualIndInfo.ctorAlg_isInductive {lval : LamValuation.{u}} {mind : MutualIndInfo} {cs : IndSig mind.length}
  (hspec : mind.SemSpec lval) (hcs : mind.toIndSig? = .some cs) (lctx : Nat → LamSort)
  (lctxTerm : ∀ n, (lctx n).interp lval.tyVal)
  (wf : ∀ (j : Fin mind.length) (c : Fin mind[j].ctors.length), mind[j].CtorWF lval.toLamTyVal lctx c) :
  cs.IsInductive lval.tyVal (fun l => mind[l].type.interp lval.tyVal) (mind.ctorAlg lval hcs lctx lctxTerm wf) where
  distinct j c₁ c₂ hne _ _ := hspec.distinct lctx lctxTerm j _ _
    (fun h => hne (Fin.ext (by simpa using congrArg Fin.val h))) _ _ _ _
  inject _ _ _ _ heq := HList.recast_inj (hspec.inject lctx lctxTerm _ _ _ _ _ heq)
  induction P H := by
    apply hspec.induction lctx lctxTerm P
    intro j c' wf' xsL hih
    let c : Fin (cs j).length := c'.cast (toIndSig?_ctors_length hcs j).symm
    obtain ⟨xs, hxs⟩ := HList.exists_recast_eq (toIndSig?_args_length hcs j c) (toIndSig?_argType hcs j c) xsL
    have heq : mind.ctorAlg lval hcs lctx lctxTerm wf j c xs = LamSort.uncurry (wf'.interp lval lctx lctxTerm) xsL := by
      unfold ctorAlg; rw [hxs]; exact congrArg (LamSort.uncurry · xsL) LamWF.interp_substWF
    refine heq ▸ H j c xs fun i => ?_
    apply IH_of_semIH (toIndSig?_indArg? hcs j c (i.cast (toIndSig?_args_length hcs j c))) (xs.get i)
      (xsL.get (i.cast (toIndSig?_args_length hcs j c))) ?_ (hih _)
    rw [← hxs, HList.get_recast]; exact (cast_heq _ _).symm

/--
  If `mind` satisfies its spec, then its types are isomorphic to the types of the W type model `cs`
    of `mind`, and the isomorphisms commute with the constructors
-/
theorem MutualIndInfo.isomType_of_spec {lval : LamValuation.{u}} {mind : MutualIndInfo} {cs : IndSig mind.length}
  (hspec : mind.Spec lval) (hcs : mind.toIndSig? = .some cs) (lctx : Nat → LamSort)
  (lctxTerm : ∀ n, (lctx n).interp lval.tyVal)
  (wf : ∀ (j : Fin mind.length) (c : Fin mind[j].ctors.length), mind[j].CtorWF lval.toLamTyVal lctx c) :
  ∃ (φ : ∀ j, IsomType (cs.T lval.tyVal j) (mind[j].type.interp lval.tyVal)),
    ∀ j c xs, (φ j).f (cs.mkVal lval.tyVal j c xs) =
      mind.ctorAlg lval hcs lctx lctxTerm wf j c (xs.map (IndArg.fmap lval.tyVal fun l => (φ l).f)) := by
  obtain ⟨φ, hφ⟩ := cs.exists_isomType lval.tyVal (ctorAlg_isInductive (spec_iff_semSpec.mp hspec) hcs lctx lctxTerm wf)
  refine ⟨φ, fun j c xs => ?_⟩
  rw [show (fun l => (φ l).f) = cs.fold lval.tyVal _ (mind.ctorAlg lval hcs lctx lctxTerm wf) from funext hφ, hφ]
  exact cs.fold_mkVal lval.tyVal _ _ j c xs

end Auto.Embedding.Lam

namespace Auto

open Embedding.Lam

/--
  The characterization of an inductive type (see `IndInfo.specTerms`), by kind.
    This is used when `lean-auto` sends facts to provers, e.g. in `NativeInterface`
-/
structure IndTypeSpec (α : Type u) where
  /-- Different constructors produce different values (see `IndInfo.distinctTerms`) -/
  distinct : Array α := #[]
  /-- The constructors are injective (see `IndInfo.injectTerms`) -/
  inject   : Array α := #[]
  /-- The projections of a structure project the arguments of its constructor (see `IndInfo.projTerms`) -/
  proj     : Array α := #[]

/--
  The characterization of a mutual block of inductive types, which is one fact in the
    verified checker (see `IndBlockSpec.toLamTerm`). This is used when `lean-auto` sends
    facts to provers, e.g. in `NativeInterface`
-/
structure IndBlockSpec (α : Type u) where
  /--
    The characterizations of the types of the block. The types nested in them (e.g.
      `List Tr` for `inductive Tr | node : List Tr → Tr`) are characterized in their own blocks
  -/
  types     : Array (IndTypeSpec α)
  /-- Induction over the types of the block and the types nested in them (see `MutualIndInfo.inductionTerm`) -/
  induction : α

def IndTypeSpec.toArray (ts : IndTypeSpec α) : Array α := ts.distinct ++ ts.inject ++ ts.proj

def IndTypeSpec.mapM {m : Type u → Type v} [Monad m] (f : α → m β) (ts : IndTypeSpec α) : m (IndTypeSpec β) := do
  return { distinct := ← ts.distinct.mapM f, inject := ← ts.inject.mapM f, proj := ← ts.proj.mapM f }

/-- All the characterizations in `bs`, in the order of the conjuncts of `IndBlockSpec.toLamTerm` -/
def IndBlockSpec.toArray (bs : IndBlockSpec α) : Array α :=
  (bs.types.flatMap IndTypeSpec.toArray).push bs.induction

def IndBlockSpec.mapM {m : Type u → Type v} [Monad m] (f : α → m β) (bs : IndBlockSpec α) : m (IndBlockSpec β) := do
  return { types := ← bs.types.mapM (·.mapM f), induction := ← f bs.induction }

def IndBlockSpec.map (f : α → β) (bs : IndBlockSpec α) : IndBlockSpec β :=
  Id.run (bs.mapM (pure ∘ f))

/-- `bs` with its characterizations replaced by `as`, in the order of `IndBlockSpec.toArray` -/
def IndBlockSpec.replace? (bs : IndBlockSpec α) (as : Array β) : Option (IndBlockSpec β) :=
  if bs.toArray.size != as.size then
    .none
  else
    (bs.mapM (m := StateT Nat Option) fun _ => do
      let i ← get
      set (i + 1)
      as[i]?).run' 0

/-- The conjunction of the characterizations in `bs`, which is one fact in the verified checker -/
def IndBlockSpec.toLamTerm (bs : IndBlockSpec LamTerm) : LamTerm := LamTerm.mkAndN bs.toArray.toList

/-- The characterization of the mutual block `mind`, whose first `n` types are the types of the block -/
def IndBlockSpec.ofMutualIndInfo (mind : MutualIndInfo) (n : Nat) : IndBlockSpec LamTerm where
  types := (mind.take n).toArray.map fun ii =>
    { distinct := ii.distinctTerms.toArray, inject := ii.injectTerms.toArray, proj := ii.projTerms.toArray }
  induction := mind.inductionTerm

end Auto
