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

/-! Characterization of mutual inductive types -/

/--
  `t x₁ ⋯ xₙ`, where `ss = [s₁, ⋯, sₙ]` are the sorts of the arguments,
    and `xᵢ` is `.bvar (off + n - i)`
-/
def LamTerm.mkAppBVars (t : LamTerm) (ss : List LamSort) (off : Nat) : LamTerm :=
  t.mkAppN (ss.zipIdx.map fun (s, i) => (s, .bvar (off + ss.length - 1 - i)))

/-- `∀ x₁ ⋯ xₙ y₁ ⋯ yₘ, ¬ (c₁ x₁ ⋯ xₙ = c₂ y₁ ⋯ yₘ)`, where `c₁ c₂` are constructors of `ty` -/
def IndInfo.distinctTerm (ty : LamSort) (c₁ c₂ : LamSort × LamTerm) : LamTerm :=
  let (s₁, t₁) := c₁
  let (s₂, t₂) := c₂
  let as₁ := s₁.getArgTys
  let as₂ := s₂.getArgTys
  let n := as₁.length + as₂.length
  LamTerm.mkForallEFN (.mkNot (.mkEq ty
    ((t₁.bvarLifts n).mkAppBVars as₁ as₂.length) ((t₂.bvarLifts n).mkAppBVars as₂ 0))) (as₁ ++ as₂)

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
    let t := t.bvarLifts (2 * n)
    let eqs := as.zipIdx.map fun (a, i) => LamTerm.mkEq a (.bvar (2 * n - 1 - i)) (.bvar (n - 1 - i))
    .some (LamTerm.mkForallEFN (.mkImp (.mkEq ty (t.mkAppBVars as n) (t.mkAppBVars as 0)) (.mkAndN eqs)) (as ++ as))

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
      let c := (c.bvarLifts n).mkAppBVars as 0
      (projs.zip as).zipIdx.map fun (((_, proj), a), i) =>
        LamTerm.mkForallEFN (.mkEq a (.app ii.type (proj.bvarLifts n) c) (.bvar (n - 1 - i))) as
  | _, _ => []

/--
  Induction over the mutual inductive types `T₁ ⋯ Tₖ` of `mind`:
    `∀ (P₁ : T₁ → Prop) ⋯ (Pₖ : Tₖ → Prop), H₁ → ⋯ → Hₘ → (∀ t, P₁ t) ∧ ⋯ ∧ (∀ t, Pₖ t)`,
  with one hypothesis `∀ x₁ ⋯ xₙ, IH₁ → ⋯ → IHᵣ → Pⱼ (c x₁ ⋯ xₙ)` for each constructor
    `c : A₁ → ⋯ → Aₙ → Tⱼ`. The induction hypotheses are `∀ b₁ ⋯ bₘ, Pₗ (xᵢ b₁ ⋯ bₘ)`
    for the arguments `xᵢ : B₁ → ⋯ → Bₘ → Tₗ` such that `B₁ ⋯ Bₘ` do not mention the
    types of `mind` (which is `Pₗ xᵢ` if `m = 0`), as in `IndSig.induction`
-/
def MutualIndInfo.inductionTerm (mind : MutualIndInfo) : LamTerm :=
  let tys := mind.map (·.type)
  let k := tys.length
  -- `Pⱼ₊₁` under `off` binders, inside the binders of `P₁ ⋯ Pₖ`
  let p (j off : Nat) := LamTerm.bvar (off + k - 1 - j)
  let hyps := mind.zipIdx.flatMap fun (ii, j) => ii.ctors.map fun (s, c) =>
    let as := s.getArgTys
    let n := as.length
    let ihs := as.zipIdx.filterMap fun (a, i) =>
      let bs := a.getArgTys
      let m := bs.length
      if bs.any fun b => tys.any b.contains then
        .none
      else
        -- `∀ b₁ ⋯ bₘ, Pₗ (xᵢ b₁ ⋯ bₘ)`
        (tys.findIdx? (· == a.getResTy)).map fun l => LamTerm.mkForallEFN
          (.app a.getResTy (p l (n + m)) ((LamTerm.bvar (m + n - 1 - i)).mkAppBVars bs 0)) bs
    LamTerm.mkForallEFN (.mkImpN ihs (.app ii.type (p j n) ((c.bvarLifts (k + n)).mkAppBVars as 0))) as
  let concl := LamTerm.mkAndN (mind.zipIdx.map fun (ii, j) => .mkForallEF ii.type (.app ii.type (p j 1) (.bvar 0)))
  LamTerm.mkForallEFN (.mkImpN hyps concl) (tys.map (.func · (.base .prop)))

/-- The characterization of the mutual inductive types `mind` (see `MutualIndInfo.Spec`) -/
def MutualIndInfo.specTerms (mind : MutualIndInfo) : List LamTerm :=
  mind.flatMap (fun ii => ii.distinctTerms ++ ii.injectTerms ++ ii.projTerms) ++ [mind.inductionTerm]

/--
  `lval` interprets `mind` as mutual inductive types:
  · Different constructors of the same type produce different values
  · The constructors are injective
  · The projections of structures project the arguments of the constructors
  · Induction over the types of `mind`
  For simple mutual inductive types, these characterize the types of `mind` up to isomorphism,
    given the interpretations of the other sorts of the arguments of the constructors.
  Arguments whose sorts mention the types of `mind` only in other sorts (e.g. `List T`, if
    `List T` is not a type of `mind`) have no induction hypotheses, so the characterization
    is weaker but still holds for such types
-/
def MutualIndInfo.Spec (lval : LamValuation) (mind : MutualIndInfo) : Prop :=
  ∀ t ∈ mind.specTerms, LamThmValid lval [] t

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

/-- `α₁ × ⋯ × αₙ`, which is `PUnit` if `n = 0` -/
def ProdList : List (Type u) → Type u
| [] => PUnit
| α :: αs => α × ProdList αs

/-- `α₁ → ⋯ → αₙ → β` -/
def FuncList : List (Type u) → Type u → Type u
| [], β => β
| α :: αs, β => α → FuncList αs β

def FuncList.uncurry : {αs : List (Type u)} → FuncList αs β → ProdList αs → β
| [], f, _ => f
| _ :: _, f, (a, as) => uncurry (f a) as

def FuncList.curry : {αs : List (Type u)} → (ProdList αs → β) → FuncList αs β
| [], f => f ⟨⟩
| _ :: _, f => fun a => curry fun as => f (a, as)

theorem FuncList.uncurry_curry : {αs : List (Type u)} → (f : ProdList αs → β) → uncurry (curry f) = f
| [], _ => funext fun ⟨⟩ => rfl
| _ :: _, f => funext fun (a, as) => congrFun (uncurry_curry (fun as => f (a, as))) as

theorem FuncList.curry_uncurry : {αs : List (Type u)} → (f : FuncList αs β) → curry (uncurry f) = f
| [], _ => rfl
| _ :: _, f => funext fun a => curry_uncurry (f a)

theorem FuncList.uncurry_inj : {αs : List (Type u)} → {f g : FuncList αs β} → uncurry f = uncurry g → f = g
| [], _, _, h => congrFun h ⟨⟩
| _ :: _, _, _, h => funext fun a => uncurry_inj (funext fun as => congrFun h (a, as))

/-- `ProdList (xs.map F) → ProdList (xs.map G)`, componentwise -/
def ProdList.map {F G : X → Type u} (f : (x : X) → F x → G x) : (xs : List X) → ProdList (xs.map F) → ProdList (xs.map G)
| [], _ => ⟨⟩
| x :: xs, (a, as) => (f x a, map f xs as)

/-- The `i`-th component of `ProdList (xs.map F)` -/
def ProdList.get {F : X → Type u} : (xs : List X) → ProdList (xs.map F) → (i : Fin xs.length) → F xs[i]
| _ :: _, (a, _), ⟨0, _⟩ => a
| _ :: xs, (_, as), ⟨i + 1, h⟩ => get xs as ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The `ProdList (xs.map F)` whose components are given by `f` -/
def ProdList.ofFn {F : X → Type u} : (xs : List X) → (f : (i : Fin xs.length) → F xs[i]) → ProdList (xs.map F)
| [], _ => ⟨⟩
| _ :: xs, f => (f ⟨0, Nat.zero_lt_succ _⟩, ofFn xs fun i => f i.succ)

theorem ProdList.get_ofFn {F : X → Type u} : (xs : List X) → (f : (i : Fin xs.length) → F xs[i]) →
  (i : Fin xs.length) → get xs (ofFn xs f) i = f i
| _ :: _, _, ⟨0, _⟩ => rfl
| _ :: xs, f, ⟨i + 1, h⟩ => get_ofFn xs (fun i => f i.succ) ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem ProdList.ext {F : X → Type u} : (xs : List X) → {as bs : ProdList (xs.map F)} →
  (∀ i, get xs as i = get xs bs i) → as = bs
| [], ⟨⟩, ⟨⟩, _ => rfl
| _ :: xs, (_, _), (_, _), h =>
  Prod.ext (h ⟨0, Nat.zero_lt_succ _⟩) (ext xs fun ⟨i, hi⟩ => h ⟨i + 1, Nat.succ_lt_succ hi⟩)

theorem ProdList.get_map {F G : X → Type u} (f : (x : X) → F x → G x) : (xs : List X) → (as : ProdList (xs.map F)) →
  (i : Fin xs.length) → get xs (map f xs as) i = f xs[i] (get xs as i)
| _ :: _, (_, _), ⟨0, _⟩ => rfl
| _ :: xs, (_, as), ⟨i + 1, h⟩ => get_map f xs as ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- An argument of a constructor of simple mutual inductive types `T₀ ⋯ Tₖ₋₁` -/
inductive IndArg (k : Nat) : Type (u + 1) where
  /-- An argument whose type `α` does not mention `T₀ ⋯ Tₖ₋₁` -/
  | plain (α : Type u)
  /-- An argument of type `β₁ → ⋯ → βₘ → Tₗ`, which is `Tₗ` if `m = 0` -/
  | recur (βs : List (Type u)) (l : Fin k)

/--
  Simple mutual inductive types `T₀ ⋯ Tₖ₋₁`, given by their constructors.
    Each constructor is given by its type `Tⱼ` and its arguments
-/
abbrev IndSig (k : Nat) : Type (u + 1) := List (Fin k × List (IndArg.{u} k))

namespace IndArg

/-- The type of the argument, given the interpretation `T` of `T₀ ⋯ Tₖ₋₁` -/
def type (T : Fin k → Type u) : IndArg.{u} k → Type u
| plain α => α
| recur βs l => FuncList βs (T l)

/-- The part of the argument stored in the label of a node of the W type -/
def shape : IndArg.{u} k → Type u
| plain α => α
| recur _ _ => PUnit

/-- The children of a node of the W type for the argument -/
def child : IndArg.{u} k → Type u
| plain _ => PEmpty
| recur βs _ => ProdList βs

/-- The type `Tₗ` of a child -/
def target : (x : IndArg k) → x.child → Fin k
| plain _, e => e.elim
| recur _ l, _ => l

end IndArg

namespace IndSig

variable (cs : IndSig.{u} k)

/-- Labels of the nodes of the W type: a constructor, with the non-recursive parts of its arguments -/
abbrev Shape := (c : Fin cs.length) × ProdList (cs[c].2.map IndArg.shape)

/-- Children of a node: an argument of the constructor, with an element of `β₁ × ⋯ × βₘ` -/
abbrev Child (a : cs.Shape) := (i : Fin cs[a.1].2.length) × cs[a.1].2[i].child

/-- The type `Tₗ` of a child -/
def target (a : cs.Shape) (b : cs.Child a) : Fin k := cs[a.1].2[b.1].target b.2

abbrev Tree := W cs.Shape cs.Child

/-- `t` is a well-typed element of `Tⱼ` -/
def WT : cs.Tree → Fin k → Prop
| .mk a f, j => cs[a.1].1 = j ∧ ∀ b, WT (f b) (cs.target a b)

theorem WT_mk {a : cs.Shape} {f : cs.Child a → cs.Tree} :
  cs.WT (.mk a f) j ↔ cs[a.1].1 = j ∧ ∀ b, cs.WT (f b) (cs.target a b) := Iff.rfl

/-- The interpretation of `Tⱼ` -/
def T (j : Fin k) := { t : cs.Tree // cs.WT t j }

end IndSig

namespace IndArg

variable (cs : IndSig.{u} k)

/-- The children of the node for the argument `x` with value `v` -/
def children : (x : IndArg k) → x.type cs.T → x.child → cs.Tree
| plain _, _, e => e.elim
| recur _ _, v, bs => (FuncList.uncurry v bs).val

theorem wt_children : (x : IndArg k) → (v : x.type cs.T) → (b : x.child) → cs.WT (x.children cs v b) (x.target b)
| plain _, _, e => e.elim
| recur _ _, v, bs => (FuncList.uncurry v bs).property

/-- The part of the argument `x` with value `v` stored in the label of the node -/
def toShape : (x : IndArg k) → x.type cs.T → x.shape
| plain _, v => v
| recur _ _, _ => ⟨⟩

/-- The value of the argument `x` with the given label and children -/
def ofShapeChildren : (x : IndArg k) → x.shape → (f : x.child → cs.Tree) →
  (∀ b, cs.WT (f b) (x.target b)) → x.type cs.T
| plain _, s, _, _ => s
| recur βs _, _, f, hf => FuncList.curry fun (bs : ProdList βs) => ⟨f bs, hf bs⟩

end IndArg

namespace IndSig

variable (cs : IndSig.{u} k)

/-- The arguments of the constructor `c` -/
abbrev Args (c : Fin cs.length) := ProdList (cs[c].2.map (IndArg.type cs.T))

/-- The element of `T cs[c].1` built by the constructor `c` from the arguments `xs` -/
def mkVal (c : Fin cs.length) (xs : cs.Args c) : cs.T cs[c].1 :=
  ⟨.mk ⟨c, ProdList.map (IndArg.toShape cs) _ xs⟩ (fun b => IndArg.children cs _ (ProdList.get _ xs b.1) b.2),
   (cs.WT_mk).mpr ⟨rfl, fun b => IndArg.wt_children cs _ _ b.2⟩⟩

/-- The constructor `c`, as a curried function -/
def ctor (c : Fin cs.length) : FuncList (cs[c].2.map (IndArg.type cs.T)) (cs.T cs[c].1) :=
  FuncList.curry (cs.mkVal c)

end IndSig

namespace IndArg

variable (cs : IndSig.{u} k)

theorem eq_of_toShape_children : (x : IndArg k) → {v w : x.type cs.T} →
  x.toShape cs v = x.toShape cs w → (∀ b, x.children cs v b = x.children cs w b) → v = w
| plain _, _, _, hs, _ => hs
| recur _ _, _, _, _, hc => FuncList.uncurry_inj (funext fun bs => Subtype.ext (hc bs))

theorem toShape_ofShapeChildren : (x : IndArg k) → (s : x.shape) → (f : x.child → cs.Tree) →
  (hf : ∀ b, cs.WT (f b) (x.target b)) → x.toShape cs (x.ofShapeChildren cs s f hf) = s
| plain _, _, _, _ => rfl
| recur _ _, ⟨⟩, _, _ => rfl

theorem children_ofShapeChildren : (x : IndArg k) → (s : x.shape) → (f : x.child → cs.Tree) →
  (hf : ∀ b, cs.WT (f b) (x.target b)) → x.children cs (x.ofShapeChildren cs s f hf) = f
| plain _, _, _, _ => funext fun e => e.elim
| recur _ _, _, _, _ => funext fun bs => congrArg Subtype.val (congrFun (FuncList.uncurry_curry _) bs)

theorem ofShapeChildren_toShape_children : (x : IndArg k) → (v : x.type cs.T) →
  (h : ∀ b, cs.WT (x.children cs v b) (x.target b)) → x.ofShapeChildren cs (x.toShape cs v) (x.children cs v) h = v
| plain _, _, _ => rfl
| recur _ _, v, _ => FuncList.curry_uncurry v

/-- The induction hypotheses for the argument `x` with value `v` -/
def IH (P : (j : Fin k) → cs.T j → Prop) : (x : IndArg k) → x.type cs.T → Prop
| plain _, _ => True
| recur _ l, v => ∀ bs, P l (FuncList.uncurry v bs)

theorem IH_ofShapeChildren (P : (j : Fin k) → cs.T j → Prop) : (x : IndArg k) → (s : x.shape) →
  (f : x.child → cs.Tree) → (hf : ∀ b, cs.WT (f b) (x.target b)) → (∀ b, P (x.target b) ⟨f b, hf b⟩) →
  x.IH cs P (x.ofShapeChildren cs s f hf)
| plain _, _, _, _, _ => True.intro
| recur _ _, _, _, _, h => fun bs => (congrArg (P _) (congrFun (FuncList.uncurry_curry _) bs)).mpr (h bs)

end IndArg

namespace IndSig

variable (cs : IndSig.{u} k)

theorem mk_congr {c : Fin cs.length} {s₁ s₂ : ProdList (cs[c].2.map IndArg.shape)} (hs : s₁ = s₂)
  {f₁ : cs.Child ⟨c, s₁⟩ → cs.Tree} {f₂ : cs.Child ⟨c, s₂⟩ → cs.Tree} (hf : ∀ b, f₁ b = f₂ b) :
  (W.mk ⟨c, s₁⟩ f₁ : cs.Tree) = W.mk ⟨c, s₂⟩ f₂ := by
  subst hs; rw [funext hf]

/-- The arguments of the element `.mk a f` of a type, which is built by the constructor `a.1` -/
def argsOf (a : cs.Shape) (f : cs.Child a → cs.Tree) (hf : ∀ b, cs.WT (f b) (cs.target a b)) : cs.Args a.1 :=
  ProdList.ofFn _ fun i =>
    IndArg.ofShapeChildren cs _ (ProdList.get _ a.2 i) (fun b => f ⟨i, b⟩) (fun b => hf ⟨i, b⟩)

theorem mkVal_argsOf (a : cs.Shape) (f : cs.Child a → cs.Tree) (hf : ∀ b, cs.WT (f b) (cs.target a b)) :
  (cs.mkVal a.1 (cs.argsOf a f hf)).val = .mk a f := by
  cases a with
  | mk c s =>
    apply mk_congr
    · apply ProdList.ext; intro i
      dsimp only [argsOf]
      rw [ProdList.get_map, ProdList.get_ofFn]
      exact IndArg.toShape_ofShapeChildren cs _ _ _ _
    · intro ⟨i, b⟩
      show IndArg.children cs _ (ProdList.get _ (cs.argsOf ⟨c, s⟩ f hf) i) b = f ⟨i, b⟩
      dsimp only [argsOf]
      rw [ProdList.get_ofFn]
      exact congrFun (IndArg.children_ofShapeChildren cs _ _ _ _) b

/-- Different constructors build different elements -/
theorem mkVal_ne {c₁ c₂ : Fin cs.length} (h : c₁ ≠ c₂) (xs : cs.Args c₁) (ys : cs.Args c₂) :
  (cs.mkVal c₁ xs).val ≠ (cs.mkVal c₂ ys).val := by
  intro heq
  injection heq with heq _
  exact h (congrArg Sigma.fst heq)

/-- The constructors are injective -/
theorem mkVal_inj {c : Fin cs.length} {xs ys : cs.Args c} (heq : cs.mkVal c xs = cs.mkVal c ys) : xs = ys := by
  have heq := congrArg Subtype.val heq
  injection heq with hs hc
  have hs := eq_of_heq (Sigma.mk.inj hs).right
  apply ProdList.ext; intro i
  apply IndArg.eq_of_toShape_children cs
  · have := congrArg (fun s => ProdList.get _ s i) hs
    simpa only [ProdList.get_map] using this
  · intro b; exact congrFun hc ⟨i, b⟩

/--
  Induction over `T₀ ⋯ Tₖ₋₁`, with induction hypotheses for all the recursive arguments
    of the constructors, including the arguments of type `β₁ → ⋯ → βₘ → Tₗ`
-/
theorem induction (P : (j : Fin k) → cs.T j → Prop)
  (H : ∀ (c : Fin cs.length) (xs : cs.Args c),
    (∀ i, IndArg.IH cs P cs[c].2[i] (ProdList.get _ xs i)) → P cs[c].1 (cs.mkVal c xs)) :
  ∀ j (t : cs.T j), P j t := by
  intro j ⟨t, ht⟩
  induction t generalizing j with
  | mk a f IH =>
    obtain ⟨hj, hf⟩ := (cs.WT_mk).mp ht
    subst hj
    have key := H a.1 (cs.argsOf a f hf) fun i => by
      dsimp only [argsOf]; rw [ProdList.get_ofFn]
      exact IndArg.IH_ofShapeChildren cs P _ _ _ _ fun b => IH ⟨i, b⟩ _ (hf ⟨i, b⟩)
    have heq : cs.mkVal a.1 (cs.argsOf a f hf) = ⟨.mk a f, ht⟩ := Subtype.ext (cs.mkVal_argsOf a f hf)
    rwa [heq] at key

/-- The `i`-th argument of the elements of `cs[c].1`, whose only constructor is `c` -/
def proj (c : Fin cs.length) (hc : ∀ c', cs[c'].1 = cs[c].1 → c' = c) (i : Fin cs[c].2.length) :
  cs.T cs[c].1 → IndArg.type cs.T cs[c].2[i]
| ⟨.mk a f, ht⟩ =>
  have hac : a.1 = c := hc a.1 ((cs.WT_mk).mp ht).1
  ProdList.get _ (hac ▸ cs.argsOf a f ((cs.WT_mk).mp ht).2) i

theorem proj_mkVal (c : Fin cs.length) (hc : ∀ c', cs[c'].1 = cs[c].1 → c' = c) (i : Fin cs[c].2.length)
  (xs : cs.Args c) : cs.proj c hc i (cs.mkVal c xs) = ProdList.get _ xs i := by
  let a : cs.Shape := ⟨c, ProdList.map (IndArg.toShape cs) _ xs⟩
  let f : cs.Child a → cs.Tree := fun b => IndArg.children cs _ (ProdList.get _ xs b.1) b.2
  have h : ∀ hf : (∀ b, cs.WT (f b) (cs.target a b)), ProdList.get _ (cs.argsOf a f hf) i = ProdList.get _ xs i := by
    intro hf
    dsimp only [argsOf, a, f]
    rw [ProdList.get_ofFn, ProdList.get_map]
    exact IndArg.ofShapeChildren_toShape_children cs _ _ _
  exact h _

end IndSig

/--
  The simple mutual inductive types described by `mind`, where the other sorts are interpreted
    by `tyVal`. The sort of each argument of a constructor should either not mention the types
    of `mind`, or be `B₁ → ⋯ → Bₘ → Tₗ`, where `B₁ ⋯ Bₘ` do not mention the types of `mind`
-/
def MutualIndInfo.toIndSig? (tyVal : TyVal.{u}) (mind : MutualIndInfo) : Option (IndSig.{u} mind.length) :=
  let tys := mind.map (·.type)
  let isInd (s : LamSort) : Bool := tys.any s.contains
  let arg? (s : LamSort) : Option (IndArg.{u} mind.length) :=
    if !isInd s then
      .some (.plain (s.interp tyVal))
    else if s.getArgTys.any isInd then
      .none
    else
      ((tys.findFinIdx? (· == s.getResTy)).map (Fin.cast (List.length_map _))).map
        (.recur (s.getArgTys.map (·.interp tyVal)))
  ((List.finRange mind.length).flatMap fun j => mind[j].ctors.map fun (s, _) => (j, s)).mapM fun (j, s) =>
    if s.getResTy != mind[j].type then
      .none
    else
      (s.getArgTys.mapM arg?).map (j, ·)

end Auto.Embedding.Lam
