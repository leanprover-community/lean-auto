module

public import Auto.EmbedCoc.CoCBase
public import Auto.Embedding.Lift
public import Auto.Lib.BoolExtra

@[expose] public section

/-!
  The model of the embedded system. Each sort is interpreted as the Lean sort of
  the same level and `∀` as Lean's `∀`, so e.g. the embedded `∀ x : Nat, x = x`
  is interpreted as the Lean proposition `∀ x : Nat, x = x` itself. The embedded
  levels `u` and `v` are interpreted as the Lean universe levels `u` and `v`.

  Values of different levels have to share one Lean type, so types and their
  elements are lifted into one universe, `SemSortMax`. Only the wrappers are
  uniform: `A.down` is the genuine Lean type for each `A : SemSort.Ty s`
-/

namespace Auto.Embedding.CoC

universe u v

/--
  The levels of the model: those of the sorts `CoCSort`, together with the levels
  of their types. A type at a top sort, such as `Nat → Type : Sort 2`, is still a
  value, and its type `Sort 2` lives in `Sort 3`
-/
meta def SemLevel : List Lean.Level := withSuccLevels CoCLevel

/-- The levels of the model, one per level of `SemLevel` -/
mkSortType SemSort from SemLevel deriving Inhabited, DecidableEq

set_option linter.checkUnivs false in
/-- The universe that the types and values of the model are lifted into -/
mkSortMax SemSortMax from SemLevel

/-- Types at level `s`, i.e. elements of `Sort s`, lifted into `SemSortMax` -/
mkSortTy SemSort.Ty for SemSort from SemLevel SemSortMax

/-- Elements of a type at level `s`, lifted into `SemSortMax` -/
mkSortEl SemSort.El for SemSort from SemLevel SemSort.Ty SemSortMax

/-- Proofs are irrelevant in the model, as they are in Lean -/
instance (A : SemSort.Ty.{u, v} .prop) : Subsingleton (SemSort.El .prop A) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- The level of `Sort s` -/
mkSortMap CoCSort.toSem : CoCSort → SemSort from CoCLevel SemLevel

/--
  The level of the type of `Sort s`, i.e. `s + 1`. Unlike `CoCSort.succ` this is
  total, since the model has a level above each top sort
-/
mkSortMap CoCSort.sortOf : CoCSort → SemSort from CoCLevel SemLevel + 1

/-- The sort `s` with `s.sortOf = l`, if any -/
mkSortMap SemSort.pred? : SemSort → Option CoCSort from SemLevel CoCLevel - 1

theorem CoCSort.pred?_sortOf (s : CoCSort) : s.sortOf.pred? = some s := by
  cases s <;> rfl

theorem SemSort.sortOf_of_pred? {l : SemSort} {s : CoCSort} (h : l.pred? = some s) :
    s.sortOf = l := by
  cases l <;> cases h <;> rfl

/-- `CoCSort.succ` agrees with the levels of the model -/
theorem CoCSort.toSem_of_succ {s s₁ : CoCSort} (h : s.succ = some s₁) : s₁.toSem = s.sortOf := by
  cases s <;> cases h <;> rfl

/-- `Sort s` itself, as a type at level `s.sortOf` -/
mkSortCode CoCSort.sortCode for CoCSort from CoCLevel : (s : CoCSort) → SemSort.Ty.{u, v} s.sortOf

/-- A type at sort `s`, as an element of `Sort s` -/
def CoCSort.tyUp (s : CoCSort) (A : SemSort.Ty.{u, v} s.toSem) : SemSort.El s.sortOf s.sortCode := by
  cases s <;> exact ⟨A.down⟩

/-- An element of `Sort s`, as a type at sort `s`. Inverse to `CoCSort.tyUp` -/
def CoCSort.tyDown (s : CoCSort) (a : SemSort.El.{u, v} s.sortOf s.sortCode) : SemSort.Ty s.toSem := by
  cases s <;> exact ⟨a.down⟩

theorem CoCSort.tyDown_tyUp (s : CoCSort) (A : SemSort.Ty.{u, v} s.toSem) :
    s.tyDown (s.tyUp A) = A := by
  cases s <;> rfl

theorem CoCSort.tyUp_tyDown (s : CoCSort) (a : SemSort.El.{u, v} s.sortOf s.sortCode) :
    s.tyUp (s.tyDown a) = a := by
  cases s <;> rfl

/--
  The genuine Lean `∀ x : A, B x`, at the sort `r` that `CoCSort.join` predicts.
  Defining it makes Lean check, case by case, that `Level.imax` agrees with `join`
-/
def CoCSort.pi (s s' : CoCSort) {r : CoCSort} (h : s.join s' = some r)
    (A : SemSort.Ty.{u, v} s.toSem) (B : SemSort.El s.toSem A → SemSort.Ty.{u, v} s'.toSem) :
    SemSort.Ty.{u, v} r.toSem := by
  cases s <;> cases s' <;>
    cases h <;> exact ⟨∀ x : A.down, (B ⟨x⟩).down⟩

/-- `fun x : A => f x`, as an element of `CoCSort.pi s s' h A B` -/
def CoCSort.lam (s s' : CoCSort) {r : CoCSort} (h : s.join s' = some r)
    (A : SemSort.Ty.{u, v} s.toSem) (B : SemSort.El s.toSem A → SemSort.Ty.{u, v} s'.toSem)
    (f : (x : SemSort.El s.toSem A) → SemSort.El s'.toSem (B x)) :
    SemSort.El r.toSem (CoCSort.pi s s' h A B) := by
  cases s <;> cases s' <;>
    cases h <;> exact ⟨fun x => (f ⟨x⟩).down⟩

/-- Applying an element of `CoCSort.pi s s' h A B` -/
def CoCSort.app (s s' : CoCSort) {r : CoCSort} (h : s.join s' = some r)
    (A : SemSort.Ty.{u, v} s.toSem) (B : SemSort.El s.toSem A → SemSort.Ty.{u, v} s'.toSem)
    (f : SemSort.El r.toSem (CoCSort.pi s s' h A B)) (a : SemSort.El s.toSem A) :
    SemSort.El s'.toSem (B a) := by
  cases s <;> cases s' <;>
    cases h <;> exact ⟨f.down a.down⟩

/-- `β` holds in the model -/
theorem CoCSort.app_lam (s s' : CoCSort) {r : CoCSort} (h : s.join s' = some r)
    (A : SemSort.Ty.{u, v} s.toSem) (B : SemSort.El s.toSem A → SemSort.Ty.{u, v} s'.toSem)
    (f : (x : SemSort.El s.toSem A) → SemSort.El s'.toSem (B x)) (a : SemSort.El s.toSem A) :
    CoCSort.app s s' h A B (CoCSort.lam s s' h A B f) a = f a := by
  cases s <;> cases s' <;>
    cases h <;> rfl

/-- `η` holds in the model -/
theorem CoCSort.lam_app (s s' : CoCSort) {r : CoCSort} (h : s.join s' = some r)
    (A : SemSort.Ty.{u, v} s.toSem) (B : SemSort.El s.toSem A → SemSort.Ty.{u, v} s'.toSem)
    (f : SemSort.El r.toSem (CoCSort.pi s s' h A B)) :
    CoCSort.lam s s' h A B (fun x => CoCSort.app s s' h A B f x) = f := by
  cases s <;> cases s' <;>
    cases h <;> rfl

/--
  A value of the model, together with its type and the level of that type. Its
  universe is given, since Lean would infer one without the `imax`es of `SemSortMax`
-/
structure DVal : SemSortMax.{u, v} where
  /-- The level of `ty` -/
  s   : SemSort
  /-- The type of `val` -/
  ty  : SemSort.Ty.{u, v} s
  val : SemSort.El s ty

/-- A type at sort `s`, as a value: an element of `Sort s` -/
def DVal.ofTy (s : CoCSort) (A : SemSort.Ty.{u, v} s.toSem) : DVal.{u, v} :=
  ⟨s.sortOf, s.sortCode, s.tyUp A⟩

/--
  `d` as an element of `T`, or `none` when `d` has another type. Equality of
  Lean types is undecidable, so this is classical
-/
noncomputable def DVal.get? (s : SemSort) (T : SemSort.Ty.{u, v} s) (d : DVal.{u, v}) :
    Option (SemSort.El s T) :=
  open Classical in
  if h : ∃ x, d = ⟨s, T, x⟩ then some h.choose else none

theorem DVal.get?_eq_some {s : SemSort} {T : SemSort.Ty.{u, v} s} {d : DVal.{u, v}}
    {x : SemSort.El s T} : d.get? s T = some x ↔ d = ⟨s, T, x⟩ := by
  unfold DVal.get?
  split
  case isTrue h =>
    rw [Option.some.injEq]
    constructor
    · intro hx; rw [← hx]; exact h.choose_spec
    · intro hd
      have hx := (DVal.mk.inj (hd.symm.trans h.choose_spec)).2.2
      exact (eq_of_heq hx).symm
  case isFalse h =>
    constructor
    · intro hn; cases hn
    · intro hd; exact absurd ⟨x, hd⟩ h

theorem DVal.get?_mk (s : SemSort) (T : SemSort.Ty.{u, v} s) (x : SemSort.El s T) :
    DVal.get? s T ⟨s, T, x⟩ = some x :=
  DVal.get?_eq_some.mpr rfl

/-- `d` as a type at sort `s`, i.e. when `d` is an element of `Sort s` -/
noncomputable def DVal.asTy (s : CoCSort) (d : DVal.{u, v}) : Option (SemSort.Ty.{u, v} s.toSem) :=
  (d.get? s.sortOf s.sortCode).map s.tyDown

theorem DVal.asTy_eq_some {s : CoCSort} {d : DVal.{u, v}} {A : SemSort.Ty.{u, v} s.toSem} :
    d.asTy s = some A ↔ d = DVal.ofTy s A := by
  unfold DVal.asTy DVal.ofTy
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [DVal.get?_eq_some.mp ha, CoCSort.tyUp_tyDown]
  · intro hd
    exact ⟨s.tyUp A, DVal.get?_eq_some.mpr hd, CoCSort.tyDown_tyUp s A⟩

theorem DVal.asTy_ofTy (s : CoCSort) (A : SemSort.Ty.{u, v} s.toSem) :
    (DVal.ofTy s A).asTy s = some A :=
  DVal.asTy_eq_some.mpr rfl

/--
  `Sort s` as a value, i.e. as a type at sort `s + 1`, or `none` when `s` is a top sort.
  `s.sortCode` is at level `s.sortOf`, which is the level of `s + 1` by `toSem_of_succ`
-/
def CoCSort.sortVal (s : CoCSort) : Option DVal.{u, v} :=
  match h : s.succ with
  | some s₁ => some (.ofTy s₁ (cast (congrArg SemSort.Ty (CoCSort.toSem_of_succ h).symm) s.sortCode))
  | none    => none

/-- The Lean type that `σ` stands for -/
def ConstTy.interp : ConstTy → Type
  | .prop     => Prop
  | .bool     => Bool
  | .nat      => Nat
  | .func σ τ => σ.interp → τ.interp

/-- A constant `x : σ` as a value. Its type `σ` is in `Sort 1`, i.e. at level `.«1»` -/
def DVal.ofConst (σ : ConstTy) (x : σ.interp) : DVal.{u, v} :=
  ⟨.«1», ⟨σ.interp⟩, ⟨x⟩⟩

def PropConst.interpVal : (pc : PropConst) → pc.constTy.interp
  | .trueE  => True
  | .falseE => False
  | .not    => Not
  | .and    => And
  | .or     => Or
  | .imp    => fun p q => p → q
  | .iff    => Iff

noncomputable def BoolConst.interpVal : (bc : BoolConst) → bc.constTy.interp
  | .ofProp => Bool.ofProp
  | .trueb  => true
  | .falseb => false
  | .notb   => fun a => !a
  | .andb   => fun a b => a && b
  | .orb    => fun a b => a || b

def NatConst.interpVal : (nc : NatConst) → nc.constTy.interp
  | .natVal n => n
  | .nadd     => Nat.add
  | .nsub     => Nat.sub
  | .nmul     => Nat.mul
  | .ndiv     => Nat.div
  | .nmod     => Nat.mod
  | .nle      => Nat.le
  | .nlt      => Nat.lt
  | .nmax     => Nat.max
  | .nmin     => Nat.min

def PropConst.interp (pc : PropConst) : DVal.{u, v} := .ofConst pc.constTy pc.interpVal

noncomputable def BoolConst.interp (bc : BoolConst) : DVal.{u, v} := .ofConst bc.constTy bc.interpVal

def NatConst.interp (nc : NatConst) : DVal.{u, v} := .ofConst nc.constTy nc.interpVal

/--
  The value of a base term, or `none` when it is a top sort, which has no type.
  Mirrors `CoCBaseTerm.check`
-/
noncomputable def CoCBaseTerm.interp : CoCBaseTerm → Option DVal.{u, v}
  | .sort s  => s.sortVal
  | .bool    => some (.ofTy .«1» ⟨Bool⟩)
  | .nat     => some (.ofTy .«1» ⟨Nat⟩)
  | .pcst pc => some pc.interp
  | .bcst bc => some bc.interp
  | .ncst nc => some nc.interp

-- Regression checks that the model is genuine, i.e. that interpretations reduce
-- to the Lean types they stand for

/-- Impredicativity: `∀ α : Type, ∀ x : α, x = x` is the Lean proposition itself -/
example : (CoCSort.pi .«2» .prop rfl ⟨Type⟩ (fun α =>
    CoCSort.pi .«1» .prop rfl ⟨α.down⟩ (fun x => ⟨x.down = x.down⟩))).down =
    (∀ α : Type, ∀ x : α, x = x) := rfl

/-- `imax 1 u = u`: `Nat → X` for `X : Sort u` lands in `Sort u` -/
example (X : Sort u) :
    (CoCSort.pi.{u, v} .«1» .«u» rfl ⟨Nat⟩ (fun _ => ⟨X⟩)).down = (Nat → X) :=
  rfl

end Auto.Embedding.CoC
