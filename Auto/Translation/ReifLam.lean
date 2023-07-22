import Auto.Translation.Lift

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.ReifLam

inductive LamSort
| atom : Nat → LamSort
| func : LamSort → LamSort → LamSort
deriving Inhabited, Hashable, BEq

@[reducible] def LamSort.interp.{u} (val : Nat → Sort u) : LamSort → Sort u
| .atom n => val n
| .func dom cod => interp val dom → interp val cod

inductive LamTerm
| atom    : Nat → LamTerm
| bvar    : Nat → LamTerm
-- Supporting polymorphic `eq`
| eq      : LamTerm → LamTerm → LamTerm
| lam     : LamSort → LamTerm → LamTerm
| app     : LamTerm → LamTerm → LamTerm

-- Valuation
structure LamVal.{u} where
  tyVal    : Nat → Type (u + 1)
  constVal : Nat → (s : LamSort) × LamSort.interp tyVal s

-- Interpretation pair, `(Simply typed lambda calculus term, CIC term)`
structure LamInterp.{u} where
  -- Local context, list of CIC terms
  lctx    : List ((α : Type (u + 1)) × α)
  -- A term in simply typed lambda calculus
  rterm   : LamTerm
  -- Type of `mterm`
  ty      : Type (u + 1)
  -- The CIC term that `rterm` translates into
  mterm   : ty

inductive WF.{u} (val : LamVal.{u}) : LamInterp.{u} → Prop
  | ofAtom n
      {lctx : List ((γ : Type (u + 1)) × γ)} :
    WF val <|
      let ci := val.constVal n
      let ty := LamSort.interp val.tyVal ci.fst
      ⟨lctx, (.atom n), ty, ci.snd⟩
  | ofBVar
      {lctx : List ((α : Type (u + 1)) × α)}
      (n : Fin lctx.length) :
    WF val <|
      ⟨lctx, .bvar n, lctx[n].fst, lctx[n].snd⟩
  | ofEq
      {lctx : List ((γ : Type (u + 1)) × γ)}
      {hlhs hrhs : LamTerm}
      (α : Type (u + 1)) (lhs rhs : α)
      (Hl : WF val ⟨lctx, hlhs, α, lhs⟩)
      (Hr : WF val ⟨lctx, hrhs, α, rhs⟩) :
    WF val <|
      ⟨lctx, .eq hlhs hrhs, Type u, EqLift lhs rhs⟩
  | ofLam
      {lctx : List ((γ : Type (u + 1)) × γ)}
      {hs : LamSort} {ht : LamTerm}
      (α β : Type (u + 1)) (fn : α → β)
      (H : ∀ (t : α), WF val ⟨⟨α, t⟩ :: lctx, ht, β, fn t⟩)
      :
    WF val <|
      ⟨lctx, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctx : List ((γ : Type (u + 1)) × γ)}
      {hfn harg : LamTerm}
      (α β : Type (u + 1)) (fn : α → β) (arg : α)
      (Hfn : WF val ⟨lctx, hfn, α → β, fn⟩)
      (Harg : WF val ⟨lctx, harg, α, arg⟩)
      :
    WF val <|
      ⟨lctx, .app hfn harg, β, fn arg⟩

section Example
  
  def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  def interpEx₁.{u} : LamInterp.{u} :=
    ⟨[], .lam (.atom 0) (.app (.atom 0) (.bvar 0)),
     GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  def valuation₁.{u} : LamVal.{u} :=
    ⟨fun _ => GLift Nat, fun _ => ⟨.func (.atom 0) (.atom 0), Nat.succLift⟩⟩

  def wf.{u} : WF valuation₁.{u} interpEx₁.{u} := by
    apply WF.ofLam
    intro t
    apply WF.ofApp
    case Hfn =>
      apply WF.ofAtom
    case Harg =>
      apply (WF.ofBVar (lctx :=[{ fst := GLift Nat, snd := t }]) ⟨0, by simp⟩)

end Example

end Auto.ReifLam