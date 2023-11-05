@[reducible] def pushLCtx (x : α) (lctx : Nat → α) (n : Nat) : α :=
  match n with
  | 0 => x
  | n' + 1 => lctx n'

inductive Pos where
  | xH : Pos
  | xO : Pos → Pos
  | xI : Pos → Pos
deriving Inhabited, Hashable

set_option profiler true


-- This `namespace Fast` does not reveal any issue. It's meant to
--   be compared to `namespace Slow` and ``namespace Switch`
namespace Fast

  inductive LamSort
  | atom : Nat → LamSort
  | func : LamSort → LamSort → LamSort
  deriving Inhabited, Hashable

  structure LamTyVal where
    lamVarTy     : Nat → LamSort
    lamILTy      : Nat → LamSort
    lamEVarTy    : Nat → LamSort

  inductive LamTerm
    | atom    : Nat → LamTerm
    -- Existential atoms. Supports definition and skolemization
    | etom    : Nat → LamTerm
    | bvar    : Nat → LamTerm
    | lam     : LamSort → LamTerm → LamTerm
    -- The `LamSort` is here so that both the type of
    --   the function and argument can be inferred directly
    --   when we know the type of the application
    | app     : LamSort → LamTerm → LamTerm → LamTerm
  deriving Inhabited, Hashable

  structure LamJudge where
    lctx   : Nat → LamSort
    rterm  : LamTerm
    rty    : LamSort
  deriving Inhabited

  inductive LamWF (ltv : LamTyVal) : LamJudge → Type
    | ofAtom
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, .atom n, ltv.lamVarTy n⟩
    | ofEtom
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, .etom n, ltv.lamEVarTy n⟩
    | ofBVar
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, .bvar n, lctx n⟩
    | ofLam
        {lctx : Nat → LamSort}
        {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
        (H : LamWF ltv ⟨pushLCtx argTy lctx, body, bodyTy⟩) :
      LamWF ltv ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
    | ofApp
        {lctx : Nat → LamSort}
        (argTy : LamSort) {resTy : LamSort}
        {fn : LamTerm} {arg : LamTerm}
        (HFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩)
        (HArg : LamWF ltv ⟨lctx, arg, argTy⟩) :
      LamWF ltv ⟨lctx, .app argTy fn arg, resTy⟩

  def LamTerm.mapBVarAt (idx : Nat) (f : Nat → Nat) (t : LamTerm) : LamTerm :=
    match t with
    | .atom n       => .atom n
    | .etom n       => .etom n
    | .bvar n       => .bvar n
    | .lam s t      => .lam s (t.mapBVarAt (.succ idx) f)
    | .app s fn arg => .app s (fn.mapBVarAt idx f) (arg.mapBVarAt idx f)

  def LamWF.fromMapBVarAtAux
    (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
    (hRTerm : rterm' = rterm.mapBVarAt idx f)
    (HWF : LamWF lamVarTy ⟨lctx', rterm', rty⟩) : LamWF lamVarTy ⟨lctx, rterm, rty⟩ :=
    match rterm with
    | .atom n =>
      match HWF with
      | .ofAtom _ => by rw [LamTerm.atom.inj hRTerm]; apply ofAtom
    | .etom n =>
      match HWF with
      | .ofEtom _ => sorry
    | .bvar n =>
      match HWF with
      | .ofBVar _ => sorry
    | .lam argTy body =>
      match HWF with
      | .ofLam bodyTy wfBody => sorry
    | .app argTy' fn arg =>
      match HWF with
      | .ofApp _ HFn HArg => sorry

  def non_general_match (hwf : LamWF ltv ⟨lctx, .lam argTy body, .func a b⟩) : True := by
    cases hwf; exact True.intro

end Fast


-- Compared to `namespace fast`, the only difference is that
--   we switched the second and third field in `LamJudge`.
-- However, notice that `Fast.non_general_match` is able to compile,
--   while `Switch.non_general_match` fails.
-- It would be great if the behaviour of equational compiler
--   does not depend on the order of constructors/fields in
--   the inductive type.
namespace Switch

  inductive LamSort
  | atom : Nat → LamSort
  | func : LamSort → LamSort → LamSort
  deriving Inhabited, Hashable

  structure LamTyVal where
    lamVarTy     : Nat → LamSort
    lamILTy      : Nat → LamSort
    lamEVarTy    : Nat → LamSort

  inductive LamTerm
    | atom    : Nat → LamTerm
    -- Existential atoms. Supports definition and skolemization
    | etom    : Nat → LamTerm
    | bvar    : Nat → LamTerm
    | lam     : LamSort → LamTerm → LamTerm
    -- The `LamSort` is here so that both the type of
    --   the function and argument can be inferred directly
    --   when we know the type of the application
    | app     : LamSort → LamTerm → LamTerm → LamTerm
  deriving Inhabited, Hashable

  structure LamJudge where
    lctx   : Nat → LamSort
    rty    : LamSort
    rterm  : LamTerm
  deriving Inhabited

  -- **Note: Branches irrelevant to the issue are deleted**
  inductive LamWF (ltv : LamTyVal) : LamJudge → Type
    | ofAtom
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, ltv.lamVarTy n, .atom n⟩

  def non_general_match (hwf : LamWF ltv ⟨lctx, .func a b, .lam argTy body⟩) : True := by
    cases hwf; exact True.intro

end Switch


-- Issues:
-- 1. Compilation of `LamWF.fromMapBVarAtAux` is unexpectedly slow
--    Compared to `Fast`, we only added one extra constructor to
--    `LamBaseSort` and `LamTerm`, but the compilation
--    time changes from `200ms` to over `15s`
-- 2. In `LamWF.fromMapBVarAtAux₂`, the equational solver could not
--    solve `LamTerm.bvar n✝ = LamTerm.mapBVarAt idx f (LamTerm.bvar n)`,
--    but `LamTerm.mapBVarAt idx f (LamTerm.bvar n)` is definitionally
--    equal to `LamTerm.bvar n`, so the equational
--    matcher should be able to solve it
namespace Slow

  /-- Interpreted sorts -/
  inductive LamBaseSort
    | prop   : LamBaseSort            -- GLift `Prop`
    | bool   : LamBaseSort            -- GLift `Bool`
    | nat    : LamBaseSort            -- GLift `Nat`
    | int    : LamBaseSort            -- GLift `Int`
    /--
      For each `p : Pos`, `isto0 p` is an interpreted sort
      `p`       `isto0 p`
      .xH        String
      _          Empty
    -/
    | isto0  : Pos → LamBaseSort
    | bv     : (n : Nat) → LamBaseSort -- GLift `BitVec n`
  deriving Hashable, Inhabited

  inductive LamSort
  | atom : Nat → LamSort
  | base : LamBaseSort → LamSort
  | func : LamSort → LamSort → LamSort
  deriving Inhabited, Hashable

  inductive BoolConst
    | trueb  -- Boolean `true`
    | falseb -- Boolean `false`
    | notb   -- Boolean `not`
    | andb   -- Boolean `and`
    | orb    -- Boolean `or`
  deriving Inhabited, Hashable

  inductive BoolConst.LamWF : BoolConst → LamSort → Type
    | ofTrueB      : LamWF .trueb (.base .bool)
    | ofFalseB     : LamWF .falseb (.base .bool)
    | ofNotB       : LamWF .notb (.func (.base .bool) (.base .bool))
    | ofAndB       : LamWF .andb (.func (.base .bool) (.func (.base .bool) (.base .bool)))
    | ofOrB        : LamWF .orb (.func (.base .bool) (.func (.base .bool) (.base .bool)))

  inductive NatConst
    | natVal (n : Nat)
    | nadd
    | nsub
    | nmul
    | ndiv
    | nmod
    | nle
    | nge
    | nlt
    | ngt
  deriving Inhabited, Hashable

  inductive NatConst.LamWF : NatConst → LamSort → Type
    | ofNatVal n : LamWF (.natVal n) (.base .nat)
    | ofNadd     : LamWF .nadd (.func (.base .nat) (.func (.base .nat) (.base .nat)))
    | ofNsub     : LamWF .nsub (.func (.base .nat) (.func (.base .nat) (.base .nat)))
    | ofNmul     : LamWF .nmul (.func (.base .nat) (.func (.base .nat) (.base .nat)))
    | ofNdiv     : LamWF .ndiv (.func (.base .nat) (.func (.base .nat) (.base .nat)))
    | ofNmod     : LamWF .nmod (.func (.base .nat) (.func (.base .nat) (.base .nat)))
    | ofNle      : LamWF .nle (.func (.base .nat) (.func (.base .nat) (.base .prop)))
    | ofNge      : LamWF .nge (.func (.base .nat) (.func (.base .nat) (.base .prop)))
    | ofNlt      : LamWF .nlt (.func (.base .nat) (.func (.base .nat) (.base .prop)))
    | ofNgt      : LamWF .ngt (.func (.base .nat) (.func (.base .nat) (.base .prop)))

  inductive IntConst
    | intVal (n : Int)
    | iofNat
    | inegSucc
    | ineg
    | iabs
    | iadd
    | isub
    | imul
    | idiv
    | imod
    | iediv
    | iemod
    | ile
    | ige
    | ilt
    | igt
  deriving Inhabited, Hashable

  inductive IntConst.LamWF : IntConst → LamSort → Type
    | ofIntVal n : LamWF (.intVal n) (.base .int)
    | ofIOfNat   : LamWF .iofNat (.func (.base .nat) (.base .int))
    | ofINegSucc : LamWF .inegSucc (.func (.base .nat) (.base .int))
    | ofIneg     : LamWF .ineg (.func (.base .int) (.base .int))
    | ofIabs     : LamWF .iabs (.func (.base .int) (.base .int))
    | ofIadd     : LamWF .iadd (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofIsub     : LamWF .isub (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofImul     : LamWF .imul (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofIdiv     : LamWF .idiv (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofImod     : LamWF .imod (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofIediv    : LamWF .iediv (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofIemod    : LamWF .iemod (.func (.base .int) (.func (.base .int) (.base .int)))
    | ofIle      : LamWF .ile (.func (.base .int) (.func (.base .int) (.base .prop)))
    | ofIge      : LamWF .ige (.func (.base .int) (.func (.base .int) (.base .prop)))
    | ofIlt      : LamWF .ilt (.func (.base .int) (.func (.base .int) (.base .prop)))
    | ofIgt      : LamWF .igt (.func (.base .int) (.func (.base .int) (.base .prop)))

  inductive LamBaseTerm
    | trueE    : LamBaseTerm -- Propositional `true`
    | falseE   : LamBaseTerm -- Propositional `false`
    | not      : LamBaseTerm -- Propositional `not`
    | and      : LamBaseTerm -- Propositional `and`
    | or       : LamBaseTerm -- Propositional `or`
    | imp      : LamBaseTerm -- Propositional `imp`
    | iff      : LamBaseTerm -- Propositional `iff`
    | bcst     : BoolConst → LamBaseTerm
    | ncst     : NatConst → LamBaseTerm
    | icst     : IntConst → LamBaseTerm
    | bvVal    : List Bool → LamBaseTerm
    | eqI      : Nat → LamBaseTerm
    | forallEI : Nat → LamBaseTerm
    | existEI  : Nat → LamBaseTerm
    -- Non-import versions of `eq, ∀, ∃`
    | eq       : LamSort → LamBaseTerm
    | forallE  : LamSort → LamBaseTerm
    | existE   : LamSort → LamBaseTerm
  deriving Inhabited, Hashable

  structure LamTyVal where
    lamVarTy     : Nat → LamSort
    lamILTy      : Nat → LamSort
    lamEVarTy    : Nat → LamSort

  inductive LamBaseTerm.LamWF (ltv : LamTyVal) : LamBaseTerm → LamSort → Type
    | ofTrueE      : LamWF ltv .trueE (.base .prop)
    | ofFalseE     : LamWF ltv .falseE (.base .prop)
    | ofNot        : LamWF ltv .not (.func (.base .prop) (.base .prop))
    | ofAnd        : LamWF ltv .and (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    | ofOr         : LamWF ltv .or (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    | ofImp        : LamWF ltv .imp (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    | ofIff        : LamWF ltv .iff (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    | ofBcst       : (bcwf : BoolConst.LamWF bc s) → LamWF ltv (.bcst bc) s
    | ofNcst       : (ncwf : NatConst.LamWF nc s) → LamWF ltv (.ncst nc) s
    | ofIcst       : (icwf : IntConst.LamWF ic s) → LamWF ltv (.icst ic) s
    | ofBvVal ls   : LamWF ltv (.bvVal ls) (.base (.bv ls.length))
    | ofEqI n      : LamWF ltv (.eqI n) (.func (ltv.lamILTy n) (.func (ltv.lamILTy n) (.base .prop)))
    | ofForallEI n : LamWF ltv (.forallEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
    | ofExistEI n  : LamWF ltv (.existEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
    | ofEq s       : LamWF ltv (.eq s) (.func s (.func s (.base .prop)))
    | ofForallE s  : LamWF ltv (.forallE s) (.func (.func s (.base .prop)) (.base .prop))
    | ofExistE s   : LamWF ltv (.existE s) (.func (.func s (.base .prop)) (.base .prop))

  inductive LamTerm
    | atom    : Nat → LamTerm
    -- Existential atoms. Supports definition and skolemization
    | etom    : Nat → LamTerm
    | base    : LamBaseTerm → LamTerm
    | bvar    : Nat → LamTerm
    | lam     : LamSort → LamTerm → LamTerm
    -- The `LamSort` is here so that both the type of
    --   the function and argument can be inferred directly
    --   when we know the type of the application
    | app     : LamSort → LamTerm → LamTerm → LamTerm
  deriving Inhabited, Hashable

  structure LamJudge where
    lctx   : Nat → LamSort
    rterm  : LamTerm
    rty    : LamSort
  deriving Inhabited

  inductive LamWF (ltv : LamTyVal) : LamJudge → Type
    | ofAtom
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, .atom n, ltv.lamVarTy n⟩
    | ofEtom
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, .etom n, ltv.lamEVarTy n⟩
    | ofBase
        {lctx : Nat → LamSort} {b : LamBaseTerm} {s : LamSort}
        (H : LamBaseTerm.LamWF ltv b s) :
      LamWF ltv ⟨lctx, .base b, s⟩
    | ofBVar
        {lctx : Nat → LamSort} (n : Nat) :
      LamWF ltv ⟨lctx, .bvar n, lctx n⟩
    | ofLam
        {lctx : Nat → LamSort}
        {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
        (H : LamWF ltv ⟨pushLCtx argTy lctx, body, bodyTy⟩) :
      LamWF ltv ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
    | ofApp
        {lctx : Nat → LamSort}
        (argTy : LamSort) {resTy : LamSort}
        {fn : LamTerm} {arg : LamTerm}
        (HFn : LamWF ltv ⟨lctx, fn, .func argTy resTy⟩)
        (HArg : LamWF ltv ⟨lctx, arg, argTy⟩) :
      LamWF ltv ⟨lctx, .app argTy fn arg, resTy⟩

  def LamTerm.mapBVarAt (idx : Nat) (f : Nat → Nat) (t : LamTerm) : LamTerm :=
    match t with
    | .atom n       => .atom n
    | .etom n       => .etom n
    | .base b       => .base b
    | .bvar n       => .bvar n
    | .lam s t      => .lam s (t.mapBVarAt (.succ idx) f)
    | .app s fn arg => .app s (fn.mapBVarAt idx f) (arg.mapBVarAt idx f)

  def LamWF.fromMapBVarAtAux
    (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
    (hRTerm : rterm' = rterm.mapBVarAt idx f)
    (HWF : LamWF lamVarTy ⟨lctx', rterm', rty⟩) : LamWF lamVarTy ⟨lctx, rterm, rty⟩ :=
    match rterm with
    | .atom n =>
      match HWF with
      | .ofAtom _ => by rw [LamTerm.atom.inj hRTerm]; apply ofAtom
    | .etom n =>
      match HWF with
      | .ofEtom _ => sorry
    | .base b =>
      match HWF with
      | .ofBase _ => sorry
    | .bvar n =>
      match HWF with
      | .ofBVar _ => sorry
    | .lam argTy body =>
      match HWF with
      | .ofLam bodyTy wfBody => sorry
    | .app argTy' fn arg =>
      match HWF with
      | .ofApp _ HFn HArg => sorry

  #check Slow.LamWF.fromMapBVarAtAux.match_5

  -- Issue and workaround
  def LamWF.fromMapBVarAtAux₂
    (idx : Nat) {lamVarTy lctx} (rterm : LamTerm)
    (hRTerm : rterm' = rterm.mapBVarAt idx f)
    (HWF : LamWF lamVarTy ⟨lctx', rterm', rty⟩) : LamWF lamVarTy ⟨lctx, rterm, rty⟩ := by
    revert hRTerm
    match HWF with
    | .ofAtom _ => sorry
    | .ofEtom _ => sorry
    | .ofBase _ => sorry
    | .ofBVar _ =>
      intro hRTerm
      match rterm, hRTerm with
      | .bvar n, Eq.refl _ => sorry
      -- There exists a workaround
      -- match rterm, hRTerm with
      -- | .bvar n, h =>
      --   rw [LamTerm.bvar.inj h]; sorry
    | .ofLam bodyTy wfBody => sorry
    | .ofApp _ HFn HArg => sorry

end Slow


-- If the target contains `match h : term with` where `term` is not
--   a free variable, and we execute the tactic
--   `cases term / cases h : term / match h : term with`,
--   we get `tactic 'generalize' failed, result is not type correct`
namespace EquationalMatch

  axiom p : Nat → Type
  
  def match1 (h₁ : p n) (h₂ : p m) : p m :=
    match h : m.beq n with
    | true => Nat.eq_of_beq_eq_true h ▸ h₁
    | false => h₂
  
  -- tactic 'generalize' failed, result is not type correct
  theorem match1_eq (h₁ : p n) (h₂ : p m) : match1 h₁ h₂ = h₂ := by
    dsimp [match1]
    cases h : m.beq n
  
  -- As a workaround, we have to provide a lemma about `Bool.rec`,
  --   which is annoying
  theorem bool_eq_rec_false (q : Bool → Sort u)
    (c₁ : b = false → q b) (c₂ : b = true → q b) (h : b = false) :
    Bool.rec (motive := fun x => b = x → q b) c₁ c₂ b rfl = c₁ h := by
    cases b
    case false => rfl
    case true => cases h
  
  -- Now we're able to prove `match1_eq`
  theorem match1_eq' (h₁ : p n) (h₂ : p m) (hm : Nat.beq m n = false) :
    match1 h₁ h₂ = h₂ := by
    dsimp [match1, match1.match_1]
    rw [bool_eq_rec_false (p:=fun _ => p m) _ _ hm]

end EquationalMatch