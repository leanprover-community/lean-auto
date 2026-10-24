module

public import Lean
public import Auto.Translation.LamUtils
public import Auto.EmbedLam.LamBVarOp

public section

/-!
  Recognition of later-declared types (`LaterType`), e.g. Mathlib's `Real`,
  and of their constants during reification
-/

open Lean

initialize
  registerTraceClass `auto.lamLater

register_option auto.lamLater.recognize.real : Bool := {
  defValue := true
  descr := "Enable/Disable recognition of `Real` and its constants as interpreted sorts and constants"
}

register_option auto.lamLater.recognize.complex : Bool := {
  defValue := true
  descr := "Enable/Disable recognition of `Complex` and its constants as interpreted sorts and constants. Requires recognition of `Real`"
}

namespace Auto.Embedding.Lam

/-- All `LaterType`s, in the order of the parameters of `LaterType.interp`.
  Each `LaterType` comes after the `LaterType`s it depends on -/
def LaterType.all : Array LaterType := #[.real, .complex]

/-- The `LaterType`s mentioned by the sorts of the constants of `t` -/
def LaterType.deps : LaterType → Array LaterType
| .real    => #[]
| .complex => #[.real]

/-- The option enabling recognition of `t` -/
def LaterType.option : LaterType → Lean.Option Bool
| .real    => auto.lamLater.recognize.real
| .complex => auto.lamLater.recognize.complex

/-- Whether recognition of `t` is enabled -/
def LaterType.enabled (t : LaterType) (opts : Options) : Bool := t.option.get opts

/-- Constants of `t`, in the order of the fields of the un-lifted interpretation of `t` -/
def LaterType.consts : LaterType → Array LaterConst
| .real    => #[.zero, .one, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt,
               .le, .lt, .max, .min, .abs, .ofScientific, .floor, .ceil, .pow, .sqrt, .ofRat].map .real
| .complex => #[.zero, .one, .I, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt,
               .ofReal, .re, .im, .mk, .normSq, .conj, .norm, .pow, .ofRat].map .complex

/-- Constants of `t` interpreting the numerals `0`, `1` and `n` (as a function of `n : Nat`) -/
def LaterType.numerals : LaterType → LaterConst × LaterConst × LaterConst
| .real    => (.real .zero, .real .one, .real .ofNat)
| .complex => (.complex .zero, .complex .one, .complex .ofNat)

/--
  Forms of `t` that are recognized as terms built from the constants of `t`, e.g.
    `GE.ge Real _` as `λ x y, (.real .le) y x`. Each is a canonical form (whose
    construction may fail) and the term it is recognized as
-/
def LaterType.derivedForms : LaterType → Array (MetaM Expr × LamTerm)
| .real =>
  let real := Lam2D.interpLaterTypeAsUnlifted .real
  let s : LamSort := .base .real
  let flip (lc : LaterConst) : LamTerm := .lam s (.lam s (.app s (.app s (.base (.lcst lc)) (.bvar 0)) (.bvar 1)))
  #[(Meta.mkAppOptM ``GE.ge #[real, .none], flip (.real .le)),
    (Meta.mkAppOptM ``GT.gt #[real, .none], flip (.real .lt))]
| .complex =>
  let complex := Lam2D.interpLaterTypeAsUnlifted .complex
  #[(Meta.mkAppOptM `Star.star #[complex, .none], .base (.lcst (.complex .conj)))]

/--
  Un-lifted interpretation of the constants of `t`, given the canonical forms of the
    recognized constants of `t`. The other constants are interpreted by the corresponding
    fields of the default interpretation, which is built from `elems`, the elements of
    the types `t.deps.push t`
-/
def LaterType.mkInterp (t : LaterType) (canons : Array (Option Expr)) (elems : Array Expr) : Expr :=
  let (structName, mk, dflt) := match t with
    | .real => (``RealInterpUnlifted, ``RealInterpUnlifted.mk, ``RealInterpUnlifted.default)
    | .complex => (``ComplexInterpUnlifted, ``ComplexInterpUnlifted.intro, ``ComplexInterpUnlifted.default)
  let tys := (t.deps.push t).map Lam2D.interpLaterTypeAsUnlifted
  let dflt := mkAppN (.const dflt []) (tys ++ elems)
  mkAppN (.const mk []) (tys ++ canons.mapIdx fun i canon? => canon?.getD (.proj structName i dflt))

private def LaterConst.reprAux : LaterConst → String
| .real rc => s!"real.{rc.reprAux}"
| .complex cc => s!"complex.{cc.reprAux}"

end Auto.Embedding.Lam

namespace Auto.LamLater

open Embedding Embedding.Lam

/-- A form recognized as `term` if it is definitionally equal to `canon`, whose type is `type` -/
structure LaterForm where
  canon : Expr
  type  : Expr
  term  : LamTerm
deriving Inhabited

/--
  Later-declared types (e.g. Mathlib's `Real`) and their constants, recognized
    from the environment at the start of reification. Reification produces sorts
    and constants of a later-declared type only if it is recognized. The constants
    of a recognized later-declared type are recognized individually, and those that
    are not recognized are treated as uninterpreted atoms.
  A term-like expression `e` is reified as `.lcst lc` iff `e` is definitionally
    equal to the canonical form of `lc`, which is the corresponding field of the
    un-lifted interpretation in `interps`. This is exactly what the kernel needs
    to check when checking the interpretation of the reified term. `index` is
    only used to select the candidates to check.
-/
structure LaterInfo where
  /-- The recognized later-declared types, e.g. `real ↦ Real` -/
  types   : Std.HashMap LaterType Expr           := {}
  /--
    An element of each recognized later-declared type, used to interpret
    the constants that are not recognized
  -/
  elems   : Std.HashMap LaterType Expr           := {}
  /--
    Un-lifted interpretation of the constants of each recognized later-declared
    type, e.g. `⟨0, 1, HAdd.hAdd, ⋯⟩ : RealInterpUnlifted Real`
  -/
  interps : Std.HashMap LaterType Expr           := {}
  /-- Canonical form and type of each recognized constant -/
  consts  : Std.HashMap LaterConst (Expr × Expr) := {}
  /--
    Recognized forms, indexed by the head constants of their canonical forms and of the
    δ-unfoldings of the canonical forms, e.g. `HAdd.hAdd`, `Add.add` and the (private)
    `Real.add` for `.real .add`
  -/
  index   : Std.HashMap Name (Array LaterForm)   := {}
  /--
    Head constants of the canonical forms `f c` whose last argument `c` is explicit,
    e.g. `DFunLike.coe` for `DFunLike.coe Complex.normSq`. During reification, `f` and
    `c` are separate term-like expressions, so applications `f c` with these heads are
    also checked by `reifTerm?`
  -/
  appHeads : Std.HashSet Name                    := {}
deriving Inhabited

/-- The recognized later-declared type whose Lean type is `e` -/
def LaterInfo.laterType? (li : LaterInfo) (e : Expr) : Option LaterType :=
  li.types.fold (fun acc t ty => if ty == e then .some t else acc) .none

/--
  Head constants of `e` and its δ-unfoldings, as long as `e x₁ ⋯ xₙ` unfolds to
    `c a₁ ⋯ aₖ x₁ ⋯ xₙ` (where `x₁ ⋯ xₙ` are the arguments of `e`
    and `a₁ ⋯ aₖ` does not contain `x₁ ⋯ xₙ`)
-/
private def headChain (e : Expr) (fuel : Nat := 16) : MetaM (Array Name) := Meta.withDefault do
  Meta.forallTelescope (← Meta.inferType e) fun xs _ => do
    let mut body := mkAppN e xs
    let mut ret := #[]
    for _ in [0:fuel] do
      body ← Meta.whnfCore body
      let .some c := body.getAppFn.constName?
        | break
      let args := body.getAppArgs
      if args.size < xs.size then
        break
      let n := args.size - xs.size
      if args[n:].toArray != xs || args[:n].toArray.any (fun a => xs.any (fun x => a.containsFVar x.fvarId!)) then
        break
      ret := ret.push c
      if let .some body' ← Meta.unfoldProjInst? body then
        body := body'
      else if let .some body' ← Meta.unfoldDefinition? body then
        body := body'
      else
        break
    return ret

/--
  The canonical form of `lc`, if it can be constructed and its type is
    the un-lifted interpretation of the sort of `lc`
-/
private def LaterConst.canonical? (lc : LaterConst) : MetaM (Option Expr) := do
  let canon? : Option Expr ← try pure (.some (← Lam2D.interpLaterConstAsUnlifted lc)) catch err => do
    trace[auto.lamLater] "{decl_name%} :: Cannot construct `{lc.reprAux}`: {err.toMessageData}"
    pure .none
  let .some canon := canon?
    | return .none
  let expected ← Lam2D.interpLamSortAsUnlifted {} lc.lamCheck
  if !(← Meta.withNewMCtxDepth <| Meta.isDefEq (← Meta.inferType canon) expected) then
    trace[auto.lamLater] "{decl_name%} :: The canonical form `{canon}` of `{lc.reprAux}` is not of type `{expected}`, ignored"
    return .none
  return .some canon

/-- Recognize `t` and the canonical forms of its constants from the environment -/
private def LaterInfo.add (li : LaterInfo) (t : LaterType) : MetaM LaterInfo := do
  if !t.enabled (← getOptions) then
    return li
  let ty := Lam2D.interpLaterTypeAsUnlifted t
  let .some ci := (← getEnv).find? ty.constName!
    | return li
  -- `ty : Type`
  if !ci.levelParams.isEmpty || ci.type != .sort (.succ .zero) then
    trace[auto.lamLater] "{decl_name%} :: `{ty}` is not a type in `Type`, ignored"
    return li
  if let .some dep := t.deps.find? (!li.types.contains ·) then
    let depTy := Lam2D.interpLaterTypeAsUnlifted dep
    throwError "{decl_name%} :: Recognition of `{ty}` requires `{depTy}` to be recognized, but `{depTy}` is not recognized. Set `{t.option.name}` to `false` to disable recognition of `{ty}`"
  -- Each constant is recognized individually
  let canons ← t.consts.mapM LaterConst.canonical?
  -- An element of `ty`, used to interpret the constants that are not recognized
  let (zero, _, _) := t.numerals
  let elem? : Option Expr ← match (t.consts.zip canons).findSome? (fun (lc, c?) => if lc == zero then c? else .none) with
    | .some e => pure (.some e)
    | .none => try pure (.some (← Meta.mkDefault ty)) catch _ => pure .none
  let .some elem := elem?
    | trace[auto.lamLater] "{decl_name%} :: Cannot find an element of `{ty}`, ignored"
      return li
  let mut li := { li with types := li.types.insert t ty, elems := li.elems.insert t elem }
  let elems := (t.deps.push t).filterMap li.elems.get?
  li := { li with interps := li.interps.insert t (t.mkInterp canons elems) }
  let mut forms := #[]
  let mut missing := #[]
  for (lc, e?) in t.consts.zip canons do
    if let .some e := e? then
      let eTy ← instantiateMVars (← Meta.inferType e)
      li := { li with consts := li.consts.insert lc (e, eTy) }
      forms := forms.push (⟨e, eTy, .base (.lcst lc)⟩, lc.reprAux)
    else
      missing := missing.push lc.reprAux
  for (mkCanon, term) in t.derivedForms do
    -- Derived forms are recognized only if the constants they mention are recognized
    if let .some lc := (LamExportUtils.collectLamTermLaterConsts term).toArray.find? (!li.consts.contains ·) then
      trace[auto.lamLater] "{decl_name%} :: `{lc.reprAux}` is not recognized, so `{toString term}` is not recognized"
      continue
    let e? : Option Expr ← try pure (.some (← mkCanon)) catch err => do
      trace[auto.lamLater] "{decl_name%} :: Cannot construct the canonical form of `{toString term}` for `{ty}`: {err.toMessageData}"
      pure .none
    let .some e := e?
      | continue
    -- The canonical form must be definitionally equal to the interpretation of `term`
    if !(← Meta.withNewMCtxDepth <| Meta.isDefEqD e (← Lam2D.interpLamTermAsUnlifted {} {} {} 0 term)) then
      trace[auto.lamLater] "{decl_name%} :: `{e}` is not definitionally equal to the interpretation of `{toString term}`, ignored"
      continue
    forms := forms.push (⟨e, ← instantiateMVars (← Meta.inferType e), term⟩, toString term)
  let mut heads := #[]
  for (form, name) in forms do
    for c in ← headChain form.canon do
      li := { li with index := li.index.insert c ((li.index.getD c #[]).push form) }
      heads := heads.push (c, name)
    if let .app f _ := form.canon then
      if let .forallE _ _ _ .default ← Meta.whnfD (← Meta.inferType f) then
        if let .some c := form.canon.getAppFn.constName? then
          li := { li with appHeads := li.appHeads.insert c }
  trace[auto.lamLater] "Recognized `{ty}`. Constants that are not recognized: {missing}. Head constants of canonical forms: {heads}"
  return li

/-- Recognize all later-declared types and their constants from the environment -/
def LaterInfo.init : MetaM LaterInfo :=
  LaterType.all.foldlM LaterInfo.add {}

/--
  Reify `e` as a constant of a recognized later-declared type (or a numeral, or a derived
    form) if `e` is definitionally equal to the corresponding canonical form. See `LaterInfo`
-/
def LaterInfo.reifTerm? (li : LaterInfo) (e : Expr) : MetaM (Option LamTerm) := do
  let .some c := e.getAppFn.constName?
    | return .none
  let canonical? (lc : LaterConst) : Option Expr := (li.consts.get? lc).map (·.1)
  let isDefEqCanon (canon : Expr) : MetaM Bool :=
    Meta.withNewMCtxDepth <| Meta.isDefEqD e canon
  -- Numerals `OfNat.ofNat ty n _`, where `ty` is a recognized later-declared type
  if c == ``OfNat.ofNat then
    let #[ty, .lit (.natVal n), _] := e.getAppArgs
      | return .none
    let .some t := li.laterType? ty
      | return .none
    let (zero, one, ofNat) := t.numerals
    let canonRes? : Option (Expr × LamTerm) := match n with
      | 0 => (canonical? zero).map (·, .base (.lcst zero))
      | 1 => (canonical? one).map (·, .base (.lcst one))
      | n => (canonical? ofNat).map fun canon =>
        (.app canon (mkRawNatLit n), .app (.base .nat) (.base (.lcst ofNat)) (.base (.natVal n)))
    let .some (canon, res) := canonRes?
      | return .none
    if ← isDefEqCanon canon then
      return .some res
    return .none
  let .some forms := li.index.get? c
    | return .none
  let ty ← instantiateMVars (← Meta.inferType e)
  for form in forms do
    if ty == form.type && (← isDefEqCanon form.canon) then
      return .some form.term
  return .none

/--
  `TyVal.later : LaterType → Type u`, interpreting each recognized later-declared
    type `ty` as `GLift ty`, and the others as `PUnit`
-/
def LaterInfo.laterTyValExpr (li : LaterInfo) (u : Level) : Expr :=
  mkAppN (.const ``LaterType.interp [u]) (LaterType.all.map fun t =>
    match li.types.get? t with
    | .some ty => .app (.const ``GLift [.succ .zero, u]) ty
    | .none => .const ``PUnit [.succ u])

/--
  `LaterVal (li.laterTyValExpr u)`, the interpretation of the constants of later-declared types.
  The constants of a later-declared type that is not recognized are given a default interpretation
-/
def LaterInfo.laterValExpr (li : LaterInfo) (u : Level) : Expr :=
  let realTy := Lam2D.interpLaterTypeAsUnlifted .real
  let complexTy := Lam2D.interpLaterTypeAsUnlifted .complex
  let real := match li.interps.get? .real with
    | .some ri => Lean.mkApp2 (.const ``RealInterpUnlifted.toRealInterp [u]) realTy ri
    | .none => .const ``RealInterp.default [u]
  let complex := match li.interps.get? .complex with
    | .some ci => Lean.mkApp3 (.const ``ComplexInterpUnlifted.toComplexInterp [u]) realTy complexTy ci
    | .none =>
      -- `ComplexInterp.default` needs an element of the interpretation of `Real`
      let laterTy := li.laterTyValExpr u
      let realLiftedTy := Expr.app laterTy (.const ``LaterType.real [])
      let realZero := Lean.mkApp2 (.const ``RealInterp.zero [u]) realLiftedTy real
      Lean.mkApp2 (.const ``ComplexInterp.default [u]) realLiftedTy realZero
  Lean.mkApp3 (.const ``LaterVal.mk [u]) (li.laterTyValExpr u) real complex

end Auto.LamLater
