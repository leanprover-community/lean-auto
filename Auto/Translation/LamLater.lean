module

public import Lean
public import Auto.Translation.LamUtils

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
| .real    => #[.zero, .one, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt].map .real
| .complex => #[.zero, .one, .I, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt,
               .ofReal, .re, .im, .mk].map .complex

/-- Constants of `t` interpreting the numerals `0`, `1` and `n` (as a function of `n : Nat`) -/
def LaterType.numerals : LaterType → LaterConst × LaterConst × LaterConst
| .real    => (.real .zero, .real .one, .real .ofNat)
| .complex => (.complex .zero, .complex .one, .complex .ofNat)

/-- Un-lifted interpretation of the constants of `t`, given their canonical forms -/
def LaterType.mkInterp (t : LaterType) (canons : Array Expr) : Expr :=
  match t with
  | .real => mkAppN (.const ``RealInterpUnlifted.mk []) (#[Lam2D.interpLaterTypeAsUnlifted .real] ++ canons)
  | .complex => mkAppN (.const ``ComplexInterpUnlifted.intro [])
    (#[Lam2D.interpLaterTypeAsUnlifted .real, Lam2D.interpLaterTypeAsUnlifted .complex] ++ canons)

private def LaterConst.reprAux : LaterConst → String
| .real rc => s!"real.{rc.reprAux}"
| .complex cc => s!"complex.{cc.reprAux}"

end Auto.Embedding.Lam

namespace Auto.LamLater

open Embedding Embedding.Lam

/--
  Later-declared types (e.g. Mathlib's `Real`) and their constants, recognized
    from the environment at the start of reification. Reification produces sorts
    and constants of a later-declared type only if it is recognized.
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
    Un-lifted interpretation of the constants of each recognized later-declared
    type, e.g. `⟨0, 1, HAdd.hAdd, ⋯⟩ : RealInterpUnlifted Real`
  -/
  interps : Std.HashMap LaterType Expr           := {}
  /-- Canonical form and type of each constant of the recognized later-declared types -/
  consts  : Std.HashMap LaterConst (Expr × Expr) := {}
  /--
    Head constants of the canonical forms and of their δ-unfoldings, e.g.
    `HAdd.hAdd`, `Add.add` and the (private) `Real.add` for `.real .add`
  -/
  index   : Std.HashMap Name (Array LaterConst)  := {}
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
  let mut canons := #[]
  for lc in t.consts do
    let e? : Option Expr ← try pure (.some (← Lam2D.interpLaterConstAsUnlifted lc)) catch err => do
      trace[auto.lamLater] "{decl_name%} :: Cannot construct `{lc.reprAux}` for `{ty}`: {err.toMessageData}"
      pure .none
    let .some e := e?
      | return li
    canons := canons.push e
  let mut li := { li with types := li.types.insert t ty, interps := li.interps.insert t (t.mkInterp canons) }
  let mut heads := #[]
  for (lc, e) in t.consts.zip canons do
    li := { li with consts := li.consts.insert lc (e, ← instantiateMVars (← Meta.inferType e)) }
    for c in ← headChain e do
      li := { li with index := li.index.insert c ((li.index.getD c #[]).push lc) }
      heads := heads.push (c, lc.reprAux)
  trace[auto.lamLater] "Recognized `{ty}`. Head constants of canonical forms: {heads}"
  return li

/-- Recognize all later-declared types and their constants from the environment -/
def LaterInfo.init : MetaM LaterInfo :=
  LaterType.all.foldlM LaterInfo.add {}

/--
  Reify `e` as a constant of a recognized later-declared type (or a numeral) if `e` is
    definitionally equal to the canonical form of the constant. See `LaterInfo`
-/
def LaterInfo.reifTerm? (li : LaterInfo) (e : Expr) : MetaM (Option LamTerm) := do
  let .some c := e.getAppFn.constName?
    | return .none
  let canonical (lc : LaterConst) : MetaM Expr := do
    let .some (canon, _) := li.consts.get? lc
      | throwError "{decl_name%} :: Unknown canonical form of {lc.reprAux}"
    return canon
  let isDefEqCanon (canon : Expr) : MetaM Bool :=
    Meta.withNewMCtxDepth <| Meta.isDefEqD e canon
  -- Numerals `OfNat.ofNat ty n _`, where `ty` is a recognized later-declared type
  if c == ``OfNat.ofNat then
    let #[ty, .lit (.natVal n), _] := e.getAppArgs
      | return .none
    let .some t := li.laterType? ty
      | return .none
    let (zero, one, ofNat) := t.numerals
    let (canon, res) ← (do
      match n with
      | 0 => return (← canonical zero, .base (.lcst zero))
      | 1 => return (← canonical one, .base (.lcst one))
      | n => return (.app (← canonical ofNat) (mkRawNatLit n),
                     .app (.base .nat) (.base (.lcst ofNat)) (.base (.natVal n))))
    if ← isDefEqCanon canon then
      return .some res
    return .none
  let .some lcs := li.index.get? c
    | return .none
  let ty ← instantiateMVars (← Meta.inferType e)
  for lc in lcs do
    let .some (canon, canonTy) := li.consts.get? lc
      | continue
    if ty == canonTy && (← isDefEqCanon canon) then
      return .some (.base (.lcst lc))
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
