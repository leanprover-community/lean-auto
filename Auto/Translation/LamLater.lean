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

namespace Auto.LamLater

open Embedding Embedding.Lam

/--
  Information about Mathlib's `Real`, recognized from the environment at the
    start of reification. Reification produces `Real` sorts and constants only
    if this information is available.
  A term-like expression `e` is reified as `.lcst (.real rc)` iff `e` is
    definitionally equal to the canonical form of `rc`, which is the corresponding
    field of `interp`. This is exactly what the kernel needs to check when
    checking the interpretation of the reified term. `index` is only used to
    select the candidates to check.
-/
structure RealInfo where
  /-- `Real` -/
  real   : Expr
  /-- `⟨0, 1, HAdd.hAdd, ⋯⟩ : RealInterpUnlifted Real`, the interpretation of the `RealConst`s -/
  interp : Expr
  /-- Canonical form and type of each `RealConst` -/
  consts : Std.HashMap RealConst (Expr × Expr)
  /--
    Head constants of the canonical forms and of their δ-unfoldings, e.g.
    `HAdd.hAdd`, `Add.add` and the (private) `Real.add` for `RealConst.add`
  -/
  index  : Std.HashMap Name (Array RealConst)

/-- All `RealConst`s, in the order of the fields of `RealInterpUnlifted` -/
private def realConsts : Array RealConst :=
  #[.zero, .one, .add, .sub, .mul, .div, .neg, .inv, .ofNat, .ofInt]

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

/-- Recognize `Real` and the canonical forms of the `RealConst`s from the environment -/
def RealInfo.init? : MetaM (Option RealInfo) := do
  if !auto.lamLater.recognize.real.get (← getOptions) then
    return .none
  let .some ci := (← getEnv).find? `Real
    | return .none
  -- `Real : Type`
  if !ci.levelParams.isEmpty || ci.type != .sort (.succ .zero) then
    trace[auto.lamLater] "{decl_name%} :: `Real` is not a type in `Type`, ignored"
    return .none
  let real := Expr.const `Real []
  let mut consts := {}
  let mut index : Std.HashMap Name (Array RealConst) := {}
  let mut fields := #[]
  for rc in realConsts do
    let e? : Option Expr ← try pure (.some (← Lam2D.interpRealConstAsUnlifted rc)) catch err => do
      trace[auto.lamLater] "{decl_name%} :: Cannot construct `{rc.reprAux}` for `Real`: {err.toMessageData}"
      pure .none
    let .some e := e?
      | return .none
    let ty ← instantiateMVars (← Meta.inferType e)
    consts := consts.insert rc (e, ty)
    fields := fields.push e
    for c in ← headChain e do
      index := index.insert c ((index.getD c #[]).push rc)
  let interp := mkAppN (.const ``RealInterpUnlifted.mk []) (#[real] ++ fields)
  trace[auto.lamLater] "Recognized `Real`. Head constants of canonical forms: {index.toList.map (fun (c, rcs) => (c, rcs.map RealConst.reprAux))}"
  return .some { real, interp, consts, index }

/--
  Reify `e` as a `RealConst` (or a numeral) if `e` is definitionally
    equal to the canonical form of the `RealConst`. See `RealInfo`
-/
def RealInfo.reifTerm? (ri : RealInfo) (e : Expr) : MetaM (Option LamTerm) := do
  let .some c := e.getAppFn.constName?
    | return .none
  let canonical (rc : RealConst) : MetaM Expr := do
    let .some (canon, _) := ri.consts.get? rc
      | throwError "{decl_name%} :: Unknown canonical form of {rc.reprAux}"
    return canon
  let isDefEqCanon (canon : Expr) : MetaM Bool :=
    Meta.withNewMCtxDepth <| Meta.isDefEqD e canon
  -- Numerals `OfNat.ofNat Real n _`
  if c == ``OfNat.ofNat then
    let #[ty, .lit (.natVal n), _] := e.getAppArgs
      | return .none
    if ty != ri.real then
      return .none
    let (canon, t) ← (do
      match n with
      | 0 => return (← canonical .zero, .base .rzero)
      | 1 => return (← canonical .one, .base .rone)
      | n => return (.app (← canonical .ofNat) (mkRawNatLit n),
                     .app (.base .nat) (.base .rofNat) (.base (.natVal n))))
    if ← isDefEqCanon canon then
      return .some t
    return .none
  let .some rcs := ri.index.get? c
    | return .none
  let ty ← instantiateMVars (← Meta.inferType e)
  for rc in rcs do
    let .some (canon, canonTy) := ri.consts.get? rc
      | continue
    if ty == canonTy && (← isDefEqCanon canon) then
      return .some (.base (.lcst (.real rc)))
  return .none

/--
  `TyVal.later : LaterType → Type u`, interpreting `Real` as `GLift Real`
    if `Real` is recognized, and as `PUnit` otherwise
-/
def laterTyValExpr (ri? : Option RealInfo) (u : Level) : Expr :=
  let realTy := match ri? with
    | .some ri => Expr.app (.const ``GLift [.succ .zero, u]) ri.real
    | .none => .const ``PUnit [.succ u]
  .app (.const ``LaterType.interp [u]) realTy

/-- `LaterVal (laterTyValExpr ri? u)`, the interpretation of the constants of later-declared types -/
def laterValExpr (ri? : Option RealInfo) (u : Level) : Expr :=
  match ri? with
  | .some ri =>
    let real := Lean.mkApp2 (.const ``RealInterpUnlifted.toRealInterp [u]) ri.real ri.interp
    Lean.mkApp2 (.const ``LaterVal.mk [u]) (laterTyValExpr ri? u) real
  | .none => .const ``LaterVal.default [u]

end Auto.LamLater
