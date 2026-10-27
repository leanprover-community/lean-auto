module

public import Lean
public import Auto.Translation.LamUtils
public import Auto.EmbedLam.LamBVarOp
public import Auto.EmbedLam.LamLaterSpec

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

register_option auto.lamLater.spec : Bool := {
  defValue := true
  descr := "Enable/Disable construction of proofs that the recognized constants of later-declared types satisfy their characterizations (e.g. `RealInterpUnlifted.CoreSpec` and `RealInterpUnlifted.ExtSpec`), from theorems in the environment. The SMT translation only interprets later-declared types and constants whose characterizations are proved"
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
  let (structName, mk, dflt, lvls) := match t with
    | .real => (``RealInterpUnlifted, ``RealInterpUnlifted.mk, ``RealInterpUnlifted.default, [Level.zero])
    | .complex => (``ComplexInterpUnlifted, ``ComplexInterpUnlifted.intro, ``ComplexInterpUnlifted.default, [Level.zero])
  let tys := (t.deps.push t).map Lam2D.interpLaterTypeAsUnlifted
  let dflt := mkAppN (.const dflt lvls) (tys ++ elems)
  mkAppN (.const mk lvls) (tys ++ canons.mapIdx fun i canon? => canon?.getD (.proj structName i dflt))

/--
  The structures characterizing the constants of `t`, if any. The first one characterizes
    the core constants of `t` as a whole, and takes the types `t.deps.push t` and the
    un-lifted interpretation of the constants of `t` as parameters. The second one has an
    optional characterization of each of the other constants of `t`, and also takes the
    un-lifted interpretations of the constants of `t.deps` (before that of `t`)
-/
def LaterType.specs : LaterType → Option (Name × Name)
| .real    => .some (``RealInterpUnlifted.CoreSpec, ``RealInterpUnlifted.ExtSpec)
| .complex => .some (``ComplexInterpUnlifted.CoreSpec, ``ComplexInterpUnlifted.ExtSpec)

/-- The field of the structures characterizing the constants of `lc`'s type (see `LaterType.specs`) for `lc` -/
def LaterConst.specField : LaterConst → Name
| .real rc => .mkSimple rc.reprAux
| .complex cc => .mkSimple cc.reprAux

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
    Proof of the characterization of the core constants of each recognized later-declared
    type (see `LaterType.specs`), if it is proved from the theorems in the environment,
    e.g. `⟨add_assoc, ⋯⟩ : RealInterpUnlifted.CoreSpec ri`. Only constructed if
    `auto.lamLater.spec` is enabled
  -/
  coreSpecs : Std.HashMap LaterType Expr         := {}
  /--
    Characterizations of the other constants of each recognized later-declared type,
    each with a proof if it is proved from the theorems in the environment, e.g.
    `⟨some ⟨sub_eq_add_neg⟩, none, ⋯⟩ : RealInterpUnlifted.ExtSpec ri`. Only
    constructed if `auto.lamLater.spec` is enabled
  -/
  extSpecs : Std.HashMap LaterType Expr          := {}
  /-- The constants whose characterizations in `extSpecs` have proofs -/
  extAvail : Std.HashSet LaterConst              := {}
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

/-- `intros; apply n`, closing the remaining goals by assumption -/
private def byApply (n : Name) : CoreM Term :=
  `(by intros; apply $(mkIdent n) <;> try assumption)

/--
  Candidate proofs of the field `field` of the structures characterizing the constants of `t`
    (see `LaterType.specs`). Theorems are referred to by name because Mathlib is not available
    when `lean-auto` is compiled. Each candidate is elaborated against the statement of the
    field, and the first one that succeeds is used
-/
private def LaterType.specProofs (t : LaterType) (field : Name) : CoreM (Array Term) := do
  let thms (ns : List Name) : CoreM (Array Term) := ns.toArray.mapM byApply
  let conj (ns : List Name) : CoreM (Array Term) := do
    let ts ← ns.toArray.mapM byApply
    return #[← `(⟨$ts,*⟩)]
  match t, field with
  -- `RealInterpUnlifted.CoreSpec`
  | .real, `add_assoc       => thms [`add_assoc]
  | .real, `add_comm        => thms [`add_comm]
  | .real, `zero_add        => thms [`zero_add]
  | .real, `add_neg_cancel  => thms [`add_neg_cancel, `add_right_neg]
  | .real, `mul_assoc       => thms [`mul_assoc]
  | .real, `mul_comm        => thms [`mul_comm]
  | .real, `one_mul         => thms [`one_mul]
  | .real, `mul_add         => thms [`mul_add, `left_distrib]
  | .real, `zero_ne_one     => thms [`zero_ne_one]
  | .real, `mul_inv_cancel  => thms [`mul_inv_cancel₀]
  | .real, `inv_zero        => thms [`inv_zero]
  | .real, `le_refl         => thms [`le_refl]
  | .real, `le_trans        => thms [`le_trans]
  | .real, `le_antisymm     => thms [`le_antisymm]
  | .real, `le_total        => thms [`le_total]
  | .real, `add_le_add_left =>
    -- The meanings of `add_le_add_left` and `add_le_add_right` have been swapped in Mathlib
    return #[← `(fun _ _ z h => $(mkIdent `add_le_add) ($(mkIdent `le_refl) z) h)] ++
      (← thms [`add_le_add_left, `add_le_add_right])
  | .real, `mul_nonneg      => thms [`mul_nonneg, `Left.mul_nonneg]
  | .real, `complete        => return #[← `(fun S => @$(mkIdent `Real.exists_isLUB) S)]
  -- `RealInterpUnlifted.ExtSpec`
  | .real, `sub             => thms [`sub_eq_add_neg]
  | .real, `div             => thms [`div_eq_mul_inv]
  | .real, `ofNat           => conj [`Nat.cast_zero, `Nat.cast_succ]
  | .real, `ofInt           => conj [`Int.cast_one, `Int.cast_add]
  | .real, `lt              => thms [`lt_iff_le_not_ge, `lt_iff_le_not_le]
  | .real, `max             => conj [`max_eq_left, `max_eq_right]
  | .real, `min             => conj [`min_eq_left, `min_eq_right]
  | .real, `abs             => conj [`abs_of_nonneg, `abs_of_nonpos]
  | .real, `ofScientific    => return #[← `(fun m s e => ($(mkIdent `Rat.cast_ofScientific) m s e).symm)]
  | .real, `floor           => conj [`Int.floor_le, `Int.lt_floor_add_one]
  | .real, `ceil            => conj [`Int.le_ceil, `Int.ceil_lt_add_one]
  | .real, `pow             => conj [`pow_zero, `pow_succ]
  | .real, `sqrt            => conj [`Real.sqrt_nonneg, `Real.mul_self_sqrt, `Real.sqrt_eq_zero_of_nonpos]
  | .real, `ofRat           => conj [`Rat.cast_one, `Rat.cast_add, `Rat.cast_mul]
  -- `ComplexInterpUnlifted.CoreSpec`. These hold by definition if `Complex` is a structure
  | .complex, `re_mk        => return #[← `(fun _ _ => rfl)]
  | .complex, `im_mk        => return #[← `(fun _ _ => rfl)]
  | .complex, `mk_re_im     => return (← thms [`Complex.eta]) ++ #[← `(fun _ => rfl)]
  -- `ComplexInterpUnlifted.ExtSpec`
  | .complex, `zero         => conj [`Complex.zero_re, `Complex.zero_im]
  | .complex, `one          => conj [`Complex.one_re, `Complex.one_im]
  | .complex, `I            => conj [`Complex.I_re, `Complex.I_im]
  | .complex, `add          => conj [`Complex.add_re, `Complex.add_im]
  | .complex, `sub          => conj [`Complex.sub_re, `Complex.sub_im]
  | .complex, `mul          => conj [`Complex.mul_re, `Complex.mul_im]
  | .complex, `div          => thms [`div_eq_mul_inv]
  | .complex, `neg          => conj [`Complex.neg_re, `Complex.neg_im]
  | .complex, `inv          => conj [`Complex.inv_re, `Complex.inv_im]
  | .complex, `ofNat        => conj [`Complex.natCast_re, `Complex.natCast_im]
  | .complex, `ofInt        => conj [`Complex.intCast_re, `Complex.intCast_im]
  | .complex, `ofReal       => conj [`Complex.ofReal_re, `Complex.ofReal_im]
  | .complex, `normSq       => thms [`Complex.normSq_apply]
  | .complex, `conj         => conj [`Complex.conj_re, `Complex.conj_im]
  | .complex, `norm         => thms [`Complex.norm_def]
  | .complex, `pow          => conj [`pow_zero, `pow_succ]
  | .complex, `ofRat        => conj [`Complex.ratCast_re, `Complex.ratCast_im]
  | _, _ => return #[]

/-- Elaborate `stx` against `type`, returning a proof without metavariables -/
private def elabProof (stx : Term) (type : Expr) : MetaM Expr := withoutModifyingState do
  Core.resetMessageLog
  let e ← Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry do
    let e ← Elab.Term.elabTermEnsuringType stx type
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if (← Core.getMessageLog).hasErrors then
    throwError "{decl_name%} :: Errors: {(← Core.getMessageLog).toList.map (·.data)}"
  if e.hasMVar || e.hasSyntheticSorry then
    throwError "{decl_name%} :: The proof `{e}` is incomplete"
  return e

/-- Reduce the projections of the structures `interpNames` applied to their constructors -/
private def reduceInterpProjs (interpNames : Array Name) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .some e' ← Meta.reduceProjOf? e interpNames.contains
      | return .continue
    return .visit (← Meta.whnfCore e'))

/--
  The constructor of the structure `structName` applied to `params`, and the fields of the
    structure with their statements. Each statement is also given with the projections of
    the structures `interpNames` reduced, e.g. `(RealInterpUnlifted.mk _ ⋯).add x y` to the
    canonical form `HAdd.hAdd x y`
-/
private def specFields (structName : Name) (interpNames : Array Name) (params : Array Expr) :
  MetaM (Expr × Array (Name × Expr × Expr)) := do
  let ctor := getStructureCtor (← getEnv) structName
  -- The interpretations of later-declared types are in `Type`
  let lvls := ctor.levelParams.map fun _ => .zero
  let ctorTy := ctor.type.instantiateLevelParams ctor.levelParams lvls
  -- The fields of the structure do not depend on each other
  let fields ← Meta.forallTelescope (← Meta.instantiateForall ctorTy params) fun xs _ =>
    xs.mapM fun x => do
      let stmt ← Meta.inferType x
      return (← x.fvarId!.getUserName, stmt, ← reduceInterpProjs interpNames stmt)
  return (.const ctor.name lvls, fields)

/--
  Prove the structures characterizing the constants of `t` (see `LaterType.specs`)
    from the theorems in the environment, given the un-lifted interpretation `interp`
    of the constants of `t`
-/
private def LaterInfo.addSpecs (li : LaterInfo) (t : LaterType) (interp : Expr) : MetaM LaterInfo := do
  let .some (coreName, extName) := t.specs
    | return li
  let ty := Lam2D.interpLaterTypeAsUnlifted t
  let depInterps ← t.deps.mapM fun dep => do
    let .some depInterp := li.interps.get? dep
      | throwError "{decl_name%} :: The interpretation of {dep} is unknown"
    return depInterp
  let interpNames ← (depInterps.push interp).mapM fun interp => do
    let .some interpName := (← Meta.inferType interp).getAppFn.constName?
      | throwError "{decl_name%} :: Unexpected interpretation {interp}"
    return interpName
  let tys := (t.deps.push t).map Lam2D.interpLaterTypeAsUnlifted
  let coreParams := tys.push interp
  let extParams := tys ++ depInterps |>.push interp
  let prove (field : Name) (stmt : Expr) : MetaM (Option Expr) := do
    for stx in ← LaterType.specProofs t field do
      try
        return .some (← elabProof stx stmt)
      catch err =>
        trace[auto.lamLater] "{decl_name%} :: `{stx}` does not prove `{field}` for `{ty}`: {err.toMessageData}"
    return .none
  -- A characterization is only made available if the constants it mentions are recognized,
  --   so that its translation by `Lam2D` agrees with the valuation
  let unrecognized (spec : LamTerm) : List String :=
    (LamExportUtils.collectLamTermLaterConsts spec).toList.filter (!li.consts.contains ·) |>.map (·.reprAux)
  let mut li := li
  -- The core constants, as a whole
  let (coreCtor, coreFields) ← specFields coreName interpNames coreParams
  let coreUnrecognized := unrecognized t.coreSpec
  let mut coreProofs := #[]
  let mut coreFailed := #[]
  if coreUnrecognized.isEmpty then
    for (field, _, stmt) in coreFields do
      match ← prove field stmt with
      | .some proof => coreProofs := coreProofs.push proof
      | .none => coreFailed := coreFailed.push field
    if coreFailed.isEmpty then
      li := { li with coreSpecs := li.coreSpecs.insert t (mkAppN coreCtor (coreParams ++ coreProofs)) }
  -- The other constants, each with an optional proof
  let (extCtor, extFields) ← specFields extName interpNames extParams
  let mut extArgs := #[]
  let mut extFailed := #[]
  let mut extUnrecognized := #[]
  for (field, stmt, _) in extFields do
    let .app (.const ``Option optLvls) plift@(.app (.const ``PLift pliftLvls) p) := stmt
      | throwError "{decl_name%} :: Field `{field}` of `{extName}` is not of the form `Option (PLift _)`"
    let .some lc := t.consts.find? (·.specField == field)
      | throwError "{decl_name%} :: Field `{field}` of `{extName}` does not correspond to a constant of `{ty}`"
    let noneArg := mkApp (.const ``Option.none optLvls) plift
    if !(unrecognized lc.extSpec).isEmpty then
      extArgs := extArgs.push noneArg
      extUnrecognized := extUnrecognized.push field
      continue
    -- `p` is e.g. `ri.extProp rc`
    let reducedP ← reduceInterpProjs interpNames (← Meta.whnfD p)
    if let .some proof ← prove field reducedP then
      let proof := mkApp2 (.const ``PLift.up pliftLvls) p proof
      extArgs := extArgs.push (mkApp2 (.const ``Option.some optLvls) plift proof)
      li := { li with extAvail := li.extAvail.insert lc }
    else
      extArgs := extArgs.push noneArg
      extFailed := extFailed.push field
  li := { li with extSpecs := li.extSpecs.insert t (mkAppN extCtor (extParams ++ extArgs)) }
  let coreMsg :=
    if !coreUnrecognized.isEmpty then m!"not available, mentions constants that are not recognized: {coreUnrecognized}"
    else if coreFailed.isEmpty then m!"proved"
    else m!"not proved, failed: {coreFailed.toList}"
  trace[auto.lamLater] "Characterizations of `{ty}`: core constants {coreMsg}; other constants not proved: {extFailed.toList}; other constants whose characterizations mention constants that are not recognized: {extUnrecognized.toList}"
  return li

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
  let interp := t.mkInterp canons elems
  li := { li with interps := li.interps.insert t interp }
  let mut forms := #[]
  let mut missing := #[]
  for (lc, e?) in t.consts.zip canons do
    if let .some e := e? then
      let eTy ← instantiateMVars (← Meta.inferType e)
      li := { li with consts := li.consts.insert lc (e, eTy) }
      forms := forms.push (⟨e, eTy, .base (.lcst lc)⟩, lc.reprAux)
    else
      missing := missing.push lc.reprAux
  -- After the constants are recognized, see `LaterInfo.addSpecs`
  if auto.lamLater.spec.get (← getOptions) then
    li ← li.addSpecs t interp
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
  -- Characterizations of the constants of `Real`
  let laterRealTy := Expr.app (li.laterTyValExpr u) (.const ``LaterType.real [])
  let realLowered := Lean.mkApp2 (.const ``RealInterp.lower [u]) laterRealTy real
  let coreSpecTy := Lean.mkApp2 (.const ``RealInterpUnlifted.CoreSpec [u]) laterRealTy realLowered
  let coreOptTy := Expr.app (.const ``PLift [.zero]) coreSpecTy
  let realCore := match li.interps.get? .real, li.coreSpecs.get? .real with
    | .some ri, .some h =>
      let h := Lean.mkApp3 (.const ``RealInterpUnlifted.CoreSpec.toRealInterp [u]) realTy ri h
      Lean.mkApp2 (.const ``Option.some [.zero]) coreOptTy (Lean.mkApp2 (.const ``PLift.up [.zero]) coreSpecTy h)
    | _, _ => Expr.app (.const ``Option.none [.zero]) coreOptTy
  let realExt := match li.interps.get? .real, li.extSpecs.get? .real with
    | .some ri, .some e => Lean.mkApp3 (.const ``RealInterpUnlifted.ExtSpec.toRealInterp [u]) realTy ri e
    | _, _ => Lean.mkApp2 (.const ``RealInterpUnlifted.ExtSpec.none [u]) laterRealTy realLowered
  -- Characterizations of the constants of `Complex`
  let laterComplexTy := Expr.app (li.laterTyValExpr u) (.const ``LaterType.complex [])
  let complexLowered := Lean.mkApp3 (.const ``ComplexInterp.lower [u]) laterRealTy laterComplexTy complex
  let complexCoreSpecTy :=
    Lean.mkApp3 (.const ``ComplexInterpUnlifted.CoreSpec [u]) laterRealTy laterComplexTy complexLowered
  let complexCoreOptTy := Expr.app (.const ``PLift [.zero]) complexCoreSpecTy
  let complexCore := match li.interps.get? .complex, li.coreSpecs.get? .complex with
    | .some ci, .some h =>
      let h := Lean.mkApp4 (.const ``ComplexInterpUnlifted.CoreSpec.toComplexInterp [u]) realTy complexTy ci h
      Lean.mkApp2 (.const ``Option.some [.zero]) complexCoreOptTy
        (Lean.mkApp2 (.const ``PLift.up [.zero]) complexCoreSpecTy h)
    | _, _ => Expr.app (.const ``Option.none [.zero]) complexCoreOptTy
  let complexExt := match li.interps.get? .real, li.interps.get? .complex, li.extSpecs.get? .complex with
    | .some ri, .some ci, .some e =>
      Lean.mkApp5 (.const ``ComplexInterpUnlifted.ExtSpec.toComplexInterp [u]) realTy complexTy ri ci e
    | _, _, _ =>
      Lean.mkApp4 (.const ``ComplexInterpUnlifted.ExtSpec.none [u]) laterRealTy laterComplexTy realLowered complexLowered
  mkAppN (.const ``LaterVal.mk [u])
    #[li.laterTyValExpr u, real, complex, realCore, realExt, complexCore, complexExt]

/--
  Reassemble a proof `h` of the characterization of the core constants of `t`
    (`LaterType.coreSpec`) as translated by `Lam2D` into a proof of the structure
    in `coreSpecs`, e.g. `⟨h.1, h.2.1, ⋯⟩ : RealInterpUnlifted.CoreSpec ri`. The
    conjuncts of the characterization are in the same order as the fields of the structure
-/
def LaterInfo.coreSpecOfConj (li : LaterInfo) (t : LaterType) (h : Expr) : MetaM Expr := do
  let .some coreSpec := li.coreSpecs.get? t
    | throwError "{decl_name%} :: The characterization of the core constants of `{Lam2D.interpLaterTypeAsUnlifted t}` is not available"
  -- `coreSpec` is the constructor of the structure applied to its parameters and to proofs of its fields
  let .const ctorName _ := coreSpec.getAppFn
    | throwError "{decl_name%} :: Unexpected proof {coreSpec}"
  let .ctorInfo ctor ← getConstInfo ctorName
    | throwError "{decl_name%} :: `{ctorName}` is not a constructor"
  let mut conjs := #[]
  let mut rest := h
  for _ in [1:ctor.numFields] do
    conjs := conjs.push (← Meta.mkAppM ``And.left #[rest])
    rest ← Meta.mkAppM ``And.right #[rest]
  conjs := conjs.push rest
  return mkAppN coreSpec.getAppFn (coreSpec.getAppArgs.extract 0 ctor.numParams ++ conjs)

/-- The proof in `extSpecs` of the characterization of `lc`, e.g. `sub_eq_add_neg` for `.real .sub` -/
def LaterInfo.extSpecProof (li : LaterInfo) (lc : LaterConst) : MetaM Expr := do
  let t : LaterType := match lc with
    | .real _ => .real
    | .complex _ => .complex
  let .some extSpec := li.extSpecs.get? t
    | throwError "{decl_name%} :: The characterizations of the constants of `{Lam2D.interpLaterTypeAsUnlifted t}` are unknown"
  -- The field of `lc` is `some (PLift.up _ proof)` if the characterization of `lc` is available
  let field ← Meta.whnfD (← Meta.mkProjection extSpec lc.specField)
  let .app (.app (.const ``Option.some _) _) (.app (.app (.const ``PLift.up _) _) proof) := field
    | throwError "{decl_name%} :: The characterization of `{lc.reprAux}` is not available"
  return proof

/--
  The characterizations available in `li.laterValExpr u`. It must be equal to `LaterVal.specAvail`
    of `li.laterValExpr u` by reduction, which is checked by the kernel
-/
def LaterInfo.specAvail (li : LaterInfo) : LaterSpecAvail :=
  ⟨li.coreSpecs.contains .real, RealConst.all.filter fun rc => li.extAvail.contains (.real rc),
   li.coreSpecs.contains .complex, ComplexConst.all.filter fun cc => li.extAvail.contains (.complex cc)⟩

end Auto.LamLater
