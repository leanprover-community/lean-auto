module

public import Lean
public import Auto.Lib.MetaExtra
public import Auto.Translation.Inductive

public section

/-!
  Proofs of the characterizations of inductive types (see `IndInfo.specTerms` and
    `MutualIndInfo.inductionTerm`), given their statements as Lean expressions
-/

open Lean

register_option auto.indSpec : Bool := {
  defValue := true
  descr := "Send the characterizations of inductive types to native provers"
}

namespace Auto.IndSpec

/-- Prove `∀ x₁ ⋯ xₙ y₁ ⋯ yₘ, ¬ (c₁ x₁ ⋯ xₙ = c₂ y₁ ⋯ yₘ)` for different constructors `c₁ c₂` -/
def proveDistinct (stmt : Expr) : MetaM Expr :=
  Meta.forallTelescopeReducing stmt fun xs body => do
    -- The last binder is the hypothesis `c₁ x₁ ⋯ xₙ = c₂ y₁ ⋯ yₘ` of `¬`
    let .some h := xs.back?
      | throwError "{decl_name%} :: Unexpected statement {stmt}"
    Meta.mkLambdaFVars xs (← Meta.mkNoConfusion body h)

/--
  Prove `∀ x₁ ⋯ xₙ y₁ ⋯ yₙ, c x₁ ⋯ xₙ = c y₁ ⋯ yₙ → x₁ = y₁ ∧ ⋯ ∧ xₙ = yₙ` by `c.inj`.
    `c.inj` omits the equations of the fields that are proofs, which are proved by
    proof irrelevance instead
-/
def proveInject (stmt : Expr) : MetaM Expr :=
  Meta.forallTelescopeReducing stmt fun xs _ => do
    let .some h := xs.back?
      | throwError "{decl_name%} :: Unexpected statement {stmt}"
    let .some (_, lhs, _) := (← Meta.whnf (← Meta.inferType h)).eq?
      | throwError "{decl_name%} :: Unexpected statement {stmt}"
    let .const ctor _ := (← Meta.whnf lhs).getAppFn
      | throwError "{decl_name%} :: Unexpected statement {stmt}"
    -- `xs` is `x₁ ⋯ xₙ y₁ ⋯ yₙ h`
    let n := (xs.size - 1) / 2
    let isProofField ← (xs.extract 0 n).mapM Meta.isProof
    let numData := (isProofField.filter (!·)).size
    let dataEqs ←
      if numData == 0 then pure #[]
      else Meta.mkAndProjN (← Meta.mkAppM (ctor ++ `inj) #[h]) numData
    let mut eqs := #[]
    let mut j := 0
    for i in [0:n] do
      if isProofField[i]! then
        eqs := eqs.push (← Meta.mkAppM ``proof_irrel #[xs[i]!, xs[n + i]!])
      else
        eqs := eqs.push dataEqs[j]!
        j := j + 1
    Meta.mkLambdaFVars xs (← Meta.mkAndIntroN eqs)

/-- Prove `∀ x₁ ⋯ xₙ, projᵢ (c x₁ ⋯ xₙ) = xᵢ` by reflexivity -/
def proveProj (stmt : Expr) : MetaM Expr :=
  Meta.forallTelescopeReducing stmt fun xs body => do
    let .some (_, _, rhs) := body.eq?
      | throwError "{decl_name%} :: Unexpected statement {stmt}"
    Meta.mkLambdaFVars xs (← Meta.mkEqRefl rhs)

/--
  Prove induction over the mutual block `smiv` (see `MutualIndInfo.inductionTerm`), i.e.
    `stmt := ∀ (P₁ : T₁ → Prop) ⋯ (Pₖ : Tₖ → Prop), H₁ → ⋯ → Hₘ → (∀ t, P₁ t) ∧ ⋯ ∧ (∀ t, Pₖ t)`,
    by the recursors of `smiv`. `T₁ ⋯ Tₖ` are the types of `smiv`, followed by the types
    in `smiv.nested` that are `reified`. The motives of the other nested types are `fun _ => True`.
  The hypotheses `H₁ ⋯ Hₘ` are the minor premises of the recursors of the types `T₁ ⋯ Tₖ`, with
    the induction hypotheses about the other nested types removed
-/
def proveInduction (stmt : Expr) (smiv : SimpleMutIndVal) (reified : Array Bool) : MetaM Expr := do
  let .some first := smiv.vals[0]?
    | throwError "{decl_name%} :: Empty mutual block"
  let firstTy ← Meta.zetaReduce first.type
  let .const _ lvls := firstTy.getAppFn
    | throwError "{decl_name%} :: Unexpected type {firstTy}"
  let params := firstTy.getAppArgs
  -- Whether the type of each motive of the recursors is among `T₁ ⋯ Tₖ`
  let present := Array.replicate smiv.vals.size true ++ reified
  -- The recursors of the types of `smiv`, followed by the ones of the nested types
  let recNames := smiv.vals.map (·.name ++ `rec) ++
    (Array.range smiv.nested.size).map fun i => first.name ++ .mkSimple s!"rec_{i + 1}"
  let recVal ← getConstInfoRec recNames[0]!
  if recVal.numMotives != present.size then
    throwError "{decl_name%} :: The recursors of {smiv.vals.map (·.name)} have {recVal.numMotives} motives, but {present.size} are expected"
  -- The motives are in `Prop`
  let recLvls := if recVal.levelParams.length == lvls.length + 1 then .zero :: lvls else lvls
  let recTy ← Meta.inferType (mkAppN (.const recNames[0]! recLvls) params)
  let motiveTys ← Meta.forallBoundedTelescope recTy (.some present.size) fun motives _ =>
    motives.mapM fun motive => do return (← Meta.inferType motive).bindingDomain!
  -- The number of fields of the constructors of each type of the motives
  let ctorFields ← motiveTys.mapM fun ty => do
    let .const tyName _ := (← Meta.whnf ty).getAppFn
      | throwError "{decl_name%} :: Unexpected type {ty}"
    let indVal ← getConstInfoInduct tyName
    indVal.ctors.toArray.mapM fun ctor => do return (← getConstInfoCtor ctor).numFields
  let k := (present.filter id).size
  let m := ((ctorFields.zip present).filter (·.2)).foldl (· + ·.1.size) 0
  Meta.forallBoundedTelescope stmt (.some (k + m)) fun xs _ => do
    if xs.size != k + m then
      throwError "{decl_name%} :: Unexpected statement {stmt}"
    let Ps := xs.extract 0 k
    let hs := xs.extract k xs.size
    let isMotiveFVar (fvarId : FVarId) := Ps.any (·.fvarId! == fvarId)
    let mut motives := #[]
    let mut pIdx := 0
    for (ty, p) in motiveTys.zip present do
      if p then
        motives := motives.push Ps[pIdx]!
        pIdx := pIdx + 1
      else
        motives := motives.push (.lam `_ ty (.const ``True []) .default)
    let mut ty ← Meta.instantiateForall recTy motives
    let mut minors := #[]
    let mut hIdx := 0
    for (fields, p) in ctorFields.zip present do
      for numFields in fields do
        let .forallE _ minorTy b _ ← Meta.whnf ty
          | throwError "{decl_name%} :: Unexpected type {ty} of recursor {recNames[0]!}"
        let minor ← Meta.forallTelescope minorTy fun args _ => do
          if !p then
            return ← Meta.mkLambdaFVars args (.const ``True.intro [])
          -- The induction hypotheses about `T₁ ⋯ Tₖ`
          let ihs ← (args.extract numFields args.size).filterM fun ih => do
            return (← Meta.inferType ih).hasAnyFVar isMotiveFVar
          Meta.mkLambdaFVars args (mkAppN hs[hIdx]! (args.extract 0 numFields ++ ihs))
        if p then
          hIdx := hIdx + 1
        minors := minors.push minor
        ty := b.instantiate1 minor
    let concls := (recNames.zip present).filterMap fun (recName, p) =>
      if p then .some (mkAppN (.const recName recLvls) (params ++ motives ++ minors)) else .none
    Meta.mkLambdaFVars xs (← Meta.mkAndIntroN concls)

end Auto.IndSpec
