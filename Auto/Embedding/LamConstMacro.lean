import Lean

/-!
# `mkConstFamily` — macro for the constant-family scaffolding in `LamBase.lean`.

Generates the ~80 lines of boilerplate (`reprAux`, `reprPrec`, `Repr`,
`toString`, `ToString`, `beq`, `BEq`, `LawfulBEq`, `lamCheck`, `LamWF`,
`LamWF.unique`, `LamWF.ofX`, `lamWF_complete`, `lamCheck_of_LamWF`,
`LamWF.ofCheck`, `interp`, `LamWF.interp`, `interp_lvalIrrelevance`,
`interp_equiv`) for a non-parameterized constant inductive in one shot.

Usage:
```
mkConstFamily PropConst with
  | trueE  | ofTrueE  | (.base .prop) | "True"  | GLift.up True
  | falseE | ofFalseE | (.base .prop) | "False" | GLift.up False
  …
```

Each row supplies (ctor name, LamWF ctor name, sort, display string, lift expr).
This prototype only handles inductives whose ctors take **no parameters**.

The emission of each declaration is split into a separate helper to keep
individual elaboration units small (Lean's elaborator slows down on large
quotation bodies, so we want each `\`(...)` to be modest).
-/

namespace Auto.Embedding.Lam

open Lean Elab Command Lean.Parser.Term

syntax constFamilyRow := "|" ident "|" ident "|" term "|" str "|" term

-- `ncInterp`: Non-computable interpretation function
syntax (name := mkConstFamilyCmd)
  "mkConstFamily " ("ncInterp")? ident " with " constFamilyRow* : command

/-- Bundle of identifiers and syntax arrays needed by every emitter step.
Computed once from the user's invocation, then threaded through the helpers. -/
structure ConstFamilyCtx where
  tyName          : Ident
  ctors           : Array Ident
  wfs             : Array Ident
  sorts           : Array Term
  disps           : Array (TSyntax `str)
  lifts           : Array Term
  qualCtors       : Array Ident
  qualWfs         : Array Ident
  reprStrs        : Array (TSyntax `str)
  nmStr           : TSyntax `str
  lamSortId       : Ident
  uId             : Ident
  reprAuxId       : Ident
  reprPrecId      : Ident
  toStringId      : Ident
  beqId           : Ident
  beqDefId        : Ident
  beqReflId       : Ident
  eqOfBeqId       : Ident
  lamCheckId      : Ident
  lamWFId         : Ident
  lamWFUniqueId   : Ident
  ofTyId          : Ident
  lamWFCompleteId : Ident
  lamCheckOfWFId  : Ident
  ofCheckId       : Ident
  interpId        : Ident
  lamWFInterpId   : Ident
  lvalIrrId       : Ident
  interpEquivId   : Ident

/-- Parse the row syntax and assemble a `ConstFamilyCtx`. -/
def buildConstFamilyCtx (tyName : Ident) (rows : Array (TSyntax `Auto.Embedding.Lam.constFamilyRow)) :
    CommandElabM ConstFamilyCtx := do
  let parsed ← rows.mapM fun row => match row with
    | `(constFamilyRow| | $ctor:ident | $wf:ident | $sort:term | $disp:str | $lift:term) =>
        pure (ctor, wf, sort, disp, lift)
    | _ => throwUnsupportedSyntax
  let ctors  : Array Ident          := parsed.map (·.1)
  let wfs    : Array Ident          := parsed.map (·.2.1)
  let sorts  : Array Term           := parsed.map (·.2.2.1)
  let disps  : Array (TSyntax `str) := parsed.map (·.2.2.2.1)
  let lifts  : Array Term           := parsed.map (·.2.2.2.2)
  let nm := tyName.getId
  let qualify (s : Name) : Ident := mkIdent (nm ++ s)
  return {
    tyName          := tyName
    ctors           := ctors
    wfs             := wfs
    sorts           := sorts
    disps           := disps
    lifts           := lifts
    qualCtors       := ctors.map fun c => mkIdent (nm ++ c.getId)
    qualWfs         := wfs.map fun w => mkIdent (nm ++ `LamWF ++ w.getId)
    reprStrs        := ctors.map fun c => Syntax.mkStrLit c.getId.toString
    nmStr           := Syntax.mkStrLit nm.toString
    lamSortId       := mkIdent `LamSort
    uId             := mkIdent `u
    reprAuxId       := qualify `reprAux
    reprPrecId      := qualify `reprPrec
    toStringId      := qualify `toString
    beqId           := qualify `beq
    beqDefId        := qualify `beq_def
    beqReflId       := qualify `beq_refl
    eqOfBeqId       := qualify `eq_of_beq_eq_true
    lamCheckId      := qualify `lamCheck
    lamWFId         := qualify `LamWF
    lamWFUniqueId   := qualify (`LamWF ++ `unique)
    ofTyId          := qualify (`LamWF ++ ("of" ++ nm.getString!).toName)
    lamWFCompleteId := qualify `lamWF_complete
    lamCheckOfWFId  := qualify `lamCheck_of_LamWF
    ofCheckId       := qualify (`LamWF ++ `ofCheck)
    interpId        := qualify `interp
    lamWFInterpId   := qualify (`LamWF ++ `interp)
    lvalIrrId       := qualify (`LamWF ++ `interp_lvalIrrelevance)
    interpEquivId   := qualify `interp_equiv
  }

private def emitReprAux (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { reprAuxId, tyName, qualCtors, reprStrs, .. } := c
  elabCommand <| ← `(
    def $reprAuxId : $tyName:ident → String
      $[| $qualCtors:ident => $reprStrs:str]*)

private def emitReprPrec (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { reprPrecId, tyName, nmStr, reprAuxId, .. } := c
  elabCommand <| ← `(
    def $reprPrecId (x : $tyName:ident) (n : Nat) : Std.Format :=
      match n with
      | 0 => f!"Auto.Embedding.Lam.{$nmStr}.{$reprAuxId x}"
      | _ + 1 => f!"({$reprAuxId x})")
  elabCommand <| ← `(instance : Repr $tyName:ident where reprPrec := $reprPrecId)

private def emitToString (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { toStringId, tyName, qualCtors, disps, .. } := c
  elabCommand <| ← `(
    def $toStringId : $tyName:ident → String
      $[| $qualCtors:ident => $disps:str]*)
  elabCommand <| ← `(instance : ToString $tyName:ident where toString := $toStringId)

private def emitBeq (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { beqId, tyName, qualCtors, .. } := c
  let beqAlts : TSyntaxArray ``matchAlt ←
    qualCtors.mapM fun cc => `(matchAltExpr| | $cc:ident, $cc:ident => true)
  let wildcardAlt : TSyntax ``matchAlt ← `(matchAltExpr| | _, _ => false)
  let allBeqAlts := beqAlts.push wildcardAlt
  elabCommand <| ← `(
    def $beqId (x y : $tyName:ident) : Bool :=
      match x, y with
      $allBeqAlts:matchAlt*)
  elabCommand <| ← `(instance : BEq $tyName:ident where beq := $beqId)

private def emitBeqLemmas (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { beqDefId, beqReflId, eqOfBeqId, beqId, tyName, .. } := c
  elabCommand <| ← `(
    theorem $beqDefId {x y : $tyName:ident} : (x == y) = $beqId x y := rfl)
  elabCommand <| ← `(
    theorem $beqReflId : ∀ {x : $tyName:ident}, $beqId x x = true := by
      intro x; cases x <;> rfl)
  elabCommand <| ← `(
    theorem $eqOfBeqId : ∀ {x y : $tyName:ident}, $beqId x y = true → x = y := by
      intro x y h; cases x <;> cases y <;> first | contradiction | rfl)
  elabCommand <| ← `(
    instance : LawfulBEq $tyName:ident where
      eq_of_beq := $eqOfBeqId
      rfl := $beqReflId)

private def emitLamCheck (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamCheckId, tyName, lamSortId, qualCtors, sorts, .. } := c
  elabCommand <| ← `(
    def $lamCheckId : $tyName:ident → $lamSortId
      $[| $qualCtors:ident => $sorts:term]*)

private def emitLamWFInductive (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamWFId, tyName, lamSortId, wfs, qualCtors, sorts, .. } := c
  let lamWFCtorTypes : Array Term ←
    Array.zip qualCtors sorts |>.mapM fun (cc, s) => `($lamWFId $cc:ident $s)
  elabCommand <| ← `(
    inductive $lamWFId:ident : $tyName:ident → $lamSortId → Type where
      $[| $wfs:ident : $lamWFCtorTypes:term]*)

private def emitLamWFUnique (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamWFUniqueId, tyName, lamSortId, lamWFId, .. } := c
  elabCommand <| ← `(
    def $lamWFUniqueId {x : $tyName:ident} {s₁ s₂ : $lamSortId}
        (w₁ : $lamWFId x s₁) (w₂ : $lamWFId x s₂) : s₁ = s₂ ∧ HEq w₁ w₂ := by
      cases w₁ <;> cases w₂ <;> trivial)

private def emitOfTy (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { ofTyId, tyName, lamSortId, lamWFId, qualCtors, sorts, qualWfs, .. } := c
  let ofTyAlts : TSyntaxArray ``matchAlt ←
    Array.zip qualCtors (Array.zip sorts qualWfs) |>.mapM fun (cc, s, w) =>
      `(matchAltExpr| | $cc:ident => ⟨$s, $w:ident⟩)
  elabCommand <| ← `(
    def $ofTyId (x : $tyName:ident) : (s : $lamSortId) × $lamWFId x s :=
      match x with
      $ofTyAlts:matchAlt*)

private def emitWFCompleteness (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamWFCompleteId, lamCheckOfWFId, tyName, lamSortId, lamWFId, ofTyId, lamCheckId, .. } := c
  elabCommand <| ← `(
    theorem $lamWFCompleteId {x : $tyName:ident} {s : $lamSortId} (wf : $lamWFId x s) :
        $ofTyId x = ⟨s, wf⟩ := by cases wf <;> rfl)
  elabCommand <| ← `(
    theorem $lamCheckOfWFId {x : $tyName:ident} {s : $lamSortId} (H : $lamWFId x s) :
        $lamCheckId x = s := by cases H <;> rfl)

private def emitOfCheck (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { ofCheckId, tyName, lamSortId, lamWFId, lamCheckId, .. } := c
  elabCommand <| ← `(
    def $ofCheckId {x : $tyName:ident} {s : $lamSortId} (H : $lamCheckId x = s) :
        $lamWFId x s := by
      cases H; cases x <;> constructor)

private def emitInterp (c : ConstFamilyCtx) (noncomp : Bool) : CommandElabM Unit := do
  let { interpId, lamWFInterpId, tyName, lamSortId, lamCheckId, lamWFId,
        qualCtors, qualWfs, lifts, uId, .. } := c
  if noncomp then
    elabCommand <| ← `(
      noncomputable def $interpId (tyVal : Nat → Type $uId:ident) :
          (x : $tyName:ident) → ($lamCheckId x).interp tyVal
        $[| $qualCtors:ident => $lifts:term]*)
    elabCommand <| ← `(
      noncomputable def $lamWFInterpId (tyVal : Nat → Type $uId:ident)
          {x : $tyName:ident} {s : $lamSortId} :
          (lwf : $lamWFId x s) → s.interp tyVal
        $[| $qualWfs:ident => $lifts:term]*)
  else
    elabCommand <| ← `(
      def $interpId (tyVal : Nat → Type $uId:ident) :
          (x : $tyName:ident) → ($lamCheckId x).interp tyVal
        $[| $qualCtors:ident => $lifts:term]*)
    elabCommand <| ← `(
      def $lamWFInterpId (tyVal : Nat → Type $uId:ident)
          {x : $tyName:ident} {s : $lamSortId} :
          (lwf : $lamWFId x s) → s.interp tyVal
        $[| $qualWfs:ident => $lifts:term]*)

private def emitInterpLemmas (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lvalIrrId, interpEquivId, tyName, lamSortId, lamWFId, lamWFInterpId,
        interpId, lamWFUniqueId, uId, .. } := c
  elabCommand <| ← `(
    theorem $lvalIrrId
        (tyVal₁ tyVal₂ : Nat → Type $uId:ident)
        {x₁ x₂ : $tyName:ident} {s₁ s₂ : $lamSortId}
        (w₁ : $lamWFId x₁ s₁) (w₂ : $lamWFId x₂ s₂)
        (Hxy : x₁ = x₂) (hTyVal : tyVal₁ = tyVal₂) :
        HEq ($lamWFInterpId tyVal₁ w₁) ($lamWFInterpId tyVal₂ w₂) := by
      cases Hxy; cases hTyVal
      rcases $lamWFUniqueId w₁ w₂ with ⟨⟨⟩, ⟨⟩⟩; rfl)
  elabCommand <| ← `(
    def $interpEquivId (tyVal : Nat → Type $uId:ident) {x : $tyName:ident} {s : $lamSortId}
        (w : $lamWFId x s) :
        HEq ($lamWFInterpId tyVal w) ($interpId tyVal x) := by
      cases w <;> rfl)

elab_rules : command
  | `(command| mkConstFamily $[ncInterp%$noncomp]? $tyName:ident with $rows:constFamilyRow*) => do
    let ctx ← buildConstFamilyCtx tyName rows
    emitReprAux ctx
    emitReprPrec ctx
    emitToString ctx
    emitBeq ctx
    emitBeqLemmas ctx
    emitLamCheck ctx
    emitLamWFInductive ctx
    emitLamWFUnique ctx
    emitOfTy ctx
    emitWFCompleteness ctx
    emitOfCheck ctx
    emitInterp ctx noncomp.isSome
    emitInterpLemmas ctx

end Auto.Embedding.Lam
