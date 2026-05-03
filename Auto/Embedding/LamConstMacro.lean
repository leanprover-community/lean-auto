import Lean

/-!
# `mkConstFamily` — macro for the constant-family scaffolding in `LamBase.lean`.

Generates the boilerplates (`reprAux`, `reprPrec`, `Repr`,
`toString`, `ToString`, `beq`, `BEq`, `LawfulBEq`, `lamCheck`, `LamWF`,
`LamWF.unique`, `LamWF.ofX`, `lamWF_complete`, `lamCheck_of_LamWF`,
`LamWF.ofCheck`, `interp`, `LamWF.interp`, `interp_lvalIrrelevance`,
`interp_equiv`) for a constant inductive in one shot.

Usage:
```
mkConstFamily PropConst with
  | trueE  | ofTrueE  | (.base .prop) | "True"  | GLift.up True
  | falseE | ofFalseE | (.base .prop) | "False" | GLift.up False
  ......
```

Each row supplies (ctor name [+ optional `(name : type)` binders], LamWF ctor
name, sort, display string, lift expr).  Binder names are in scope for the
sort, display, and lift terms on the right.

The `ncInterp` modifier marks `interp` and `LamWF.interp` as `noncomputable`.

Each emitter is a separate `private def` to keep individual elaboration units
small (Lean's elaborator slows down on large quotation bodies).

Binder types are required to be `LawfulBEq` for the generated `beq_refl` and
`eq_of_beq_eq_true` proofs to discharge the parameterized cases.
-/

namespace Auto.Embedding.Lam

open Lean Elab Command Lean.Parser.Term

/-- A single explicit binder `(name : type)` attached to a const-family ctor row. -/
syntax cfBinder := "(" ident " : " term ")"

syntax constFamilyRow := "|" ident cfBinder* "|" ident "|" term "|" term "|" term

-- `ncInterp`: Non-computable interpretation function
syntax (name := mkConstFamilyCmd)
  "mkConstFamily " ("ncInterp")? ident " with " constFamilyRow* : command

/-- Bundle of identifiers and syntax arrays needed by every emitter step. -/
structure ConstFamilyCtx where
  tyName          : Ident
  ctors           : Array Ident
  wfs             : Array Ident
  /-- Per-row binder list, parsed from `cfBinder*`. -/
  binders         : Array (Array (Ident × Term))
  /-- Per-row pattern term: `Ty.ctor n m` (or just `Ty.ctor` if no binders). -/
  patterns        : Array Term
  /-- Per-row WF-pattern term: `Ty.LamWF.ofCtor n m` (or `Ty.LamWF.ofCtor`). -/
  wfPatterns      : Array Term
  /-- Per-row repr string term, e.g. `"natVal"` or `"natVal " ++ toString n`. -/
  reprStrs        : Array Term
  sorts           : Array Term
  disps           : Array Term
  lifts           : Array Term
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

/-- Build a fully-qualified ctor or wf-ctor application term: `f a b c` or just `f`. -/
private def mkCtorPattern (f : Ident) (args : Array Ident) : CommandElabM Term :=
  if args.isEmpty then `($f:ident) else `($f:ident $args:ident*)

/-- Build the per-row repr string: `"name"` (no binders) or
`"name" ++ " " ++ toString b1 ++ " " ++ toString b2 ++ ...` (with binders). -/
private def mkReprStr (ctorName : String) (bnames : Array Ident) : CommandElabM Term := do
  let base : Term := Syntax.mkStrLit ctorName
  bnames.foldlM (init := base) fun acc b => `($acc ++ " " ++ toString $b)

/-- Parse the row syntax and assemble a `ConstFamilyCtx`. -/
def buildConstFamilyCtx (tyName : Ident) (rows : Array (TSyntax `Auto.Embedding.Lam.constFamilyRow)) :
    CommandElabM ConstFamilyCtx := do
  let parsed ← rows.mapM fun row => match row with
    | `(constFamilyRow|
        | $ctor:ident $bs:cfBinder* | $wf:ident | $sort:term | $disp:term | $lift:term) => do
        let binders : Array (Ident × Term) ← bs.mapM fun b => match b with
          | `(cfBinder| ($n:ident : $t:term)) => pure (n, t)
          | _ => throwUnsupportedSyntax
        pure (ctor, wf, binders, sort, disp, lift)
    | _ => throwUnsupportedSyntax
  let ctors    : Array Ident                      := parsed.map (·.1)
  let wfs      : Array Ident                      := parsed.map (·.2.1)
  let binders  : Array (Array (Ident × Term))     := parsed.map (·.2.2.1)
  let sorts    : Array Term                       := parsed.map (·.2.2.2.1)
  let disps    : Array Term                       := parsed.map (·.2.2.2.2.1)
  let lifts    : Array Term                       := parsed.map (·.2.2.2.2.2)
  let nm := tyName.getId
  let qualify (s : Name) : Ident := mkIdent (nm ++ s)
  let qualCtor (c : Ident)  : Ident := mkIdent (nm ++ c.getId)
  let qualWf   (w : Ident)  : Ident := mkIdent (nm ++ `LamWF ++ w.getId)
  let patterns : Array Term ←
    Array.zip ctors binders |>.mapM fun (c, bs) =>
      mkCtorPattern (qualCtor c) (bs.map (·.1))
  let wfPatterns : Array Term ←
    Array.zip wfs binders |>.mapM fun (w, bs) =>
      mkCtorPattern (qualWf w) (bs.map (·.1))
  let reprStrs : Array Term ←
    Array.zip ctors binders |>.mapM fun (c, bs) =>
      mkReprStr c.getId.toString (bs.map (·.1))
  return {
    tyName          := tyName
    ctors           := ctors
    wfs             := wfs
    binders         := binders
    patterns        := patterns
    wfPatterns      := wfPatterns
    reprStrs        := reprStrs
    sorts           := sorts
    disps           := disps
    lifts           := lifts
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
  let { reprAuxId, tyName, patterns, reprStrs, .. } := c
  elabCommand <| ← `(
    set_option linter.unusedVariables false in
    def $reprAuxId : $tyName:ident → String
      $[| $patterns:term => $reprStrs:term]*)

private def emitReprPrec (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { reprPrecId, tyName, nmStr, reprAuxId, .. } := c
  elabCommand <| ← `(
    def $reprPrecId (x : $tyName:ident) (n : Nat) : Std.Format :=
      match n with
      | 0 => f!"Auto.Embedding.Lam.{$nmStr}.{$reprAuxId x}"
      | _ + 1 => f!"({$reprAuxId x})")
  elabCommand <| ← `(instance : Repr $tyName:ident where reprPrec := $reprPrecId)

private def emitToString (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { toStringId, tyName, patterns, disps, .. } := c
  elabCommand <| ← `(
    set_option linter.unusedVariables false in
    def $toStringId : $tyName:ident → String
      $[| $patterns:term => $disps:term]*)
  elabCommand <| ← `(instance : ToString $tyName:ident where toString := $toStringId)

/-- Build the right-hand side pattern (with primed binder names) and the
boolean `beq` rhs for one row. -/
private def mkBeqAlt (qualCtorIdent : Ident) (binders : Array (Ident × Term)) :
    CommandElabM (Term × Term) := do
  let lnames := binders.map (·.1)
  let rnames : Array Ident ← binders.mapM fun (n, _) =>
    pure (mkIdent (n.getId.appendAfter "✝r"))
  let rPat ← mkCtorPattern qualCtorIdent rnames
  let rhs : Term ←
    if binders.isEmpty then
      `(true)
    else
      let pairs := Array.zip lnames rnames
      let head := pairs[0]!
      let rest := pairs[1:].toArray
      let init : Term ← `($(head.1) == $(head.2))
      rest.foldlM (init := init) fun acc (l, r) => `($acc && $l == $r)
  pure (rPat, rhs)

private def emitBeq (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { beqId, tyName, ctors, binders, patterns, .. } := c
  -- Build per-row beq alts with primed-name right pattern.
  let alts : TSyntaxArray ``matchAlt ←
    Array.zip ctors (Array.zip patterns binders) |>.mapM fun (cc, lpat, bs) => do
      let qualCC := mkIdent (c.tyName.getId ++ cc.getId)
      let (rpat, rhs) ← mkBeqAlt qualCC bs
      `(matchAltExpr| | $lpat:term, $rpat:term => $rhs)
  let wildcardAlt : TSyntax ``matchAlt ← `(matchAltExpr| | _, _ => false)
  let allBeqAlts := alts.push wildcardAlt
  elabCommand <| ← `(
    def $beqId (x y : $tyName:ident) : Bool :=
      match x, y with
      $allBeqAlts:matchAlt*)
  elabCommand <| ← `(instance : BEq $tyName:ident where beq := $beqId)

private def emitBeqLemmas (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { beqDefId, beqReflId, eqOfBeqId, beqId, tyName, .. } := c
  elabCommand <| ← `(
    theorem $beqDefId {x y : $tyName:ident} : (x == y) = $beqId x y := rfl)
  -- beq_refl: handles parameterless (rfl) and parameterized (`a == a` simp lemmas).
  elabCommand <| ← `(
    theorem $beqReflId : ∀ {x : $tyName:ident}, $beqId x x = true := by
      intro x; cases x <;> first | rfl | simp [$beqId:ident])
  -- eq_of_beq: handles parameterless (rfl/contradiction) and parameterized
  -- (extract underlying Prop equality from `==`).
  elabCommand <| ← `(
    theorem $eqOfBeqId : ∀ {x y : $tyName:ident}, $beqId x y = true → x = y := by
      intro x y h
      cases x <;> cases y <;>
        first
          | rfl
          | contradiction
          | (simp only [$beqId:ident, Bool.and_eq_true] at h
             repeat' (first | rfl | (apply congrArg) | (apply congrArg₂)
                            | (cases LawfulBEq.eq_of_beq h.1; clear h; rename_i h)
                            | (cases LawfulBEq.eq_of_beq h; rfl))))
  elabCommand <| ← `(
    instance : LawfulBEq $tyName:ident where
      eq_of_beq := $eqOfBeqId
      rfl := $beqReflId)

private def emitLamCheck (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamCheckId, tyName, lamSortId, patterns, sorts, .. } := c
  elabCommand <| ← `(
    set_option linter.unusedVariables false in
    def $lamCheckId : $tyName:ident → $lamSortId
      $[| $patterns:term => $sorts:term]*)

/-- Build the type of one LamWF constructor: either `LamWF pat sort` or
`∀ (b1 : T1) ..., LamWF pat sort` if there are binders. -/
private def mkWFCtorType (lamWFId : Ident) (binders : Array (Ident × Term))
    (pattern sort : Term) : CommandElabM Term := do
  if binders.isEmpty then
    `($lamWFId $pattern $sort)
  else
    let bs := binders.map (·.1)
    let ts := binders.map (·.2)
    `(∀ $[($bs:ident : $ts:term)]*, $lamWFId $pattern $sort)

private def emitLamWFInductive (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamWFId, tyName, lamSortId, wfs, binders, patterns, sorts, .. } := c
  let ctorTypes : Array Term ←
    (Array.zip binders (Array.zip patterns sorts)).mapM fun (bs, pat, s) =>
      mkWFCtorType lamWFId bs pat s
  elabCommand <| ← `(
    inductive $lamWFId:ident : $tyName:ident → $lamSortId → Type where
      $[| $wfs:ident : $ctorTypes:term]*)

private def emitLamWFUnique (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamWFUniqueId, tyName, lamSortId, lamWFId, .. } := c
  elabCommand <| ← `(
    def $lamWFUniqueId {x : $tyName:ident} {s₁ s₂ : $lamSortId}
        (w₁ : $lamWFId x s₁) (w₂ : $lamWFId x s₂) : s₁ = s₂ ∧ HEq w₁ w₂ := by
      cases w₁ <;> cases w₂ <;> trivial)

private def emitOfTy (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { ofTyId, tyName, lamSortId, lamWFId, patterns, sorts, wfPatterns, .. } := c
  let ofTyAlts : TSyntaxArray ``matchAlt ←
    Array.zip patterns (Array.zip sorts wfPatterns) |>.mapM fun (pat, s, wpat) =>
      `(matchAltExpr| | $pat:term => ⟨$s, $wpat⟩)
  elabCommand <| ← `(
    def $ofTyId (x : $tyName:ident) : (s : $lamSortId) × $lamWFId x s :=
      match x with
      $ofTyAlts:matchAlt*)

private def emitWFCompleteness (c : ConstFamilyCtx) : CommandElabM Unit := do
  let { lamWFCompleteId, lamCheckOfWFId, tyName, lamSortId, lamWFId,
        ofTyId, lamCheckId, .. } := c
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
        patterns, wfPatterns, lifts, uId, .. } := c
  if noncomp then
    elabCommand <| ← `(
      set_option linter.unusedVariables false in
      noncomputable def $interpId (tyVal : Nat → Type $uId:ident) :
          (x : $tyName:ident) → ($lamCheckId x).interp tyVal
        $[| $patterns:term => $lifts:term]*)
    elabCommand <| ← `(
      set_option linter.unusedVariables false in
      noncomputable def $lamWFInterpId (tyVal : Nat → Type $uId:ident)
          {x : $tyName:ident} {s : $lamSortId} :
          (lwf : $lamWFId x s) → s.interp tyVal
        $[| $wfPatterns:term => $lifts:term]*)
  else
    elabCommand <| ← `(
      set_option linter.unusedVariables false in
      def $interpId (tyVal : Nat → Type $uId:ident) :
          (x : $tyName:ident) → ($lamCheckId x).interp tyVal
        $[| $patterns:term => $lifts:term]*)
    elabCommand <| ← `(
      set_option linter.unusedVariables false in
      def $lamWFInterpId (tyVal : Nat → Type $uId:ident)
          {x : $tyName:ident} {s : $lamSortId} :
          (lwf : $lamWFId x s) → s.interp tyVal
        $[| $wfPatterns:term => $lifts:term]*)

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
