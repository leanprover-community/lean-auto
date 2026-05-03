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
  | trueE  | ofTrueE  | (.base .prop)                                              | "True"  | GLift.up True
  | falseE | ofFalseE | (.base .prop)                                              | "False" | GLift.up False
  …
```

Each row supplies (ctor name, LamWF ctor name, sort, display string, lift expr).
This prototype only handles inductives whose ctors take **no parameters**.
-/

namespace Auto.Embedding.Lam

open Lean Elab Command Lean.Parser.Term

syntax constFamilyRow := "|" ident "|" ident "|" term "|" str "|" term

syntax (name := mkConstFamilyCmd)
  "mkConstFamily " ident " with " constFamilyRow* : command

elab_rules : command
  | `(command| mkConstFamily $tyName:ident with $rows:constFamilyRow*) => do
    let parsed ← rows.mapM fun row => match row with
      | `(constFamilyRow| | $ctor:ident | $wf:ident | $sort:term | $disp:str | $lift:term) =>
          pure (ctor, wf, sort, disp, lift)
      | _ => throwUnsupportedSyntax
    let ctors  : Array Ident := parsed.map (·.1)
    let wfs    : Array Ident := parsed.map (·.2.1)
    let sorts  : Array Term  := parsed.map (·.2.2.1)
    let disps  : Array (TSyntax `str) := parsed.map (·.2.2.2.1)
    let lifts  : Array Term  := parsed.map (·.2.2.2.2)

    let nm := tyName.getId
    let qualify (s : Name) : Ident := mkIdent (nm ++ s)
    let reprAuxId       := qualify `reprAux
    let reprPrecId      := qualify `reprPrec
    let toStringId      := qualify `toString
    let beqId           := qualify `beq
    let beqDefId        := qualify `beq_def
    let beqReflId       := qualify `beq_refl
    let eqOfBeqId       := qualify `eq_of_beq_eq_true
    let lamCheckId      := qualify `lamCheck
    let lamWFId         := qualify `LamWF
    let lamWFUniqueId   := qualify (`LamWF ++ `unique)
    let ofTyId          := qualify (`LamWF ++ ("of" ++ nm.getString!).toName)
    let lamWFCompleteId := qualify `lamWF_complete
    let lamCheckOfWFId  := qualify `lamCheck_of_LamWF
    let ofCheckId       := qualify (`LamWF ++ `ofCheck)
    let interpId        := qualify `interp
    let lamWFInterpId   := qualify (`LamWF ++ `interp)
    let lvalIrrId       := qualify (`LamWF ++ `interp_lvalIrrelevance)
    let interpEquivId   := qualify `interp_equiv

    let reprStrs : Array (TSyntax `str) :=
      ctors.map fun c => Syntax.mkStrLit c.getId.toString
    let qualCtors : Array Ident := ctors.map fun c => mkIdent (nm ++ c.getId)
    let qualWfs   : Array Ident := wfs.map fun w => mkIdent (nm ++ `LamWF ++ w.getId)
    let nmStr : TSyntax `str := Syntax.mkStrLit nm.toString
    -- Unhygienic references to names that must resolve to the user's namespace.
    let lamSortId : Ident := mkIdent `LamSort
    let uId       : Ident := mkIdent `u

    -- 1. reprAux
    elabCommand <| ← `(
      def $reprAuxId : $tyName:ident → String
        $[| $qualCtors:ident => $reprStrs:str]*)

    -- 2. reprPrec + Repr instance
    elabCommand <| ← `(
      def $reprPrecId (x : $tyName:ident) (n : Nat) : Std.Format :=
        match n with
        | 0 => f!"Auto.Embedding.Lam.{$nmStr}.{$reprAuxId x}"
        | _ + 1 => f!"({$reprAuxId x})")
    elabCommand <| ← `(instance : Repr $tyName:ident where reprPrec := $reprPrecId)

    -- 3. toString + ToString instance
    elabCommand <| ← `(
      def $toStringId : $tyName:ident → String
        $[| $qualCtors:ident => $disps:str]*)
    elabCommand <| ← `(instance : ToString $tyName:ident where toString := $toStringId)

    -- 4. beq + BEq instance.  Build alts as a TSyntaxArray, append wildcard.
    let beqAlts : TSyntaxArray ``matchAlt ←
      qualCtors.mapM fun c => `(matchAltExpr| | $c:ident, $c:ident => true)
    let wildcardAlt : TSyntax ``matchAlt ←
      `(matchAltExpr| | _, _ => false)
    let allBeqAlts := beqAlts.push wildcardAlt
    elabCommand <| ← `(
      def $beqId (x y : $tyName:ident) : Bool :=
        match x, y with
        $allBeqAlts:matchAlt*)
    elabCommand <| ← `(instance : BEq $tyName:ident where beq := $beqId)

    -- 5. beq lemmas + LawfulBEq.
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

    -- 6. lamCheck.
    elabCommand <| ← `(
      def $lamCheckId : $tyName:ident → $lamSortId
        $[| $qualCtors:ident => $sorts:term]*)

    -- 7. LamWF inductive.
    let lamWFCtorTypes : Array Term ←
      Array.zip qualCtors sorts |>.mapM fun (c, s) =>
        `($lamWFId $c:ident $s)
    elabCommand <| ← `(
      inductive $lamWFId:ident : $tyName:ident → $lamSortId → Type where
        $[| $wfs:ident : $lamWFCtorTypes:term]*)

    -- 8. LamWF.unique.
    elabCommand <| ← `(
      def $lamWFUniqueId {x : $tyName:ident} {s₁ s₂ : $lamSortId}
          (w₁ : $lamWFId x s₁) (w₂ : $lamWFId x s₂) : s₁ = s₂ ∧ HEq w₁ w₂ := by
        cases w₁ <;> cases w₂ <;> trivial)

    -- 9. LamWF.ofTy.
    let ofTyAlts : TSyntaxArray ``matchAlt ←
      Array.zip qualCtors (Array.zip sorts qualWfs) |>.mapM fun (c, s, w) =>
        `(matchAltExpr| | $c:ident => ⟨$s, $w:ident⟩)
    elabCommand <| ← `(
      def $ofTyId (x : $tyName:ident) : (s : $lamSortId) × $lamWFId x s :=
        match x with
        $ofTyAlts:matchAlt*)

    -- 10. lamWF_complete and lamCheck_of_LamWF.
    elabCommand <| ← `(
      theorem $lamWFCompleteId {x : $tyName:ident} {s : $lamSortId} (wf : $lamWFId x s) :
          $ofTyId x = ⟨s, wf⟩ := by cases wf <;> rfl)
    elabCommand <| ← `(
      theorem $lamCheckOfWFId {x : $tyName:ident} {s : $lamSortId} (H : $lamWFId x s) :
          $lamCheckId x = s := by cases H <;> rfl)

    -- 11. LamWF.ofCheck.
    elabCommand <| ← `(
      def $ofCheckId {x : $tyName:ident} {s : $lamSortId} (H : $lamCheckId x = s) :
          $lamWFId x s := by
        cases H; cases x <;> constructor)

    -- 12. interp + LamWF.interp.  Use unhygienic `u` so auto-implicit can pick it up.
    elabCommand <| ← `(
      def $interpId (tyVal : Nat → Type $uId:ident) :
          (x : $tyName:ident) → ($lamCheckId x).interp tyVal
        $[| $qualCtors:ident => $lifts:term]*)
    elabCommand <| ← `(
      def $lamWFInterpId (tyVal : Nat → Type $uId:ident) {x : $tyName:ident} {s : $lamSortId} :
          (lwf : $lamWFId x s) → s.interp tyVal
        $[| $qualWfs:ident => $lifts:term]*)

    -- 13. interp_lvalIrrelevance, interp_equiv.
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

end Auto.Embedding.Lam
