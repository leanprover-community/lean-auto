module

public import Auto.EmbedLam.LamBase.Sort
public import Auto.EmbedLam.LamBase.ConstMacro

@[expose] public section

/-! Interpreted constants over `Prop`, `Bool`, `Nat`, `Int`, `Rat` and `String`, and `OtherConst` -/

namespace Auto.Embedding.Lam

open ToExprExtra

inductive PropConst
  | trueE    : PropConst -- Propositional `true`
  | falseE   : PropConst -- Propositional `false`
  | not      : PropConst -- Propositional `not`
  | and      : PropConst -- Propositional `and`
  | or       : PropConst -- Propositional `or`
  | imp      : PropConst -- Propositional `imp`
  | iff      : PropConst -- Propositional `iff`
deriving Inhabited, Hashable, Lean.ToExpr

mkConstFamily PropConst with
  | trueE  | ofTrueE  | (.base .prop)                                             | "True"  | GLift.up True
  | falseE | ofFalseE | (.base .prop)                                             | "False" | GLift.up False
  | not    | ofNot    | (.func (.base .prop) (.base .prop))                       | "¬"     | notLift
  | and    | ofAnd    | (.func (.base .prop) (.func (.base .prop) (.base .prop))) | "∧"     | andLift
  | or     | ofOr     | (.func (.base .prop) (.func (.base .prop) (.base .prop))) | "∨"     | orLift
  | imp    | ofImp    | (.func (.base .prop) (.func (.base .prop) (.base .prop))) | "→"     | impLift
  | iff    | ofIff    | (.func (.base .prop) (.func (.base .prop) (.base .prop))) | "↔"     | iffLift

inductive BoolConst
  | ofProp
  | trueb  -- Boolean `true`
  | falseb -- Boolean `false`
  | notb   -- Boolean `not`
  | andb   -- Boolean `and`
  | orb    -- Boolean `or`
deriving Inhabited, Hashable, Lean.ToExpr

mkConstFamily ncInterp BoolConst with
  | ofProp | ofOfProp | (.func (.base .prop) (.base .bool))                       | "ofProp" | ofPropLift
  | trueb  | ofTrueB  | (.base .bool)                                             | "true"   | GLift.up true
  | falseb | ofFalseB | (.base .bool)                                             | "false"  | GLift.up false
  | notb   | ofNotB   | (.func (.base .bool) (.base .bool))                       | "!"      | notbLift
  | andb   | ofAndB   | (.func (.base .bool) (.func (.base .bool) (.base .bool))) | "&&"     | andbLift
  | orb    | ofOrB    | (.func (.base .bool) (.func (.base .bool) (.base .bool))) | "||"     | orbLift

inductive NatConst
  | natVal (n : Nat)
  | nadd | nsub | nmul | ndiv | nmod
  | nle | nlt | nmax | nmin
deriving Inhabited, Hashable, Lean.ToExpr

mkConstFamily NatConst with
  | natVal (n : Nat) | ofNatVal | (.base .nat)                               | s!"{n} : Nat" | GLift.up n
  | nadd  | ofNadd | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "+"     | naddLift
  | nsub  | ofNsub | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "-"     | nsubLift
  | nmul  | ofNmul | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "*"     | nmulLift
  | ndiv  | ofNdiv | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "/"     | ndivLift
  | nmod  | ofNmod | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "%"     | nmodLift
  | nle   | ofNle  | (.func (.base .nat) (.func (.base .nat) (.base .prop))) | "≤"     | nleLift
  | nlt   | ofNlt  | (.func (.base .nat) (.func (.base .nat) (.base .prop))) | "<"     | nltLift
  | nmax  | ofNmax | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "nmax"  | nmaxLift
  | nmin  | ofNmin | (.func (.base .nat) (.func (.base .nat) (.base .nat)))  | "nmin"  | nminLift

inductive IntConst
  | iofNat | inegSucc | ineg | iabs
  | iadd | isub | imul | idiv | imod | iediv | iemod
  | ile | ilt | imax | imin
deriving Inhabited, Hashable, Lean.ToExpr

mkConstFamily IntConst with
  | iofNat   | ofIOfNat   | (.func (.base .nat) (.base .int))                       | "iofNat"   | iofNatLift
  | inegSucc | ofINegSucc | (.func (.base .nat) (.base .int))                       | "inegSucc" | inegSuccLift
  | ineg     | ofIneg     | (.func (.base .int) (.base .int))                       | "-"        | inegLift
  | iabs     | ofIabs     | (.func (.base .int) (.base .int))                       | "iabs"     | iabsLift
  | iadd     | ofIadd     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "+"        | iaddLift
  | isub     | ofIsub     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "-"        | isubLift
  | imul     | ofImul     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "*"        | imulLift
  | idiv     | ofIdiv     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "/"        | idivLift
  | imod     | ofImod     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "%"        | imodLift
  | iediv    | ofIediv    | (.func (.base .int) (.func (.base .int) (.base .int)))  | "/?"       | iedivLift
  | iemod    | ofIemod    | (.func (.base .int) (.func (.base .int) (.base .int)))  | "%?"       | iemodLift
  | ile      | ofIle      | (.func (.base .int) (.func (.base .int) (.base .prop))) | "≤"        | ileLift
  | ilt      | ofIlt      | (.func (.base .int) (.func (.base .int) (.base .prop))) | "<"        | iltLift
  | imax     | ofImax     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "imax"     | imaxLift
  | imin     | ofImin     | (.func (.base .int) (.func (.base .int) (.base .int)))  | "imin"     | iminLift

inductive RatConst
  | qofInt | qofScientific
  | qadd | qsub | qmul | qdiv | qneg | qinv
  | qle | qlt | qmax | qmin | qabs | qfloor | qceil
deriving Inhabited, Hashable, Lean.ToExpr

mkConstFamily RatConst with
  | qofInt        | ofQOfInt        | (.func (.base .int) (.base .rat))                                            | "qofInt"        | qofIntLift
  | qofScientific | ofQOfScientific | (.func (.base .nat) (.func (.base .bool) (.func (.base .nat) (.base .rat)))) | "qofScientific" | qofScientificLift
  | qadd          | ofQadd          | (.func (.base .rat) (.func (.base .rat) (.base .rat)))                       | "+"             | qaddLift
  | qsub          | ofQsub          | (.func (.base .rat) (.func (.base .rat) (.base .rat)))                       | "-"             | qsubLift
  | qmul          | ofQmul          | (.func (.base .rat) (.func (.base .rat) (.base .rat)))                       | "*"             | qmulLift
  | qdiv          | ofQdiv          | (.func (.base .rat) (.func (.base .rat) (.base .rat)))                       | "/"             | qdivLift
  | qneg          | ofQneg          | (.func (.base .rat) (.base .rat))                                            | "-"             | qnegLift
  | qinv          | ofQinv          | (.func (.base .rat) (.base .rat))                                            | "qinv"          | qinvLift
  | qle           | ofQle           | (.func (.base .rat) (.func (.base .rat) (.base .prop)))                      | "≤"             | qleLift
  | qlt           | ofQlt           | (.func (.base .rat) (.func (.base .rat) (.base .prop)))                      | "<"             | qltLift
  | qmax          | ofQmax          | (.func (.base .rat) (.func (.base .rat) (.base .rat)))                       | "qmax"          | qmaxLift
  | qmin          | ofQmin          | (.func (.base .rat) (.func (.base .rat) (.base .rat)))                       | "qmin"          | qminLift
  | qabs          | ofQabs          | (.func (.base .rat) (.base .rat))                                            | "qabs"          | qabsLift
  | qfloor        | ofQfloor        | (.func (.base .rat) (.base .int))                                            | "qfloor"        | qfloorLift
  | qceil         | ofQceil         | (.func (.base .rat) (.base .int))                                            | "qceil"         | qceilLift

inductive StringConst
  | strVal (s : String)
  | slength
  | sapp
  | sle
  | slt
  | sprefixof
  | srepall
deriving Inhabited, Hashable, Lean.ToExpr

mkConstFamily StringConst with
  | strVal (s : String) | ofStrVal | (.base .string)                                                                  | s!"({s} : String)" | GLift.up s
  | slength   | ofSlength   | (.func (.base .string) (.base .nat))                                                    | "length"            | slengthLift
  | sapp      | ofSapp      | (.func (.base .string) (.func (.base .string) (.base .string)))                         | "++"                | sappLift
  | sle       | ofSle       | (.func (.base .string) (.func (.base .string) (.base .prop)))                           | "≤"                 | sleLift
  | slt       | ofSlt       | (.func (.base .string) (.func (.base .string) (.base .prop)))                           | "<"                 | sltLift
  | sprefixof | ofSprefixof | (.func (.base .string) (.func (.base .string) (.base .bool)))                           | "is_prefix_of"      | sprefixofLift
  | srepall   | ofSrepall   | (.func (.base .string) (.func (.base .string) (.func (.base .string) (.base .string)))) | "replace_all"       | srepallLift

inductive OtherConst
  /--
    SMT attribute application, with one term as ⟨attribute_value⟩
    `.app _ (attribute ⟨keyword⟩ ⟨attr_term⟩) ⟨term⟩ ⇔ ⟨term⟩ ⟨keyword⟩ (⟨attr_term⟩)`

    `smtAttr1T n s₁ s₂` is interpreted as `fun (_ : s₁) (x₂ : s₂) => x₂`,
    which we'll denote as `constId`. Note that the interpretation is
    polymorphic. However, it does not need special treatment like
    `∀, ∃, =`. This is because `constId A↑ B↑ = (constId A B)↑`, where
    `↑` stands for universe level lifting.
  -/
  | smtAttr1T : String → LamSort → LamSort → OtherConst
deriving Inhabited, Hashable, Lean.ToExpr

def OtherConst.reprAux : OtherConst → String
| .smtAttr1T n sattr s₂ => s!"smtAttr1T {n} {sattr} {s₂}"

def OtherConst.reprPrec (p : OtherConst) (n : Nat) :=
  match n with
  | 0 => f!"Auto.Embedding.Lam.OtherConst.{p.reprAux}"
  | _ + 1 => f!"(.{p.reprAux})"

instance : Repr OtherConst where
reprPrec := OtherConst.reprPrec

inductive OtherConst.LamWF : OtherConst → LamSort → Type
  | ofSmtAttr1T n sattr sterm : LamWF (.smtAttr1T n sattr sterm) (.func sattr (.func sterm sterm))

def OtherConst.LamWF.ofOtherConst : (oc : OtherConst) → (s : LamSort) × OtherConst.LamWF oc s
| .smtAttr1T n sattr sterm => ⟨.func sattr (.func sterm sterm), .ofSmtAttr1T n sattr sterm⟩

def OtherConst.LamWF.interp (tyVal : TyVal.{u}) : (lwf : LamWF p s) → s.interp tyVal
| .ofSmtAttr1T _ sattr sterm => constId (a:=LamSort.interp tyVal sattr) (b:=LamSort.interp tyVal sterm)

def OtherConst.toString : OtherConst → String
| .smtAttr1T n _ _ => s!"attr[{n}]"

instance : ToString OtherConst where
  toString := OtherConst.toString

def OtherConst.beq : OtherConst → OtherConst → Bool
| .smtAttr1T n₁ sattr₁ sterm₁, .smtAttr1T n₂ sattr₂ sterm₂ =>
  n₁ == n₂ && sattr₁.beq sattr₂ && sterm₁.beq sterm₂

instance : BEq OtherConst where
  beq := OtherConst.beq

theorem OtherConst.beq_def {x y : OtherConst} : (x == y) = x.beq y := rfl

theorem OtherConst.beq_refl {o : OtherConst} : (o.beq o) = true := by
  cases o <;> unfold OtherConst.beq <;> simp [LamSort.beq_refl]

theorem OtherConst.eq_of_beq_eq_true {o₁ o₂ : OtherConst} (H : o₁.beq o₂) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> dsimp [beq] at H <;>
    rw [Bool.and_eq_true] at H <;> rw [Bool.and_eq_true] at H <;>
    try rw [LawfulBEq.eq_of_beq H.left.left]
  case smtAttr1T.smtAttr1T =>
    rw [LamSort.eq_of_beq_eq_true H.left.right, LamSort.eq_of_beq_eq_true H.right]

instance : LawfulBEq OtherConst where
  eq_of_beq := OtherConst.eq_of_beq_eq_true
  rfl := OtherConst.beq_refl

def OtherConst.lamCheck : OtherConst → LamSort
| .smtAttr1T _ sattr sterm => .func sattr (.func sterm sterm)

def OtherConst.interp (tyVal : TyVal.{u}) : (o : OtherConst) → o.lamCheck.interp tyVal
| .smtAttr1T _ sattr sterm => fun (_ : sattr.interp tyVal) (term : sterm.interp tyVal) => term

theorem OtherConst.interp_equiv (tyVal : TyVal.{u}) (ocwf : LamWF p s) :
  HEq (LamWF.interp tyVal ocwf) (interp tyVal p) := by
  cases ocwf <;> rfl

theorem OtherConst.LamWF.unique {o : OtherConst} {s₁ s₂ : LamSort}
  (ocwf₁ : LamWF o s₁) (ocwf₂ : LamWF o s₂) : s₁ = s₂ ∧ HEq ocwf₁ ocwf₂ := by
  cases ocwf₁ <;> cases ocwf₂ <;> trivial

theorem OtherConst.LamWF.interp_lvalIrrelevance
  (tyVal₁ tyVal₂ : TyVal.{u}) (ocwf₁ : LamWF b₁ s₁) (ocwf₂ : LamWF b₂ s₂)
  (HBeq : b₁ = b₂) (hTyVal : tyVal₁ = tyVal₂) :
  HEq (ocwf₁.interp tyVal₁) (ocwf₂.interp tyVal₂) := by
  cases HBeq; cases hTyVal; rcases OtherConst.LamWF.unique ocwf₁ ocwf₂ with ⟨⟨⟩, ⟨⟩⟩; rfl

theorem OtherConst.lamWF_complete (wf : LamWF sc s) : LamWF.ofOtherConst sc = ⟨s, wf⟩ := by
  cases wf <;> rfl

theorem OtherConst.lamCheck_of_LamWF (H : LamWF sc s) : sc.lamCheck = s := by
  cases H <;> rfl

def OtherConst.LamWF.ofCheck (H : sc.lamCheck = s) : LamWF sc s := by
  cases H; cases sc <;> constructor

end Auto.Embedding.Lam
