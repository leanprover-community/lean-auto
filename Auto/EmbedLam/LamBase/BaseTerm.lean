module

public import Auto.EmbedLam.LamBase.Const
public import Auto.EmbedLam.LamBase.BitVec
public import Auto.EmbedLam.LamBase.Later

@[expose] public section

/-! Base terms `LamBaseTerm`, `LamTyVal` and the typing of base terms -/

namespace Auto.Embedding.Lam

open ToExprExtra

/--
  Interpreted constants
  Note that `eq`, `forallE`, `existE` have `ilVal/lamILTy`
    associated with them. During proof reconstruction, we should collect
    the sort arguments of all `eq, forallE, existE` that occurs in the
    proof into `ilVal`.
  For `ilVal`, we need to use `ILLift.ofIsomTy` to construct
    `ILLift` structures. The idea is that we want the interpretation
    of reified assumptions to be definitionally
    equal to the assumption (or `GLift.up` applied to the assumption, to
    be precise), so we'll have to use the specially designed
    `of(Eq/Forall/Exist)Lift` function.
  Note that at the end of the proof, we'll have a `LamTerm.base .falseE`,
    no `=, ∀, ∃` left, so whatever `(Eq/Forall/Exist)Lift`
    structure are within the `(eq/forall/lam)Val`, the final result
    will always interpret to `GLift.up False`.
-/
inductive LamBaseTerm
  | pcst     : PropConst   → LamBaseTerm
  | bcst     : BoolConst   → LamBaseTerm
  | ncst     : NatConst    → LamBaseTerm
  | icst     : IntConst    → LamBaseTerm
  | qcst     : RatConst    → LamBaseTerm
  | scst     : StringConst → LamBaseTerm
  | bvcst    : BitVecConst → LamBaseTerm
  | ocst     : OtherConst  → LamBaseTerm
  | lcst     : LaterConst  → LamBaseTerm
  -- Versions of `eq, ∀, ∃, ite'` when we're importing external facts
  -- Note that the [import versions] of `eq, ∀, ∃, ite'` should only be used when
  --   we're importing external facts. When facts are imported, we call
  --   `resolveImport` on them and these [import versions] are turned into
  --   [non-import versions]
  | eqI      : Nat → LamBaseTerm
  | forallEI : Nat → LamBaseTerm
  | existEI  : Nat → LamBaseTerm
  | iteI     : Nat → LamBaseTerm
  -- Non-import versions of `eq, ∀, ∃`
  | eq       : LamSort → LamBaseTerm
  | forallE  : LamSort → LamBaseTerm
  | existE   : LamSort → LamBaseTerm
  | ite      : LamSort → LamBaseTerm
deriving Inhabited, Hashable, Lean.ToExpr

def LamBaseTerm.trueE := LamBaseTerm.pcst .trueE
def LamBaseTerm.falseE := LamBaseTerm.pcst .falseE
def LamBaseTerm.not := LamBaseTerm.pcst .not
def LamBaseTerm.and := LamBaseTerm.pcst .and
def LamBaseTerm.or := LamBaseTerm.pcst .or
def LamBaseTerm.imp := LamBaseTerm.pcst .imp
def LamBaseTerm.iff := LamBaseTerm.pcst .iff
def LamBaseTerm.ofProp := LamBaseTerm.bcst .ofProp
def LamBaseTerm.trueb := LamBaseTerm.bcst .trueb
def LamBaseTerm.falseb := LamBaseTerm.bcst .falseb
def LamBaseTerm.notb := LamBaseTerm.bcst .notb
def LamBaseTerm.andb := LamBaseTerm.bcst .andb
def LamBaseTerm.orb := LamBaseTerm.bcst .orb
def LamBaseTerm.natVal (n : Nat) := LamBaseTerm.ncst (.natVal n)
def LamBaseTerm.nadd := LamBaseTerm.ncst .nadd
def LamBaseTerm.nsub := LamBaseTerm.ncst .nsub
def LamBaseTerm.nmul := LamBaseTerm.ncst .nmul
def LamBaseTerm.ndiv := LamBaseTerm.ncst .ndiv
def LamBaseTerm.nmod := LamBaseTerm.ncst .nmod
def LamBaseTerm.nle := LamBaseTerm.ncst .nle
def LamBaseTerm.nlt := LamBaseTerm.ncst .nlt
def LamBaseTerm.nmax := LamBaseTerm.ncst .nmax
def LamBaseTerm.nmin := LamBaseTerm.ncst .nmin
def LamBaseTerm.iofNat := LamBaseTerm.icst .iofNat
def LamBaseTerm.inegSucc := LamBaseTerm.icst .inegSucc
def LamBaseTerm.ineg := LamBaseTerm.icst .ineg
def LamBaseTerm.iabs := LamBaseTerm.icst .iabs
def LamBaseTerm.iadd := LamBaseTerm.icst .iadd
def LamBaseTerm.isub := LamBaseTerm.icst .isub
def LamBaseTerm.imul := LamBaseTerm.icst .imul
def LamBaseTerm.idiv := LamBaseTerm.icst .idiv
def LamBaseTerm.imod := LamBaseTerm.icst .imod
def LamBaseTerm.iediv := LamBaseTerm.icst .iediv
def LamBaseTerm.iemod := LamBaseTerm.icst .iemod
def LamBaseTerm.ile := LamBaseTerm.icst .ile
def LamBaseTerm.ilt := LamBaseTerm.icst .ilt
def LamBaseTerm.imax := LamBaseTerm.icst .imax
def LamBaseTerm.imin := LamBaseTerm.icst .imin
def LamBaseTerm.qofInt := LamBaseTerm.qcst .qofInt
def LamBaseTerm.qofScientific := LamBaseTerm.qcst .qofScientific
def LamBaseTerm.qadd := LamBaseTerm.qcst .qadd
def LamBaseTerm.qsub := LamBaseTerm.qcst .qsub
def LamBaseTerm.qmul := LamBaseTerm.qcst .qmul
def LamBaseTerm.qdiv := LamBaseTerm.qcst .qdiv
def LamBaseTerm.qneg := LamBaseTerm.qcst .qneg
def LamBaseTerm.qinv := LamBaseTerm.qcst .qinv
def LamBaseTerm.qle := LamBaseTerm.qcst .qle
def LamBaseTerm.qlt := LamBaseTerm.qcst .qlt
def LamBaseTerm.qmax := LamBaseTerm.qcst .qmax
def LamBaseTerm.qmin := LamBaseTerm.qcst .qmin
def LamBaseTerm.qabs := LamBaseTerm.qcst .qabs
def LamBaseTerm.qfloor := LamBaseTerm.qcst .qfloor
def LamBaseTerm.qceil := LamBaseTerm.qcst .qceil
def LamBaseTerm.strVal (s : String) := LamBaseTerm.scst (.strVal s)
def LamBaseTerm.slength := LamBaseTerm.scst .slength
def LamBaseTerm.sapp := LamBaseTerm.scst .sapp
def LamBaseTerm.sle := LamBaseTerm.scst .sle
def LamBaseTerm.slt := LamBaseTerm.scst .slt
def LamBaseTerm.sprefixof := LamBaseTerm.scst .sprefixof
def LamBaseTerm.srepall := LamBaseTerm.scst .srepall
def LamBaseTerm.bvVal (n i : Nat) := LamBaseTerm.bvcst (.bvVal n i)
def LamBaseTerm.bvofNat (n : Nat) := LamBaseTerm.bvcst (.bvofNat n)
def LamBaseTerm.bvtoNat (n : Nat) := LamBaseTerm.bvcst (.bvtoNat n)
def LamBaseTerm.bvofInt (n : Nat) := LamBaseTerm.bvcst (.bvofInt n)
def LamBaseTerm.bvtoInt (n : Nat) := LamBaseTerm.bvcst (.bvtoInt n)
def LamBaseTerm.bvmsb (n : Nat) := LamBaseTerm.bvcst (.bvmsb n)
def LamBaseTerm.bvadd (n : Nat) := LamBaseTerm.bvcst (.bvadd n)
def LamBaseTerm.bvsub (n : Nat) := LamBaseTerm.bvcst (.bvsub n)
def LamBaseTerm.bvneg (n : Nat) := LamBaseTerm.bvcst (.bvneg n)
def LamBaseTerm.bvabs (n : Nat) := LamBaseTerm.bvcst (.bvabs n)
def LamBaseTerm.bvmul (n : Nat) := LamBaseTerm.bvcst (.bvmul n)
def LamBaseTerm.bvudiv (n : Nat) := LamBaseTerm.bvcst (.bvudiv n)
def LamBaseTerm.bvurem (n : Nat) := LamBaseTerm.bvcst (.bvurem n)
def LamBaseTerm.bvsdiv (n : Nat) := LamBaseTerm.bvcst (.bvsdiv n)
def LamBaseTerm.bvsrem (n : Nat) := LamBaseTerm.bvcst (.bvsrem n)
def LamBaseTerm.bvsmod (n : Nat) := LamBaseTerm.bvcst (.bvsmod n)
def LamBaseTerm.bvult (n : Nat) := LamBaseTerm.bvcst (.bvult n)
def LamBaseTerm.bvule (n : Nat) := LamBaseTerm.bvcst (.bvule n)
def LamBaseTerm.bvslt (n : Nat) := LamBaseTerm.bvcst (.bvslt n)
def LamBaseTerm.bvsle (n : Nat) := LamBaseTerm.bvcst (.bvsle n)
def LamBaseTerm.bvpropult (n : Nat) := LamBaseTerm.bvcst (.bvpropult n)
def LamBaseTerm.bvpropule (n : Nat) := LamBaseTerm.bvcst (.bvpropule n)
def LamBaseTerm.bvpropslt (n : Nat) := LamBaseTerm.bvcst (.bvpropslt n)
def LamBaseTerm.bvpropsle (n : Nat) := LamBaseTerm.bvcst (.bvpropsle n)
def LamBaseTerm.bvand (n : Nat) := LamBaseTerm.bvcst (.bvand n)
def LamBaseTerm.bvor (n : Nat) := LamBaseTerm.bvcst (.bvor n)
def LamBaseTerm.bvxor (n : Nat) := LamBaseTerm.bvcst (.bvxor n)
def LamBaseTerm.bvnot (n : Nat) := LamBaseTerm.bvcst (.bvnot n)
def LamBaseTerm.bvshl (n : Nat) := LamBaseTerm.bvcst (.bvshl n)
def LamBaseTerm.bvlshr (n : Nat) := LamBaseTerm.bvcst (.bvlshr n)
def LamBaseTerm.bvashr (n : Nat) := LamBaseTerm.bvcst (.bvashr n)
def LamBaseTerm.bvsmtshl (n : Nat) := LamBaseTerm.bvcst (.bvsmtshl n)
def LamBaseTerm.bvsmtlshr (n : Nat) := LamBaseTerm.bvcst (.bvsmtlshr n)
def LamBaseTerm.bvsmtashr (n : Nat) := LamBaseTerm.bvcst (.bvsmtashr n)
def LamBaseTerm.bvappend (n m : Nat) := LamBaseTerm.bvcst (.bvappend n m)
def LamBaseTerm.bvextract (n h l : Nat) := LamBaseTerm.bvcst (.bvextract n h l)
def LamBaseTerm.bvrepeat (w i : Nat) := LamBaseTerm.bvcst (.bvrepeat w i)
def LamBaseTerm.bvzeroExtend (w v : Nat) := LamBaseTerm.bvcst (.bvzeroExtend w v)
def LamBaseTerm.bvsignExtend (w v : Nat) := LamBaseTerm.bvcst (.bvsignExtend w v)
def LamBaseTerm.rzero := LamBaseTerm.lcst (.real .zero)
def LamBaseTerm.rone := LamBaseTerm.lcst (.real .one)
def LamBaseTerm.radd := LamBaseTerm.lcst (.real .add)
def LamBaseTerm.rsub := LamBaseTerm.lcst (.real .sub)
def LamBaseTerm.rmul := LamBaseTerm.lcst (.real .mul)
def LamBaseTerm.rdiv := LamBaseTerm.lcst (.real .div)
def LamBaseTerm.rneg := LamBaseTerm.lcst (.real .neg)
def LamBaseTerm.rinv := LamBaseTerm.lcst (.real .inv)
def LamBaseTerm.rofNat := LamBaseTerm.lcst (.real .ofNat)
def LamBaseTerm.rofInt := LamBaseTerm.lcst (.real .ofInt)
def LamBaseTerm.rle := LamBaseTerm.lcst (.real .le)
def LamBaseTerm.rlt := LamBaseTerm.lcst (.real .lt)
def LamBaseTerm.rmax := LamBaseTerm.lcst (.real .max)
def LamBaseTerm.rmin := LamBaseTerm.lcst (.real .min)
def LamBaseTerm.rabs := LamBaseTerm.lcst (.real .abs)
def LamBaseTerm.rofScientific := LamBaseTerm.lcst (.real .ofScientific)
def LamBaseTerm.rfloor := LamBaseTerm.lcst (.real .floor)
def LamBaseTerm.rceil := LamBaseTerm.lcst (.real .ceil)
def LamBaseTerm.rpow := LamBaseTerm.lcst (.real .pow)
def LamBaseTerm.rsqrt := LamBaseTerm.lcst (.real .sqrt)
def LamBaseTerm.rofRat := LamBaseTerm.lcst (.real .ofRat)
def LamBaseTerm.czero := LamBaseTerm.lcst (.complex .zero)
def LamBaseTerm.cone := LamBaseTerm.lcst (.complex .one)
def LamBaseTerm.cI := LamBaseTerm.lcst (.complex .I)
def LamBaseTerm.cadd := LamBaseTerm.lcst (.complex .add)
def LamBaseTerm.csub := LamBaseTerm.lcst (.complex .sub)
def LamBaseTerm.cmul := LamBaseTerm.lcst (.complex .mul)
def LamBaseTerm.cdiv := LamBaseTerm.lcst (.complex .div)
def LamBaseTerm.cneg := LamBaseTerm.lcst (.complex .neg)
def LamBaseTerm.cinv := LamBaseTerm.lcst (.complex .inv)
def LamBaseTerm.cofNat := LamBaseTerm.lcst (.complex .ofNat)
def LamBaseTerm.cofInt := LamBaseTerm.lcst (.complex .ofInt)
def LamBaseTerm.cofReal := LamBaseTerm.lcst (.complex .ofReal)
def LamBaseTerm.cre := LamBaseTerm.lcst (.complex .re)
def LamBaseTerm.cim := LamBaseTerm.lcst (.complex .im)
def LamBaseTerm.cmk := LamBaseTerm.lcst (.complex .mk)
def LamBaseTerm.cnormSq := LamBaseTerm.lcst (.complex .normSq)
def LamBaseTerm.cconj := LamBaseTerm.lcst (.complex .conj)
def LamBaseTerm.cnorm := LamBaseTerm.lcst (.complex .norm)
def LamBaseTerm.cpow := LamBaseTerm.lcst (.complex .pow)
def LamBaseTerm.cofRat := LamBaseTerm.lcst (.complex .ofRat)

def LamBaseTerm.isBcst : LamBaseTerm → Bool
| .bcst _ => true
| _       => false

def LamBaseTerm.isNcst : LamBaseTerm → Bool
| .ncst _ => true
| _       => false

def LamBaseTerm.isIcst : LamBaseTerm → Bool
| .icst _ => true
| _       => false

def LamBaseTerm.isQcst : LamBaseTerm → Bool
| .qcst _ => true
| _       => false

def LamBaseTerm.isScst : LamBaseTerm → Bool
| .scst _ => true
| _       => false

def LamBaseTerm.isBvcst : LamBaseTerm → Bool
| .bvcst _ => true
| _        => false

def LamBaseTerm.isEqI : LamBaseTerm → Bool
| .eqI _ => true
| _      => false

def LamBaseTerm.isForallEI : LamBaseTerm → Bool
| .forallEI _ => true
| _           => false

def LamBaseTerm.isExistEI : LamBaseTerm → Bool
| .existEI _ => true
| _          => false

def LamBaseTerm.isIteI : LamBaseTerm → Bool
| .iteI _ => true
| _       => false

def LamBaseTerm.isEq : LamBaseTerm → Bool
| .eq _ => true
| _     => false

def LamBaseTerm.isForallE : LamBaseTerm → Bool
| .forallE _ => true
| _          => false

def LamBaseTerm.isExistE : LamBaseTerm → Bool
| .existE _ => true
| _         => false

def LamBaseTerm.isIte : LamBaseTerm → Bool
| .ite _ => true
| _      => false

def LamBaseTerm.reprPrec (l : LamBaseTerm) (n : Nat) :=
  let s :=
    match l with
    | .pcst pc    => f!"pcst {PropConst.reprPrec pc 1}"
    | .bcst bc    => f!"bcst {BoolConst.reprPrec bc 1}"
    | .ncst nc    => f!"ncst {NatConst.reprPrec nc 1}"
    | .icst ic    => f!"icst {IntConst.reprPrec ic 1}"
    | .qcst qc    => f!"qcst {RatConst.reprPrec qc 1}"
    | .scst sc    => f!"scst {StringConst.reprPrec sc 1}"
    | .bvcst bvc  => f!"bvcst {BitVecConst.reprPrec bvc 1}"
    | .ocst oc    => f!"ocst {OtherConst.reprPrec oc 1}"
    | .lcst lc    => f!"lcst {LaterConst.reprPrec lc 1}"
    | .eqI n      => f!"eqI {n}"
    | .forallEI n => f!"forallEI {n}"
    | .existEI n  => f!"existEI {n}"
    | .iteI n     => f!"iteI {n}"
    | .eq s       => f!"eq {LamSort.reprPrec s 1}"
    | .forallE s  => f!"forallE {LamSort.reprPrec s 1}"
    | .existE s   => f!"existE {LamSort.reprPrec s 1}"
    | .ite n      => f!"ite {n}"
  if n == 0 then
    f!"Auto.Embedding.Lam.LamBaseTerm." ++ s
  else
    f!"(.{s})"

instance : Repr LamBaseTerm where
  reprPrec := LamBaseTerm.reprPrec

def LamBaseTerm.toString : LamBaseTerm → String
| .pcst pc    => s!"{pc}"
| .bcst bc    => s!"{bc}"
| .ncst nc    => s!"{nc}"
| .icst ic    => s!"{ic}"
| .qcst qc    => s!"{qc}"
| .scst sc    => s!"{sc}"
| .bvcst bvc  => s!"{bvc}"
| .ocst oc    => s!"{oc}"
| .lcst lc    => s!"{lc}"
| .eqI _      => "="
| .forallEI _ => "∀"
| .existEI _  => "∃"
| .iteI _     => "ite"
| .eq _       => "="
| .forallE _  => "∀"
| .existE _   => "∃"
| .ite _      => "ite"

instance : ToString LamBaseTerm where
  toString := LamBaseTerm.toString

def LamBaseTerm.beq : LamBaseTerm → LamBaseTerm → Bool
| .pcst pc₁,    .pcst pc₂    => pc₁.beq pc₂
| .bcst bc₁,    .bcst bc₂    => bc₁.beq bc₂
| .ncst nc₁,    .ncst nc₂    => nc₁.beq nc₂
| .icst ic₁,    .icst ic₂    => ic₁.beq ic₂
| .qcst qc₁,    .qcst qc₂    => qc₁.beq qc₂
| .scst sc₁,    .scst sc₂    => sc₁.beq sc₂
| .bvcst l₁,    .bvcst l₂    => l₁.beq l₂
| .ocst o₁,     .ocst o₂     => o₁.beq o₂
| .lcst l₁,     .lcst l₂     => l₁.beq l₂
| .eqI n₁,      .eqI n₂      => n₁.beq n₂
| .forallEI n₁, .forallEI n₂ => n₁.beq n₂
| .existEI n₁,  .existEI n₂  => n₁.beq n₂
| .iteI n₁,     .iteI n₂     => n₁.beq n₂
| .eq s₁,       .eq s₂       => s₁.beq s₂
| .forallE s₁,  .forallE s₂  => s₁.beq s₂
| .existE s₁,   .existE s₂   => s₁.beq s₂
| .ite s₁,      .ite s₂      => s₁.beq s₂
| _,            _            => false

instance : BEq LamBaseTerm where
  beq := LamBaseTerm.beq

theorem LamBaseTerm.beq_refl {b : LamBaseTerm} : (b.beq b) = true := by
  cases b <;> first | rfl | apply LamSort.beq_refl | apply Nat.beq_refl | skip
  case pcst pc => apply BEq.rfl (α := PropConst)
  case bcst bc => apply BEq.rfl (α := BoolConst)
  case ncst n => apply BEq.rfl (α := NatConst)
  case icst i => apply BEq.rfl (α := IntConst)
  case qcst q => apply BEq.rfl (α := RatConst)
  case scst s => apply BEq.rfl (α := StringConst)
  case bvcst s => apply BEq.rfl (α := BitVecConst)
  case ocst o => apply BEq.rfl (α := OtherConst)
  case lcst l => apply BEq.rfl (α := LaterConst)

theorem LamBaseTerm.eq_of_beq_eq_true {b₁ b₂ : LamBaseTerm} (H : b₁.beq b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> (first | contradiction | rfl | apply congrArg) <;>
    (try apply LamSort.eq_of_beq_eq_true H) <;> (try apply Nat.eq_of_beq_eq_true H)
  case pcst.pcst pc₁ pc₂ => apply LawfulBEq.eq_of_beq (α := PropConst) H
  case bcst.bcst bc₁ bc₂ => apply LawfulBEq.eq_of_beq (α := BoolConst) H
  case ncst.ncst nc₁ nc₂ => apply LawfulBEq.eq_of_beq (α := NatConst) H
  case icst.icst n₁ n₂ => apply LawfulBEq.eq_of_beq (α := IntConst) H
  case qcst.qcst q₁ q₂ => apply LawfulBEq.eq_of_beq (α := RatConst) H
  case scst.scst s₁ s₂ => apply LawfulBEq.eq_of_beq (α := StringConst) H
  case bvcst.bvcst v₁ v₂ => apply LawfulBEq.eq_of_beq (α := BitVecConst) H
  case ocst.ocst o₁ o₂ => apply LawfulBEq.eq_of_beq (α := OtherConst) H
  case lcst.lcst l₁ l₂ => apply LawfulBEq.eq_of_beq (α := LaterConst) H

instance : LawfulBEq LamBaseTerm where
  eq_of_beq := LamBaseTerm.eq_of_beq_eq_true
  rfl := LamBaseTerm.beq_refl

def LamBaseTerm.containsSort (b : LamBaseTerm) (s : LamSort) : Bool :=
  match b with
  | .pcst _     => false
  | .bcst _     => false
  | .ncst _     => false
  | .icst _     => false
  | .qcst _     => false
  | .scst _     => false
  | .bvcst _    => false
  | .ocst _     => false
  | .lcst _     => false
  | .eqI _      => false
  | .forallEI _ => false
  | .existEI _  => false
  | .iteI _     => false
  | .eq s'      => s'.contains s
  | .forallE s' => s'.contains s
  | .existE s'  => s'.contains s
  | .ite s'     => s'.contains s

structure LamTyVal where
  lamVarTy     : Nat → LamSort
  lamILTy      : Nat → LamSort
  lamEVarTy    : Nat → LamSort

instance : Inhabited LamTyVal where
  default := let func := fun _ => .atom 0; ⟨func, func, func⟩

def LamBaseTerm.lamCheck (ltv : LamTyVal) : LamBaseTerm → LamSort
| .pcst pc    => pc.lamCheck
| .bcst bc    => bc.lamCheck
| .ncst nc    => nc.lamCheck
| .icst ic    => ic.lamCheck
| .qcst qc    => qc.lamCheck
| .scst sc    => sc.lamCheck
| .bvcst bvc  => bvc.lamCheck
| .ocst oc    => oc.lamCheck
| .lcst lc    => lc.lamCheck
| .eqI n      =>
  let s := ltv.lamILTy n
  .func s (.func s (.base .prop))
| .forallEI n =>
  let s := ltv.lamILTy n
  .func (.func s (.base .prop)) (.base .prop)
| .existEI n  =>
  let s := ltv.lamILTy n
  .func (.func s (.base .prop)) (.base .prop)
| .iteI n     =>
  let s := ltv.lamILTy n
  .func (.base .prop) (.func s (.func s s))
| .eq s       => .func s (.func s (.base .prop))
| .forallE s  => .func (.func s (.base .prop)) (.base .prop)
| .existE s   => .func (.func s (.base .prop)) (.base .prop)
| .ite s      => .func (.base .prop) (.func s (.func s s))

inductive LamBaseTerm.LamWF (ltv : LamTyVal) : LamBaseTerm → LamSort → Type
  | ofPcst       : (pcwf : PropConst.LamWF pc s) → LamWF ltv (.pcst pc) s
  | ofBcst       : (bcwf : BoolConst.LamWF bc s) → LamWF ltv (.bcst bc) s
  | ofNcst       : (ncwf : NatConst.LamWF nc s) → LamWF ltv (.ncst nc) s
  | ofIcst       : (icwf : IntConst.LamWF ic s) → LamWF ltv (.icst ic) s
  | ofQcst       : (qcwf : RatConst.LamWF qc s) → LamWF ltv (.qcst qc) s
  | ofScst       : (scwf : StringConst.LamWF sc s) → LamWF ltv (.scst sc) s
  | ofBvcst      : (bvcwf : BitVecConst.LamWF bvc s) → LamWF ltv (.bvcst bvc) s
  | ofOcst       : (ocwf : OtherConst.LamWF oc s) → LamWF ltv (.ocst oc) s
  | ofLcst       : (lcwf : LaterConst.LamWF lc s) → LamWF ltv (.lcst lc) s
  | ofEqI n      : LamWF ltv (.eqI n) (.func (ltv.lamILTy n) (.func (ltv.lamILTy n) (.base .prop)))
  | ofForallEI n : LamWF ltv (.forallEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
  | ofExistEI n  : LamWF ltv (.existEI n) (.func (.func (ltv.lamILTy n) (.base .prop)) (.base .prop))
  | ofIteI n     : LamWF ltv (.iteI n) (.func (.base .prop) (.func (ltv.lamILTy n) (.func (ltv.lamILTy n) (ltv.lamILTy n))))
  | ofEq s       : LamWF ltv (.eq s) (.func s (.func s (.base .prop)))
  | ofForallE s  : LamWF ltv (.forallE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofExistE s   : LamWF ltv (.existE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofIte s      : LamWF ltv (.ite s) (.func (.base .prop) (.func s (.func s s)))

theorem LamBaseTerm.LamWF.unique {ltv : LamTyVal} {b : LamBaseTerm} {s₁ s₂ : LamSort}
  (lbwf₁ : LamWF ltv b s₁) (lbwf₂ : LamWF ltv b s₂) : s₁ = s₂ ∧ HEq lbwf₁ lbwf₂ := by
  cases lbwf₁ <;> cases lbwf₂ <;> try trivial
  case ofPcst.ofPcst pc wf₁ wf₂ =>
    rcases PropConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofBcst.ofBcst bc wf₁ wf₂ =>
    rcases BoolConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofNcst.ofNcst bc wf₁ wf₂ =>
    rcases NatConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofIcst.ofIcst ic wf₁ wf₂ =>
    rcases IntConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofQcst.ofQcst qc wf₁ wf₂ =>
    rcases RatConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofScst.ofScst sc wf₁ wf₂ =>
    rcases StringConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofBvcst.ofBvcst bvc wf₁ wf₂ =>
    rcases BitVecConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofOcst.ofOcst oc wf₁ wf₂ =>
    rcases OtherConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial
  case ofLcst.ofLcst lc wf₁ wf₂ =>
    rcases LaterConst.LamWF.unique wf₁ wf₂ with ⟨⟨⟩, ⟨⟩⟩; trivial

def LamBaseTerm.LamWF.eVarIrrelevance
  (hLamVarTy : ltv₁.lamVarTy = ltv₂.lamVarTy)
  (hLamILTy : ltv₁.lamILTy = ltv₂.lamILTy)
  (lbwf : LamWF ltv₁ b s) : LamWF ltv₂ b s := by
  cases b <;> cases lbwf <;> (try constructor) <;> cases ltv₁ <;> cases ltv₂ <;>
    cases hLamVarTy <;> cases hLamILTy <;> first | assumption | constructor

abbrev LamBaseTerm.LamWF.ofTrueE {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofTrueE
abbrev LamBaseTerm.LamWF.ofFalseE {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofFalseE
abbrev LamBaseTerm.LamWF.ofNot {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofNot
abbrev LamBaseTerm.LamWF.ofAnd {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofAnd
abbrev LamBaseTerm.LamWF.ofOr {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofOr
abbrev LamBaseTerm.LamWF.ofImp {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofImp
abbrev LamBaseTerm.LamWF.ofIff {ltv : LamTyVal} := LamWF.ofPcst (ltv:=ltv) .ofIff
abbrev LamBaseTerm.LamWF.ofOfProp {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofOfProp
abbrev LamBaseTerm.LamWF.ofTrueB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofTrueB
abbrev LamBaseTerm.LamWF.ofFalseB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofFalseB
abbrev LamBaseTerm.LamWF.ofNotB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofNotB
abbrev LamBaseTerm.LamWF.ofAndB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofAndB
abbrev LamBaseTerm.LamWF.ofOrB {ltv : LamTyVal} := LamWF.ofBcst (ltv:=ltv) .ofOrB
abbrev LamBaseTerm.LamWF.ofNatVal {ltv : LamTyVal} (n : Nat) := LamWF.ofNcst (ltv:=ltv) (.ofNatVal n)
abbrev LamBaseTerm.LamWF.ofNadd {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNadd
abbrev LamBaseTerm.LamWF.ofNsub {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNsub
abbrev LamBaseTerm.LamWF.ofNmul {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmul
abbrev LamBaseTerm.LamWF.ofNdiv {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNdiv
abbrev LamBaseTerm.LamWF.ofNmod {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmod
abbrev LamBaseTerm.LamWF.ofNle {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNle
abbrev LamBaseTerm.LamWF.ofNlt {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNlt
abbrev LamBaseTerm.LamWF.ofNmax {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmax
abbrev LamBaseTerm.LamWF.ofNmin {ltv : LamTyVal} := LamWF.ofNcst (ltv:=ltv) .ofNmin
abbrev LamBaseTerm.LamWF.ofIOfNat {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIOfNat
abbrev LamBaseTerm.LamWF.ofINegSucc {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofINegSucc
abbrev LamBaseTerm.LamWF.ofIneg {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIneg
abbrev LamBaseTerm.LamWF.ofIabs {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIabs
abbrev LamBaseTerm.LamWF.ofIadd {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIadd
abbrev LamBaseTerm.LamWF.ofIsub {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIsub
abbrev LamBaseTerm.LamWF.ofImul {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImul
abbrev LamBaseTerm.LamWF.ofIdiv {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIdiv
abbrev LamBaseTerm.LamWF.ofImod {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImod
abbrev LamBaseTerm.LamWF.ofIediv {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIediv
abbrev LamBaseTerm.LamWF.ofIemod {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIemod
abbrev LamBaseTerm.LamWF.ofIle {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIle
abbrev LamBaseTerm.LamWF.ofIlt {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofIlt
abbrev LamBaseTerm.LamWF.ofImax {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImax
abbrev LamBaseTerm.LamWF.ofImin {ltv : LamTyVal} := LamWF.ofIcst (ltv:=ltv) .ofImin
abbrev LamBaseTerm.LamWF.ofQOfInt {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQOfInt
abbrev LamBaseTerm.LamWF.ofQOfScientific {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQOfScientific
abbrev LamBaseTerm.LamWF.ofQadd {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQadd
abbrev LamBaseTerm.LamWF.ofQsub {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQsub
abbrev LamBaseTerm.LamWF.ofQmul {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQmul
abbrev LamBaseTerm.LamWF.ofQdiv {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQdiv
abbrev LamBaseTerm.LamWF.ofQneg {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQneg
abbrev LamBaseTerm.LamWF.ofQinv {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQinv
abbrev LamBaseTerm.LamWF.ofQle {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQle
abbrev LamBaseTerm.LamWF.ofQlt {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQlt
abbrev LamBaseTerm.LamWF.ofQmax {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQmax
abbrev LamBaseTerm.LamWF.ofQmin {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQmin
abbrev LamBaseTerm.LamWF.ofQabs {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQabs
abbrev LamBaseTerm.LamWF.ofQfloor {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQfloor
abbrev LamBaseTerm.LamWF.ofQceil {ltv : LamTyVal} := LamWF.ofQcst (ltv:=ltv) .ofQceil
abbrev LamBaseTerm.LamWF.ofStrVal {ltv : LamTyVal} (s : String) := LamWF.ofScst (ltv:=ltv) (.ofStrVal s)
abbrev LamBaseTerm.LamWF.ofSlength {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSlength
abbrev LamBaseTerm.LamWF.ofSapp {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSapp
abbrev LamBaseTerm.LamWF.ofSle {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSle
abbrev LamBaseTerm.LamWF.ofSlt {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSlt
abbrev LamBaseTerm.LamWF.ofSprefixof {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSprefixof
abbrev LamBaseTerm.LamWF.ofSrepall {ltv : LamTyVal} := LamWF.ofScst (ltv:=ltv) .ofSrepall
abbrev LamBaseTerm.LamWF.ofBvVal {ltv : LamTyVal} (n i : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvVal n i)
abbrev LamBaseTerm.LamWF.ofBvofNat {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvofNat n)
abbrev LamBaseTerm.LamWF.ofBvtoNat {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvtoNat n)
abbrev LamBaseTerm.LamWF.ofBvofInt {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvofInt n)
abbrev LamBaseTerm.LamWF.ofBvtoInt {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvtoInt n)
abbrev LamBaseTerm.LamWF.ofBvmsb {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvmsb n)
abbrev LamBaseTerm.LamWF.ofBvadd {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvadd n)
abbrev LamBaseTerm.LamWF.ofBvsub {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsub n)
abbrev LamBaseTerm.LamWF.ofBvneg {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvneg n)
abbrev LamBaseTerm.LamWF.ofBvabs {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvabs n)
abbrev LamBaseTerm.LamWF.ofBvmul {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvmul n)
abbrev LamBaseTerm.LamWF.ofBvudiv {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvudiv n)
abbrev LamBaseTerm.LamWF.ofBvurem {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvurem n)
abbrev LamBaseTerm.LamWF.ofBvsdiv {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsdiv n)
abbrev LamBaseTerm.LamWF.ofBvsrem {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsrem n)
abbrev LamBaseTerm.LamWF.ofBvsmod {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmod n)
abbrev LamBaseTerm.LamWF.ofBvult {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvult n)
abbrev LamBaseTerm.LamWF.ofBvule {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvule n)
abbrev LamBaseTerm.LamWF.ofBvslt {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvslt n)
abbrev LamBaseTerm.LamWF.ofBvsle {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsle n)
abbrev LamBaseTerm.LamWF.ofBvand {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvand n)
abbrev LamBaseTerm.LamWF.ofBvor {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvor n)
abbrev LamBaseTerm.LamWF.ofBvxor {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvxor n)
abbrev LamBaseTerm.LamWF.ofBvnot {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvnot n)
abbrev LamBaseTerm.LamWF.ofBvshl {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvshl n)
abbrev LamBaseTerm.LamWF.ofBvlshr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvlshr n)
abbrev LamBaseTerm.LamWF.ofBvashr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvashr n)
abbrev LamBaseTerm.LamWF.ofBvsmtshl {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmtshl n)
abbrev LamBaseTerm.LamWF.ofBvsmtlshr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmtlshr n)
abbrev LamBaseTerm.LamWF.ofBvsmtashr {ltv : LamTyVal} (n : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsmtashr n)
abbrev LamBaseTerm.LamWF.ofBvappend {ltv : LamTyVal} (n m : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvappend n m)
abbrev LamBaseTerm.LamWF.ofBvextract {ltv : LamTyVal} (n h l : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvextract n h l)
abbrev LamBaseTerm.LamWF.ofBvrepeat {ltv : LamTyVal} (w i : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvrepeat w i)
abbrev LamBaseTerm.LamWF.ofBvzeroExtend {ltv : LamTyVal} (w v : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvzeroExtend w v)
abbrev LamBaseTerm.LamWF.ofBvsignExtend {ltv : LamTyVal} (w v : Nat) := LamWF.ofBvcst (ltv:=ltv) (.ofBvsignExtend w v)
abbrev LamBaseTerm.LamWF.ofRzero {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofZero)
abbrev LamBaseTerm.LamWF.ofRone {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofOne)
abbrev LamBaseTerm.LamWF.ofRadd {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofAdd)
abbrev LamBaseTerm.LamWF.ofRsub {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofSub)
abbrev LamBaseTerm.LamWF.ofRmul {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofMul)
abbrev LamBaseTerm.LamWF.ofRdiv {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofDiv)
abbrev LamBaseTerm.LamWF.ofRneg {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofNeg)
abbrev LamBaseTerm.LamWF.ofRinv {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofInv)
abbrev LamBaseTerm.LamWF.ofRofNat {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofOfNat)
abbrev LamBaseTerm.LamWF.ofRofInt {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofOfInt)
abbrev LamBaseTerm.LamWF.ofRle {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofLe)
abbrev LamBaseTerm.LamWF.ofRlt {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofLt)
abbrev LamBaseTerm.LamWF.ofRmax {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofMax)
abbrev LamBaseTerm.LamWF.ofRmin {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofMin)
abbrev LamBaseTerm.LamWF.ofRabs {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofAbs)
abbrev LamBaseTerm.LamWF.ofRofScientific {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofOfScientific)
abbrev LamBaseTerm.LamWF.ofRfloor {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofFloor)
abbrev LamBaseTerm.LamWF.ofRceil {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofCeil)
abbrev LamBaseTerm.LamWF.ofRpow {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofPow)
abbrev LamBaseTerm.LamWF.ofRsqrt {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofSqrt)
abbrev LamBaseTerm.LamWF.ofRofRat {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofReal .ofOfRat)
abbrev LamBaseTerm.LamWF.ofCzero {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofZero)
abbrev LamBaseTerm.LamWF.ofCone {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofOne)
abbrev LamBaseTerm.LamWF.ofCI {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofI)
abbrev LamBaseTerm.LamWF.ofCadd {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofAdd)
abbrev LamBaseTerm.LamWF.ofCsub {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofSub)
abbrev LamBaseTerm.LamWF.ofCmul {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofMul)
abbrev LamBaseTerm.LamWF.ofCdiv {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofDiv)
abbrev LamBaseTerm.LamWF.ofCneg {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofNeg)
abbrev LamBaseTerm.LamWF.ofCinv {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofInv)
abbrev LamBaseTerm.LamWF.ofCofNat {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofOfNat)
abbrev LamBaseTerm.LamWF.ofCofInt {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofOfInt)
abbrev LamBaseTerm.LamWF.ofCofReal {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofOfReal)
abbrev LamBaseTerm.LamWF.ofCre {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofRe)
abbrev LamBaseTerm.LamWF.ofCim {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofIm)
abbrev LamBaseTerm.LamWF.ofCmk {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofMk)
abbrev LamBaseTerm.LamWF.ofCnormSq {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofNormSq)
abbrev LamBaseTerm.LamWF.ofCconj {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofConj)
abbrev LamBaseTerm.LamWF.ofCnorm {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofNorm)
abbrev LamBaseTerm.LamWF.ofCpow {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofPow)
abbrev LamBaseTerm.LamWF.ofCofRat {ltv : LamTyVal} := LamWF.ofLcst (ltv:=ltv) (.ofComplex .ofOfRat)

def LamBaseTerm.LamWF.getPcst (wf : LamWF ltv (.pcst pc) s) : PropConst.LamWF pc s :=
  match wf with | .ofPcst pcwf => pcwf

def LamBaseTerm.LamWF.getBcst (wf : LamWF ltv (.bcst bc) s) : BoolConst.LamWF bc s :=
  match wf with | .ofBcst bcwf => bcwf

def LamBaseTerm.LamWF.getNcst (wf : LamWF ltv (.ncst nc) s) : NatConst.LamWF nc s :=
  match wf with | .ofNcst ncwf => ncwf

def LamBaseTerm.LamWF.getIcst (wf : LamWF ltv (.icst ic) s) : IntConst.LamWF ic s :=
  match wf with | .ofIcst icwf => icwf

def LamBaseTerm.LamWF.getQcst (wf : LamWF ltv (.qcst qc) s) : RatConst.LamWF qc s :=
  match wf with | .ofQcst qcwf => qcwf

def LamBaseTerm.LamWF.getScst (wf : LamWF ltv (.scst sc) s) : StringConst.LamWF sc s :=
  match wf with | .ofScst scwf => scwf

def LamBaseTerm.LamWF.getBvcst (wf : LamWF ltv (.bvcst bvc) s) : BitVecConst.LamWF bvc s :=
  match wf with | .ofBvcst bvcwf => bvcwf

def LamBaseTerm.LamWF.getLcst (wf : LamWF ltv (.lcst lc) s) : LaterConst.LamWF lc s :=
  match wf with | .ofLcst lcwf => lcwf

def LamBaseTerm.LamWF.ofLamBaseTerm (ltv : LamTyVal) : (b : LamBaseTerm) → (s : LamSort) × LamBaseTerm.LamWF ltv b s
| .pcst pc    => have ⟨s, wf⟩ := PropConst.LamWF.ofPropConst pc; ⟨s, .ofPcst wf⟩
| .bcst bc    => have ⟨s, wf⟩ := BoolConst.LamWF.ofBoolConst bc; ⟨s, .ofBcst wf⟩
| .ncst nc    => have ⟨s, wf⟩ := NatConst.LamWF.ofNatConst nc; ⟨s, .ofNcst wf⟩
| .icst ic    => have ⟨s, wf⟩ := IntConst.LamWF.ofIntConst ic; ⟨s, .ofIcst wf⟩
| .qcst qc    => have ⟨s, wf⟩ := RatConst.LamWF.ofRatConst qc; ⟨s, .ofQcst wf⟩
| .scst sc    => have ⟨s, wf⟩ := StringConst.LamWF.ofStringConst sc; ⟨s, .ofScst wf⟩
| .bvcst bvc  => have ⟨s, wf⟩ := BitVecConst.LamWF.ofBitVecConst bvc; ⟨s, .ofBvcst wf⟩
| .ocst oc    => have ⟨s, wf⟩ := OtherConst.LamWF.ofOtherConst oc; ⟨s, .ofOcst wf⟩
| .lcst lc    => have ⟨s, wf⟩ := LaterConst.LamWF.ofLaterConst lc; ⟨s, .ofLcst wf⟩
| .eqI n      => ⟨.func _ (.func _ (.base .prop)), .ofEqI n⟩
| .forallEI n => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallEI n⟩
| .existEI n  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistEI n⟩
| .iteI n     => ⟨.func (.base .prop) (.func _ (.func _ _)), .ofIteI n⟩
| .eq s       => ⟨.func _ (.func _ (.base .prop)), .ofEq s⟩
| .forallE s  => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofForallE s⟩
| .existE s   => ⟨.func (.func _ (.base .prop)) (.base .prop), .ofExistE s⟩
| .ite s      => ⟨.func (.base .prop) (.func _ (.func _ _)), .ofIte s⟩

theorem LamBaseTerm.lamWF_complete (wf : LamWF ltv b s) : LamWF.ofLamBaseTerm ltv b = ⟨s, wf⟩ := by
  cases wf <;> try rfl
  case ofPcst pc wf => dsimp [LamWF.ofLamBaseTerm]; rw [PropConst.lamWF_complete wf]
  case ofBcst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [BoolConst.lamWF_complete wf]
  case ofNcst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [NatConst.lamWF_complete wf]
  case ofIcst ic wf => dsimp [LamWF.ofLamBaseTerm]; rw [IntConst.lamWF_complete]
  case ofQcst qc wf => dsimp [LamWF.ofLamBaseTerm]; rw [RatConst.lamWF_complete wf]
  case ofScst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [StringConst.lamWF_complete wf]
  case ofBvcst bc wf => dsimp [LamWF.ofLamBaseTerm]; rw [BitVecConst.lamWF_complete wf]
  case ofOcst oc wf => dsimp [LamWF.ofLamBaseTerm]; rw [OtherConst.lamWF_complete wf]
  case ofLcst lc wf => dsimp [LamWF.ofLamBaseTerm]; rw [LaterConst.lamWF_complete wf]

theorem LamBaseTerm.lamCheck_of_LamWF (H : LamWF ltv b s) : b.lamCheck ltv = s := by
  cases H <;> try rfl
  case ofPcst bc wf => apply PropConst.lamCheck_of_LamWF wf
  case ofBcst bc wf => apply BoolConst.lamCheck_of_LamWF wf
  case ofNcst bc wf => apply NatConst.lamCheck_of_LamWF wf
  case ofIcst bc wf => apply IntConst.lamCheck_of_LamWF wf
  case ofQcst qc wf => apply RatConst.lamCheck_of_LamWF wf
  case ofScst sc wf => apply StringConst.lamCheck_of_LamWF wf
  case ofBvcst sc wf => apply BitVecConst.lamCheck_of_LamWF wf
  case ofOcst oc wf => apply OtherConst.lamCheck_of_LamWF wf
  case ofLcst lc wf => apply LaterConst.lamCheck_of_LamWF wf

def LamBaseTerm.LamWF.ofCheck (H : b.lamCheck ltv = s) : LamWF ltv b s := by
  cases H; cases b <;> constructor
  case refl.pcst => apply PropConst.LamWF.ofCheck; rfl
  case refl.bcst => apply BoolConst.LamWF.ofCheck; rfl
  case refl.ncst => apply NatConst.LamWF.ofCheck; rfl
  case refl.icst => apply IntConst.LamWF.ofCheck; rfl
  case refl.qcst => apply RatConst.LamWF.ofCheck; rfl
  case refl.scst => apply StringConst.LamWF.ofCheck; rfl
  case refl.bvcst => apply BitVecConst.LamWF.ofCheck; rfl
  case refl.ocst => apply OtherConst.LamWF.ofCheck; rfl
  case refl.lcst => apply LaterConst.LamWF.ofCheck; rfl

end Auto.Embedding.Lam
