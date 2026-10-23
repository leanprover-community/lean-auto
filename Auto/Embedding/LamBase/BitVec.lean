module

public import Auto.Embedding.LamBase.Sort
public import Auto.Embedding.LamBase.ConstMacro

@[expose] public section

/-! Interpreted `BitVec` constants -/

namespace Auto.Embedding.Lam

open ToExprExtra

inductive BVAOp where
  | add
  | sub
  | mul
  -- `BitVec.smtUDiv`
  | udiv
  | urem
  -- `BitVec.smtSDiv`
  | sdiv
  | srem
  | smod
  deriving Inhabited, Hashable, Lean.ToExpr

def BVAOp.repr (n : Nat) : BVAOp → String
| .add  => s!"bvadd {n}"
| .sub  => s!"bvsub {n}"
| .mul  => s!"bvmul {n}"
| .udiv => s!"bvudiv {n}"
| .urem => s!"bvurem {n}"
| .sdiv => s!"bvsdiv {n}"
| .srem => s!"bvsrem {n}"
| .smod => s!"bvsmod {n}"

def BVAOp.toString : BVAOp → String
| .add  => s!"+"
| .sub  => s!"-"
| .mul  => s!"*"
| .udiv => s!"/ᵤ"
| .urem => s!"%ᵤ"
| .sdiv => s!"/"
| .srem => s!"%ᵣ"
| .smod => s!"%"

def BVAOp.beq : BVAOp → BVAOp → Bool
| add,  add  => true
| sub,  sub  => true
| mul,  mul  => true
| udiv, udiv => true
| urem, urem => true
| sdiv, sdiv => true
| srem, srem => true
| smod, smod => true
| _,    _    => false

instance : BEq BVAOp where
  beq := BVAOp.beq

theorem BVAOp.beq_refl {a : BVAOp} : (a.beq a) = true := by
  cases a <;> rfl

theorem BVAOp.eq_of_beq_eq_true {a₁ a₂ : BVAOp} (H : a₁.beq a₂) : a₁ = a₂ := by
  cases a₁ <;> cases a₂ <;> first | contradiction | rfl

instance : LawfulBEq BVAOp where
  eq_of_beq := BVAOp.eq_of_beq_eq_true
  rfl := BVAOp.beq_refl

def BVAOp.interp (n : Nat) : (op : BVAOp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n)
| .add  => bvaddLift n
| .sub  => bvsubLift n
| .mul  => bvmulLift n
| .udiv => bvudivLift n
| .urem => bvuremLift n
| .sdiv => bvsdivLift n
| .srem => bvsremLift n
| .smod => bvsmodLift n

inductive BVCmp where
  | ult
  | ule
  | slt
  | sle
  deriving Inhabited, Hashable, Lean.ToExpr

def BVCmp.repr (n : Nat) (prop? : Bool) (cmp : BVCmp) : String :=
  let pStr := if prop? then "p" else ""
  match cmp with
  | .ult => s!"bv{pStr}ult {n}"
  | .ule => s!"bv{pStr}ule {n}"
  | .slt => s!"bv{pStr}slt {n}"
  | .sle => s!"bv{pStr}sle {n}"

def BVCmp.toString (prop? : Bool) (cmp : BVCmp) : String :=
  let pStr := if prop? then "ₚ" else ""
  match cmp with
  | .ult => s!"{pStr}<ᵤ"
  | .ule => s!"{pStr}≤ᵤ"
  | .slt => s!"{pStr}<"
  | .sle => s!"{pStr}≤"

def BVCmp.beq : BVCmp → BVCmp → Bool
| .ult, .ult => true
| .ule, .ule => true
| .slt, .slt => true
| .sle, .sle => true
| _,    _    => false

instance : BEq BVCmp where
  beq := BVCmp.beq

theorem BVCmp.beq_refl {c : BVCmp} : (c.beq c) = true := by
  cases c <;> rfl

theorem BVCmp.eq_of_beq_eq_true {c₁ c₂ : BVCmp} (H : c₁.beq c₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> first | contradiction | rfl

instance : LawfulBEq BVCmp where
  eq_of_beq := BVCmp.eq_of_beq_eq_true
  rfl := BVCmp.beq_refl

def BVCmp.interp (n : Nat) : (op : BVCmp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} Bool
| .ult => bvultLift n
| .ule => bvuleLift n
| .slt => bvsltLift n
| .sle => bvsleLift n

def BVCmp.propinterp (n : Nat) : (op : BVCmp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} Prop
| .ult => bvpropultLift n
| .ule => bvpropuleLift n
| .slt => bvpropsltLift n
| .sle => bvpropsleLift n

inductive BVShOp where
  | shl
  | lshr
  | ashr
  deriving Inhabited, Hashable, Lean.ToExpr

def BVShOp.repr (n : Nat) (smt? : Bool) (shOp : BVShOp) : String :=
  let smtStr := if smt? then "smt" else ""
  match shOp with
  | .shl  => s!"bv{smtStr}shl {n}"
  | .lshr => s!"bv{smtStr}lshr {n}"
  | .ashr => s!"bv{smtStr}ashr {n}"

def BVShOp.toString (smt? : Bool) (shOp : BVShOp) : String :=
  let smtStr := if smt? then "ₛ" else ""
  match shOp with
  | .shl => s!"<<<{smtStr}"
  | .lshr => s!">>>{smtStr}"
  | .ashr => s!">>>ₐ{smtStr}"

def BVShOp.beq : BVShOp → BVShOp → Bool
| shl,  shl  => true
| lshr, lshr => true
| ashr, ashr => true
| _,    _    => false

instance : BEq BVShOp where
  beq := BVShOp.beq

theorem BVShOp.beq_refl {s : BVShOp} : (s.beq s) = true := by
  cases s <;> rfl

theorem BVShOp.eq_of_beq_eq_true {s₁ s₂ : BVShOp} (H : s₁.beq s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> first | contradiction | rfl

instance : LawfulBEq BVShOp where
  eq_of_beq := BVShOp.eq_of_beq_eq_true
  rfl := BVShOp.beq_refl

def BVShOp.interp (n : Nat) : (op : BVShOp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} Nat → GLift.{1, u} (BitVec n)
| .shl         => bvshlLift n
| .lshr        => bvlshrLift n
| .ashr        => bvashrLift n

def BVShOp.smtinterp (n : Nat) : (op : BVShOp) →
  GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n) → GLift.{1, u} (BitVec n)
| .shl         => bvsmtshlLift n
| .lshr        => bvsmtlshrLift n
| .ashr        => bvsmtashrLift n

-- `ToString` instances for the helper op types, used by the `mkConstFamily`
-- macro's auto-generated `reprAux` for `BitVecConst`.  `BVCmp.toString` and
-- `BVShOp.toString` take a `Bool` flag (prop?/smt?); we default to `false`,
-- which gives the unflagged display form.
instance : ToString BVAOp := ⟨BVAOp.toString⟩
instance : ToString BVCmp := ⟨BVCmp.toString false⟩
instance : ToString BVShOp := ⟨BVShOp.toString false⟩

/--
  Following `https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV`
-/
inductive BitVecConst
  -- `BitVec.ofNat n i, but requires both arguments to be nat literals`
  | bvVal (n : Nat) (i : Nat)
  | bvofNat (n : Nat)
  | bvtoNat (n : Nat)
  | bvofInt (n : Nat)
  | bvtoInt (n : Nat)
  | bvmsb (n : Nat)
  -- zero : Use `bvofNat`
  -- allones : Use `bvneg`
  | bvaOp (n : Nat) (op : BVAOp)
  | bvneg (n : Nat)
  | bvabs (n : Nat)
  -- Bool-valued comparison: `BitVec n → BitVec n → Bool`
  | bvcmp (n : Nat) (op : BVCmp)
  -- Prop-valued comparison: `BitVec n → BitVec n → Prop`
  | bvpropcmp (n : Nat) (op : BVCmp)
  | bvand (n : Nat)
  | bvor (n : Nat)
  | bvxor (n : Nat)
  | bvnot (n : Nat)
  -- Lean version: `BitVec n → Nat → BitVec n`
  | bvshOp (n : Nat) (op : BVShOp)
  -- SMT version: `BitVec n → BitVec n → BitVec n`
  | bvsmtshOp (n : Nat) (op : BVShOp)
  | bvappend (n m : Nat)
  | bvextract (n hi lo : Nat)
  -- `BitVec.replicate`
  | bvrepeat (w i : Nat)
  | bvzeroExtend (w v : Nat)
  | bvsignExtend (w v : Nat)
deriving Inhabited, Hashable, Lean.ToExpr

def BitVecConst.bvadd (n : Nat) := BitVecConst.bvaOp n .add
def BitVecConst.bvsub (n : Nat) := BitVecConst.bvaOp n .sub
def BitVecConst.bvmul (n : Nat) := BitVecConst.bvaOp n .mul
def BitVecConst.bvudiv (n : Nat) := BitVecConst.bvaOp n .udiv
def BitVecConst.bvurem (n : Nat) := BitVecConst.bvaOp n .urem
def BitVecConst.bvsdiv (n : Nat) := BitVecConst.bvaOp n .sdiv
def BitVecConst.bvsrem (n : Nat) := BitVecConst.bvaOp n .srem
def BitVecConst.bvsmod (n : Nat) := BitVecConst.bvaOp n .smod
def BitVecConst.bvult (n : Nat) := BitVecConst.bvcmp n .ult
def BitVecConst.bvule (n : Nat) := BitVecConst.bvcmp n .ule
def BitVecConst.bvslt (n : Nat) := BitVecConst.bvcmp n .slt
def BitVecConst.bvsle (n : Nat) := BitVecConst.bvcmp n .sle
def BitVecConst.bvpropult (n : Nat) := BitVecConst.bvpropcmp n .ult
def BitVecConst.bvpropule (n : Nat) := BitVecConst.bvpropcmp n .ule
def BitVecConst.bvpropslt (n : Nat) := BitVecConst.bvpropcmp n .slt
def BitVecConst.bvpropsle (n : Nat) := BitVecConst.bvpropcmp n .sle
def BitVecConst.bvshl (n : Nat) := BitVecConst.bvshOp n .shl
def BitVecConst.bvlshr (n : Nat) := BitVecConst.bvshOp n .lshr
def BitVecConst.bvashr (n : Nat) := BitVecConst.bvshOp n .ashr
def BitVecConst.bvsmtshl (n : Nat) := BitVecConst.bvsmtshOp n .shl
def BitVecConst.bvsmtlshr (n : Nat) := BitVecConst.bvsmtshOp n .lshr
def BitVecConst.bvsmtashr (n : Nat) := BitVecConst.bvsmtshOp n .ashr

mkConstFamily BitVecConst with
  | bvVal (n : Nat) (i : Nat)        | ofBvVal        | (.base (.bv n))                                                                  | ToString.toString (repr (BitVec.ofNat n i)) | GLift.up (BitVec.ofNat n i)
  | bvofNat (n : Nat)                | ofBvofNat      | (.func (.base .nat) (.base (.bv n)))                                             | s!"bvofNat {n}"                    | bvofNatLift n
  | bvtoNat (n : Nat)                | ofBvtoNat      | (.func (.base (.bv n)) (.base .nat))                                             | s!"bvtoNat {n}"                    | bvtoNatLift n
  | bvofInt (n : Nat)                | ofBvofInt      | (.func (.base .int) (.base (.bv n)))                                             | s!"bvofInt {n}"                    | bvofIntLift n
  | bvtoInt (n : Nat)                | ofBvtoInt      | (.func (.base (.bv n)) (.base .int))                                             | s!"bvtoInt {n}"                    | bvtoIntLift n
  | bvmsb (n : Nat)                  | ofBvmsb        | (.func (.base (.bv n)) (.base .bool))                                            | s!"bvmsb {n}"                      | bvmsbLift n
  | bvaOp (n : Nat) (op : BVAOp)     | ofBvaOp        | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))                  | op.toString                        | op.interp n
  | bvneg (n : Nat)                  | ofBvneg        | (.func (.base (.bv n)) (.base (.bv n)))                                          | "-"                                | bvnegLift n
  | bvabs (n : Nat)                  | ofBvabs        | (.func (.base (.bv n)) (.base (.bv n)))                                          | "bvabs"                            | bvabsLift n
  | bvcmp (n : Nat) (op : BVCmp)     | ofBvcmp        | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base .bool)))                    | op.toString false                  | op.interp n
  | bvpropcmp (n : Nat) (op : BVCmp) | ofBvpropcmp    | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base .prop)))                    | op.toString true                   | op.propinterp n
  | bvand (n : Nat)                  | ofBvand        | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))                  | "&&&"                              | bvandLift n
  | bvor (n : Nat)                   | ofBvor         | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))                  | "|||"                              | bvorLift n
  | bvxor (n : Nat)                  | ofBvxor        | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))                  | "^^^"                              | bvxorLift n
  | bvnot (n : Nat)                  | ofBvnot        | (.func (.base (.bv n)) (.base (.bv n)))                                          | "!"                                | bvnotLift n
  | bvshOp (n : Nat) (op : BVShOp)   | ofBvshOp       | (.func (.base (.bv n)) (.func (.base .nat) (.base (.bv n))))                     | op.toString false                  | op.interp n
  | bvsmtshOp (n : Nat) (op : BVShOp)| ofBvsmtshOp    | (.func (.base (.bv n)) (.func (.base (.bv n)) (.base (.bv n))))                  | op.toString true                   | op.smtinterp n
  | bvappend (n : Nat) (m : Nat)     | ofBvappend     | (.func (.base (.bv n)) (.func (.base (.bv m)) (.base (.bv (Nat.add n m)))))      | "++"                               | bvappendLift n m
  | bvextract (n : Nat) (hi : Nat) (lo : Nat) | ofBvextract | (.func (.base (.bv n)) (.base (.bv (Nat.add (Nat.sub hi lo) 1))))           | s!"bvextract {hi} {lo}"            | bvextractLift n hi lo
  | bvrepeat (w : Nat) (i : Nat)     | ofBvrepeat     | (.func (.base (.bv w)) (.base (.bv (Nat.mul w i))))                              | s!"bvrepeat {i}"                   | bvrepeatLift w i
  | bvzeroExtend (w : Nat) (v : Nat) | ofBvzeroExtend | (.func (.base (.bv w)) (.base (.bv v)))                                          | s!"bvzeroExtend {v}"               | bvzeroExtendLift w v
  | bvsignExtend (w : Nat) (v : Nat) | ofBvsignExtend | (.func (.base (.bv w)) (.base (.bv v)))                                          | s!"bvsignExtend {v}"               | bvsignExtendLift w v

def BitVecConst.LamWF.ofBvadd (n : Nat) := LamWF.ofBvaOp n .add
def BitVecConst.LamWF.ofBvsub (n : Nat) := LamWF.ofBvaOp n .sub
def BitVecConst.LamWF.ofBvmul (n : Nat) := LamWF.ofBvaOp n .mul
def BitVecConst.LamWF.ofBvudiv (n : Nat) := LamWF.ofBvaOp n .udiv
def BitVecConst.LamWF.ofBvurem (n : Nat) := LamWF.ofBvaOp n .urem
def BitVecConst.LamWF.ofBvsdiv (n : Nat) := LamWF.ofBvaOp n .sdiv
def BitVecConst.LamWF.ofBvsrem (n : Nat) := LamWF.ofBvaOp n .srem
def BitVecConst.LamWF.ofBvsmod (n : Nat) := LamWF.ofBvaOp n .smod
def BitVecConst.LamWF.ofBvult (n : Nat) := LamWF.ofBvcmp n .ult
def BitVecConst.LamWF.ofBvule (n : Nat) := LamWF.ofBvcmp n .ule
def BitVecConst.LamWF.ofBvslt (n : Nat) := LamWF.ofBvcmp n .slt
def BitVecConst.LamWF.ofBvsle (n : Nat) := LamWF.ofBvcmp n .sle
def BitVecConst.LamWF.ofBvpropult (n : Nat) := LamWF.ofBvpropcmp n .ult
def BitVecConst.LamWF.ofBvpropule (n : Nat) := LamWF.ofBvpropcmp n .ule
def BitVecConst.LamWF.ofBvpropslt (n : Nat) := LamWF.ofBvpropcmp n .slt
def BitVecConst.LamWF.ofBvpropsle (n : Nat) := LamWF.ofBvpropcmp n .sle
def BitVecConst.LamWF.ofBvshl (n : Nat) := LamWF.ofBvshOp n .shl
def BitVecConst.LamWF.ofBvlshr (n : Nat) := LamWF.ofBvshOp n .lshr
def BitVecConst.LamWF.ofBvashr (n : Nat) := LamWF.ofBvshOp n .ashr
def BitVecConst.LamWF.ofBvsmtshl (n : Nat) := LamWF.ofBvsmtshOp n .shl
def BitVecConst.LamWF.ofBvsmtlshr (n : Nat) := LamWF.ofBvsmtshOp n .lshr
def BitVecConst.LamWF.ofBvsmtashr (n : Nat) := LamWF.ofBvsmtshOp n .ashr

end Auto.Embedding.Lam
