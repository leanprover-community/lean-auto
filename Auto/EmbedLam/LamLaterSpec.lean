module

public import Auto.EmbedLam.LamTermInterp

@[expose] public section

/-!
  Characterizations of the constants of later-declared types (see `RealInterpUnlifted.CoreSpec`
    and `RealInterpUnlifted.ExtSpec`) as `λ` terms, which are valid if the characterizations
    are available in the valuation
-/

namespace Auto.Embedding.Lam

def LamTerm.mkRealConst (rc : RealConst) : LamTerm := .base (.lcst (.real rc))

/-- `rc a`, where `a : s` -/
def LamTerm.mkRealUOp (rc : RealConst) (s : LamSort) (a : LamTerm) : LamTerm :=
  .app s (.mkRealConst rc) a

/-- `rc a b`, where `a b : Real` -/
def LamTerm.mkRealBinOp (rc : RealConst) (a b : LamTerm) : LamTerm :=
  .app (.base .real) (.app (.base .real) (.mkRealConst rc) a) b

/-- The characterization `RealInterpUnlifted.CoreSpec` of the core constants, as a conjunction -/
def LamTerm.realCoreSpec : LamTerm :=
  let r : LamSort := .base .real
  let add := LamTerm.mkRealBinOp .add
  let mul := LamTerm.mkRealBinOp .mul
  let le := LamTerm.mkRealBinOp .le
  let neg := LamTerm.mkRealUOp .neg r
  let inv := LamTerm.mkRealUOp .inv r
  let zero := LamTerm.mkRealConst .zero
  let one := LamTerm.mkRealConst .one
  let x := LamTerm.bvar
  -- `∀ x, S x → le x b`, where `S` and `b` are the `bvar`s `S` and `b` outside the `∀`
  let ub (S b : Nat) := LamTerm.mkForallEF r (.mkImp (.app r (x (S + 1)) (x 0)) (le (x 0) (x (b + 1))))
  .mkAnd (.mkForallEF r (.mkForallEF r (.mkForallEF r
    (.mkEq r (add (add (x 2) (x 1)) (x 0)) (add (x 2) (add (x 1) (x 0)))))))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkEq r (add (x 1) (x 0)) (add (x 0) (x 1)))))
  (.mkAnd (.mkForallEF r (.mkEq r (add zero (x 0)) (x 0)))
  (.mkAnd (.mkForallEF r (.mkEq r (add (x 0) (neg (x 0))) zero))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkForallEF r
    (.mkEq r (mul (mul (x 2) (x 1)) (x 0)) (mul (x 2) (mul (x 1) (x 0)))))))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkEq r (mul (x 1) (x 0)) (mul (x 0) (x 1)))))
  (.mkAnd (.mkForallEF r (.mkEq r (mul one (x 0)) (x 0)))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkForallEF r
    (.mkEq r (mul (x 2) (add (x 1) (x 0))) (add (mul (x 2) (x 1)) (mul (x 2) (x 0)))))))
  (.mkAnd (.mkNot (.mkEq r zero one))
  (.mkAnd (.mkForallEF r (.mkImp (.mkNot (.mkEq r (x 0) zero)) (.mkEq r (mul (x 0) (inv (x 0))) one)))
  (.mkAnd (.mkEq r (inv zero) zero)
  (.mkAnd (.mkForallEF r (le (x 0) (x 0)))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkForallEF r
    (.mkImp (le (x 2) (x 1)) (.mkImp (le (x 1) (x 0)) (le (x 2) (x 0)))))))
  (.mkAnd (.mkForallEF r (.mkForallEF r
    (.mkImp (le (x 1) (x 0)) (.mkImp (le (x 0) (x 1)) (.mkEq r (x 1) (x 0))))))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkOr (le (x 1) (x 0)) (le (x 0) (x 1)))))
  (.mkAnd (.mkForallEF r (.mkForallEF r (.mkForallEF r
    (.mkImp (le (x 2) (x 1)) (le (add (x 0) (x 2)) (add (x 0) (x 1)))))))
  (.mkAnd (.mkForallEF r (.mkForallEF r
    (.mkImp (le zero (x 1)) (.mkImp (le zero (x 0)) (le zero (mul (x 1) (x 0)))))))
  (.mkForallEF (.func r (.base .prop))
    (.mkImp (.mkExistEF r (.app r (x 1) (x 0)))
    (.mkImp (.mkExistEF r (ub 1 0))
    (.mkExistEF r (.mkAnd (ub 1 0) (.mkForallEF r (.mkImp (ub 2 0) (le (x 1) (x 0)))))))))))))))))))))))))

theorem LamTerm.maxEVarSucc_realCoreSpec : maxEVarSucc realCoreSpec = 0 := rfl

theorem LamThmValid.realCoreSpec (h : lval.laterVal.real.lower.CoreSpec) :
  LamThmValid lval [] LamTerm.realCoreSpec :=
  LamThmValid.ofInterpAsProp _ _ rfl
    ⟨h.add_assoc, h.add_comm, h.zero_add, h.add_neg_cancel, h.mul_assoc, h.mul_comm, h.one_mul, h.mul_add,
     h.zero_ne_one, h.mul_inv_cancel, h.inv_zero, h.le_refl, h.le_trans, h.le_antisymm, h.le_total,
     h.add_le_add_left, h.mul_nonneg, fun S => h.complete fun x => (S x).down⟩ rfl

/--
  The characterization `RealInterpUnlifted.extProp rc` of a constant `rc` that
    is not a core constant. Core constants are characterized by `realCoreSpec`
-/
def LamTerm.realExtSpec (rc : RealConst) : LamTerm :=
  let r : LamSort := .base .real
  let nat : LamSort := .base .nat
  let int : LamSort := .base .int
  let rat : LamSort := .base .rat
  let add := LamTerm.mkRealBinOp .add
  let mul := LamTerm.mkRealBinOp .mul
  let le := LamTerm.mkRealBinOp .le
  let lt := LamTerm.mkRealBinOp .lt
  let neg := LamTerm.mkRealUOp .neg r
  let ofInt := LamTerm.mkRealUOp .ofInt int
  let ofRat := LamTerm.mkRealUOp .ofRat rat
  let zero := LamTerm.mkRealConst .zero
  let one := LamTerm.mkRealConst .one
  let x := LamTerm.bvar
  match rc with
  | .sub => .mkForallEF r (.mkForallEF r
      (.mkEq r (.mkRealBinOp .sub (x 1) (x 0)) (add (x 1) (neg (x 0)))))
  | .div => .mkForallEF r (.mkForallEF r
      (.mkEq r (.mkRealBinOp .div (x 1) (x 0)) (mul (x 1) (.mkRealUOp .inv r (x 0)))))
  | .ofNat =>
    let ofNat := LamTerm.mkRealUOp .ofNat nat
    .mkAnd (.mkEq r (ofNat (.mkNatVal 0)) zero)
      (.mkForallEF nat (.mkEq r (ofNat (.mkNatBinOp .nadd (x 0) (.mkNatVal 1))) (add (ofNat (x 0)) one)))
  | .ofInt =>
    .mkAnd (.mkEq r (ofInt (.mkIOfNat (.mkNatVal 1))) one)
      (.mkForallEF int (.mkForallEF int
        (.mkEq r (ofInt (.mkIntBinOp .iadd (x 1) (x 0))) (add (ofInt (x 1)) (ofInt (x 0))))))
  | .lt => .mkForallEF r (.mkForallEF r
      (.mkIff (lt (x 1) (x 0)) (.mkAnd (le (x 1) (x 0)) (.mkNot (le (x 0) (x 1))))))
  | .max =>
    let max := LamTerm.mkRealBinOp .max
    .mkAnd (.mkForallEF r (.mkForallEF r (.mkImp (le (x 0) (x 1)) (.mkEq r (max (x 1) (x 0)) (x 1)))))
      (.mkForallEF r (.mkForallEF r (.mkImp (le (x 1) (x 0)) (.mkEq r (max (x 1) (x 0)) (x 0)))))
  | .min =>
    let min := LamTerm.mkRealBinOp .min
    .mkAnd (.mkForallEF r (.mkForallEF r (.mkImp (le (x 1) (x 0)) (.mkEq r (min (x 1) (x 0)) (x 1)))))
      (.mkForallEF r (.mkForallEF r (.mkImp (le (x 0) (x 1)) (.mkEq r (min (x 1) (x 0)) (x 0)))))
  | .abs =>
    let abs := LamTerm.mkRealUOp .abs r
    .mkAnd (.mkForallEF r (.mkImp (le zero (x 0)) (.mkEq r (abs (x 0)) (x 0))))
      (.mkForallEF r (.mkImp (le (x 0) zero) (.mkEq r (abs (x 0)) (neg (x 0)))))
  | .ofScientific =>
    let ofSci := .app nat (.app (.base .bool) (.app nat (.mkRealConst .ofScientific) (x 2)) (x 1)) (x 0)
    let qofSci := .app nat (.app (.base .bool) (.app nat (.base (.qcst .qofScientific)) (x 2)) (x 1)) (x 0)
    .mkForallEF nat (.mkForallEF (.base .bool) (.mkForallEF nat (.mkEq r ofSci (ofRat qofSci))))
  | .floor =>
    let floor := LamTerm.mkRealUOp .floor r
    .mkAnd (.mkForallEF r (le (ofInt (floor (x 0))) (x 0)))
      (.mkForallEF r (lt (x 0) (add (ofInt (floor (x 0))) one)))
  | .ceil =>
    let ceil := LamTerm.mkRealUOp .ceil r
    .mkAnd (.mkForallEF r (le (x 0) (ofInt (ceil (x 0)))))
      (.mkForallEF r (lt (ofInt (ceil (x 0))) (add (x 0) one)))
  | .pow =>
    let pow (a n : LamTerm) := LamTerm.app nat (.app r (.mkRealConst .pow) a) n
    .mkAnd (.mkForallEF r (.mkEq r (pow (x 0) (.mkNatVal 0)) one))
      (.mkForallEF r (.mkForallEF nat
        (.mkEq r (pow (x 1) (.mkNatBinOp .nadd (x 0) (.mkNatVal 1))) (mul (pow (x 1) (x 0)) (x 1)))))
  | .sqrt =>
    let sqrt := LamTerm.mkRealUOp .sqrt r
    .mkAnd (.mkForallEF r (le zero (sqrt (x 0))))
      (.mkAnd (.mkForallEF r (.mkImp (le zero (x 0)) (.mkEq r (mul (sqrt (x 0)) (sqrt (x 0))) (x 0))))
        (.mkForallEF r (.mkImp (le (x 0) zero) (.mkEq r (sqrt (x 0)) zero))))
  | .ofRat =>
    let qbin (qc : RatConst) (a b : LamTerm) := LamTerm.app rat (.app rat (.base (.qcst qc)) a) b
    .mkAnd (.mkEq r (ofRat (.app int (.base (.qcst .qofInt)) (.mkIOfNat (.mkNatVal 1)))) one)
      (.mkAnd (.mkForallEF rat (.mkForallEF rat
          (.mkEq r (ofRat (qbin .qadd (x 1) (x 0))) (add (ofRat (x 1)) (ofRat (x 0))))))
        (.mkForallEF rat (.mkForallEF rat
          (.mkEq r (ofRat (qbin .qmul (x 1) (x 0))) (mul (ofRat (x 1)) (ofRat (x 0)))))))
  | .zero | .one | .add | .neg | .mul | .inv | .le => .base .trueE

theorem LamTerm.maxEVarSucc_realExtSpec (rc : RealConst) : maxEVarSucc (realExtSpec rc) = 0 := by
  cases rc <;> rfl

theorem LamThmValid.realExtSpec :
  (rc : RealConst) → (h : lval.laterVal.real.lower.extProp rc) → LamThmValid lval [] (LamTerm.realExtSpec rc)
| .sub, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .div, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .ofNat, h => LamThmValid.ofInterpAsProp _ _ rfl ⟨h.left, fun n => h.right n.down⟩ rfl
| .ofInt, h => LamThmValid.ofInterpAsProp _ _ rfl ⟨h.left, fun m n => h.right m.down n.down⟩ rfl
| .lt, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .max, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .min, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .abs, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .ofScientific, h => LamThmValid.ofInterpAsProp _ _ rfl (fun m s e => h m.down s.down e.down) rfl
| .floor, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .ceil, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .pow, h => LamThmValid.ofInterpAsProp _ _ rfl ⟨h.left, fun x n => h.right x n.down⟩ rfl
| .sqrt, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .ofRat, h => LamThmValid.ofInterpAsProp _ _ rfl
    ⟨h.left, fun p q => h.right.left p.down q.down, fun p q => h.right.right p.down q.down⟩ rfl
| .zero, _ | .one, _ | .add, _ | .neg, _ | .mul, _ | .inv, _ | .le, _ =>
  LamThmValid.ofInterpAsProp _ _ rfl True.intro rfl

def LamTerm.mkComplexConst (cc : ComplexConst) : LamTerm := .base (.lcst (.complex cc))

/-- `cc a`, where `a : s` -/
def LamTerm.mkComplexUOp (cc : ComplexConst) (s : LamSort) (a : LamTerm) : LamTerm :=
  .app s (.mkComplexConst cc) a

/-- `cc a b`, where `a b : Complex` -/
def LamTerm.mkComplexBinOp (cc : ComplexConst) (a b : LamTerm) : LamTerm :=
  .app (.base .complex) (.app (.base .complex) (.mkComplexConst cc) a) b

/-- The characterization `ComplexInterpUnlifted.CoreSpec` of the core constants, as a conjunction -/
def LamTerm.complexCoreSpec : LamTerm :=
  let r : LamSort := .base .real
  let c : LamSort := .base .complex
  let re := LamTerm.mkComplexUOp .re c
  let im := LamTerm.mkComplexUOp .im c
  let mk (x y : LamTerm) := LamTerm.app r (.app r (.mkComplexConst .mk) x) y
  let x := LamTerm.bvar
  .mkAnd (.mkForallEF r (.mkForallEF r (.mkEq r (re (mk (x 1) (x 0))) (x 1))))
    (.mkAnd (.mkForallEF r (.mkForallEF r (.mkEq r (im (mk (x 1) (x 0))) (x 0))))
      (.mkForallEF c (.mkEq c (mk (re (x 0)) (im (x 0))) (x 0))))

theorem LamTerm.maxEVarSucc_complexCoreSpec : maxEVarSucc complexCoreSpec = 0 := rfl

theorem LamThmValid.complexCoreSpec (h : lval.laterVal.complex.lower.CoreSpec) :
  LamThmValid lval [] LamTerm.complexCoreSpec :=
  LamThmValid.ofInterpAsProp _ _ rfl ⟨h.re_mk, h.im_mk, h.mk_re_im⟩ rfl

/--
  The characterization `ComplexInterpUnlifted.extProp cc` of a constant `cc` that
    is not a core constant. Core constants are characterized by `complexCoreSpec`
-/
def LamTerm.complexExtSpec (cc : ComplexConst) : LamTerm :=
  let r : LamSort := .base .real
  let c : LamSort := .base .complex
  let nat : LamSort := .base .nat
  let re := LamTerm.mkComplexUOp .re c
  let im := LamTerm.mkComplexUOp .im c
  let normSq := LamTerm.mkComplexUOp .normSq c
  let rzero := LamTerm.mkRealConst .zero
  let rone := LamTerm.mkRealConst .one
  let radd := LamTerm.mkRealBinOp .add
  let rsub := LamTerm.mkRealBinOp .sub
  let rmul := LamTerm.mkRealBinOp .mul
  let rneg := LamTerm.mkRealUOp .neg r
  let x := LamTerm.bvar
  -- `re a = reA ∧ im a = imA`
  let parts (a reA imA : LamTerm) := LamTerm.mkAnd (.mkEq r (re a) reA) (.mkEq r (im a) imA)
  -- `(∀ z : s, re a = reA) ∧ ∀ z : s, im a = imA`, where `z` is `bvar 0`
  let parts₁ (s : LamSort) (a reA imA : LamTerm) :=
    LamTerm.mkAnd (.mkForallEF s (.mkEq r (re a) reA)) (.mkForallEF s (.mkEq r (im a) imA))
  -- `(∀ z w, re a = reA) ∧ ∀ z w, im a = imA`, where `z` is `bvar 1` and `w` is `bvar 0`
  let parts₂ (a reA imA : LamTerm) :=
    LamTerm.mkAnd (.mkForallEF c (.mkForallEF c (.mkEq r (re a) reA)))
      (.mkForallEF c (.mkForallEF c (.mkEq r (im a) imA)))
  match cc with
  | .zero => parts (.mkComplexConst .zero) rzero rzero
  | .one => parts (.mkComplexConst .one) rone rzero
  | .I => parts (.mkComplexConst .I) rzero rone
  | .add => parts₂ (.mkComplexBinOp .add (x 1) (x 0)) (radd (re (x 1)) (re (x 0))) (radd (im (x 1)) (im (x 0)))
  | .sub => parts₂ (.mkComplexBinOp .sub (x 1) (x 0)) (rsub (re (x 1)) (re (x 0))) (rsub (im (x 1)) (im (x 0)))
  | .mul => parts₂ (.mkComplexBinOp .mul (x 1) (x 0))
      (rsub (rmul (re (x 1)) (re (x 0))) (rmul (im (x 1)) (im (x 0))))
      (radd (rmul (re (x 1)) (im (x 0))) (rmul (im (x 1)) (re (x 0))))
  | .div => .mkForallEF c (.mkForallEF c (.mkEq c (.mkComplexBinOp .div (x 1) (x 0))
      (.mkComplexBinOp .mul (x 1) (.mkComplexUOp .inv c (x 0)))))
  | .neg => parts₁ c (.mkComplexUOp .neg c (x 0)) (rneg (re (x 0))) (rneg (im (x 0)))
  | .inv =>
    let rdiv := LamTerm.mkRealBinOp .div
    parts₁ c (.mkComplexUOp .inv c (x 0)) (rdiv (re (x 0)) (normSq (x 0))) (rdiv (rneg (im (x 0))) (normSq (x 0)))
  | .ofNat => parts₁ nat (.mkComplexUOp .ofNat nat (x 0)) (.mkRealUOp .ofNat nat (x 0)) rzero
  | .ofInt =>
    let int : LamSort := .base .int
    parts₁ int (.mkComplexUOp .ofInt int (x 0)) (.mkRealUOp .ofInt int (x 0)) rzero
  | .ofReal => parts₁ r (.mkComplexUOp .ofReal r (x 0)) (x 0) rzero
  | .normSq => .mkForallEF c (.mkEq r (normSq (x 0)) (radd (rmul (re (x 0)) (re (x 0))) (rmul (im (x 0)) (im (x 0)))))
  | .conj => parts₁ c (.mkComplexUOp .conj c (x 0)) (re (x 0)) (rneg (im (x 0)))
  | .norm => .mkForallEF c (.mkEq r (.mkComplexUOp .norm c (x 0)) (.mkRealUOp .sqrt r (normSq (x 0))))
  | .pow =>
    let pow (a n : LamTerm) := LamTerm.app nat (.app c (.mkComplexConst .pow) a) n
    .mkAnd (.mkForallEF c (.mkEq c (pow (x 0) (.mkNatVal 0)) (.mkComplexConst .one)))
      (.mkForallEF c (.mkForallEF nat
        (.mkEq c (pow (x 1) (.mkNatBinOp .nadd (x 0) (.mkNatVal 1))) (.mkComplexBinOp .mul (pow (x 1) (x 0)) (x 1)))))
  | .ofRat =>
    let rat : LamSort := .base .rat
    parts₁ rat (.mkComplexUOp .ofRat rat (x 0)) (.mkRealUOp .ofRat rat (x 0)) rzero
  | .re | .im | .mk => .base .trueE

theorem LamTerm.maxEVarSucc_complexExtSpec (cc : ComplexConst) : maxEVarSucc (complexExtSpec cc) = 0 := by
  cases cc <;> rfl

theorem LamThmValid.complexExtSpec :
  (cc : ComplexConst) → (h : ComplexInterpUnlifted.extProp lval.laterVal.real.lower lval.laterVal.complex.lower cc) →
    LamThmValid lval [] (LamTerm.complexExtSpec cc)
| .zero, h | .one, h | .I, h | .add, h | .sub, h | .mul, h | .div, h | .neg, h | .inv, h
| .ofReal, h | .normSq, h | .conj, h | .norm, h => LamThmValid.ofInterpAsProp _ _ rfl h rfl
| .ofNat, h | .ofInt, h | .ofRat, h =>
  LamThmValid.ofInterpAsProp _ _ rfl ⟨fun n => h.left n.down, fun n => h.right n.down⟩ rfl
| .pow, h => LamThmValid.ofInterpAsProp _ _ rfl ⟨h.left, fun z n => h.right z n.down⟩ rfl
| .re, _ | .im, _ | .mk, _ => LamThmValid.ofInterpAsProp _ _ rfl True.intro rfl

end Auto.Embedding.Lam
