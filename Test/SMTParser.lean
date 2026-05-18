import Lean
import Auto.Parser.LexInit
import Auto.Parser.SMTSexp

/-
  Sanity checks for SMT parser
-/

namespace Auto
namespace Parser.SMTTerm
open Lexer
open Lean
open Meta

def testTerms : Array String := #[
  "(=> (not (<= _x _z)) (>= (+ _x (* (- 1) _z)) 1))",
  "(forall ((B0 Bool) (B1 Bool)) (= (or B0 false B1) (or B0 B1)))",
  "(let ((_let_1 (* (- 1) _z))) (or (>= (+ _x (* (- 1) _y)) 1) (>= (+ _y _let_1) 1) (not (>= (+ _x _let_1) 1))))",
  "(let ((_let_1 (* _c _d _f))) (let ((_let_2 (* _a _b _f))) (or (= _let_2 _let_1) (not (= _let_2 0)) (>= _f 1) (not (>= _f 0)) (not (= _let_1 0)))))",
  "(let ((_let_1 (_Prod.snd (_Prod.snd_0 _x)))) (let ((_let_2 (_Prod.fst_0 _x))) (=> (not (<= _let_2 _let_1)) (>= (+ _let_2 (* (- 1) _let_1)) 1))))",
  "(let ((_let_1 (_Prod.snd_0 _x))) (let ((_let_2 (* (- 1) (_Prod.snd _let_1)))) (let ((_let_3 (_Prod.fst_0 _x))) (let ((_let_4 (_Prod.fst _let_1))) (or (>= (+ _let_3 (* (- 1) _let_4)) 1) (>= (+ _let_4 _let_2) 1) (not (>= (+ _let_3 _let_2) 1)))))))",
  "(=> (forall ((_i_0 Int)) (forall ((_i_1 Int)) (_P (_Prod.mk _i_0 _i_1)))) (forall ((_i_0 Int) (_i_1 Int)) (_P (_Prod.mk _i_0 _i_1))))",
  "(=> (not (exists ((_m_0 _myStructure)) (< (_sum _x) (_sum _m_0)))) (forall ((_m_0 _myStructure)) (>= (+ (_sum _x) (* (- 1) (_sum _m_0))) 0)))",
  "(=> (and (= _wfNat (lambda ((_n Int)) (>= _n 0))) (forall ((_m _myStructure)) (= (_wf_myStructure _m) (=> ((_ is _mk) _m) (_wfNat (_field2_ _m)))))) (forall ((_m _myStructure)) (= (_wf_myStructure _m) (>= (_field2_ _m) 0))))"
]

def testMaps : Array (Std.HashMap String Expr) := #[
  Std.HashMap.ofArray #[("_x", Expr.lit (.natVal 1)), ("_y", Expr.lit (.natVal 2)), ("_z", Expr.lit (.natVal 3))],
  {},
  Std.HashMap.ofArray #[("_x", Expr.lit (.natVal 1)), ("_y", Expr.lit (.natVal 2)), ("_z", Expr.lit (.natVal 3))],
  Std.HashMap.ofArray #[
    ("_a", Expr.lit (.natVal 1)), ("_b", Expr.lit (.natVal 2)), ("_c", Expr.lit (.natVal 3)),
    ("_d", Expr.lit (.natVal 1)), ("_e", Expr.lit (.natVal 2)), ("_f", Expr.lit (.natVal 3))
  ],
  Std.HashMap.ofArray #[("_Prod.snd", Expr.lit (.natVal 1)), ("_Prod.snd_0", Expr.lit (.natVal 1)), ("_Prod.fst_0", Expr.lit (.natVal 1))],
  Std.HashMap.ofArray #[("_Prod.snd", Expr.lit (.natVal 1)), ("_Prod.snd_0", Expr.lit (.natVal 1)), ("_Prod.fst", Expr.lit (.natVal 1)), ("_Prod.fst_0", Expr.lit (.natVal 1))],
  -- Std.HashMap.ofArray #[("_P", Lean.mkConst ``sorryAx [.zero]), ("_Prod.mk", Expr.const ``Prod.mk [.zero, .zero])]
  -- TODO
]

def test : MetaM Unit := do
  for (s, mp) in testTerms.zip testMaps do
    let .complete t _ ← lexTerm s ⟨0⟩ {}
      | throwError ""
    let e ← parseTermAndAbstractSelectors t mp #[]
    trace[Compiler] "{e}"

set_option trace.Compiler true
#eval test
