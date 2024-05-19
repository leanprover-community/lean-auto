import Lean
import Auto.Embedding.LamBase
import Auto.Translation.LamCstrD
open Lean

namespace Auto.Lam2D

open Embedding Lam LamCstrD

def interpPropConstAsUnlifted : PropConst → CoreM Expr
| .trueE      => return .const ``True []
| .falseE     => return .const ``False []
| .not        => return .const ``Not []
| .and        => return .const ``And []
| .or         => return .const ``Or []
| .imp        => do
  let .some (.defnInfo impVal) := (← getEnv).find? ``ImpF
    | throwError "interpLamBaseTermAsUnlifted :: Unexpected error"
  return impVal.value.instantiateLevelParams impVal.levelParams [.zero, .zero]
| .iff        => return .const ``Iff []

def interpBoolConstAsUnlifted : BoolConst → Expr
| .ofProp => .const ``Bool.ofProp []
| .trueb  => .const ``true []
| .falseb => .const ``false []
| .notb   => .const ``not []
| .andb   => .const ``and []
| .orb    => .const ``or []

def interpNatConstAsUnlifted : NatConst → Expr
| .natVal n => Lean.toExpr n
| .nadd     => .const ``Nat.add []
| .nsub     => .const ``Nat.sub []
| .nmul     => .const ``Nat.mul []
| .ndiv     => .const ``Nat.div []
| .nmod     => .const ``Nat.mod []
| .nle      => .const ``Nat.le []
| .nlt      => .const ``Nat.lt []
| .nmax     => .const ``Nat.max []
| .nmin     => .const ``Nat.min []

def interpIntConstAsUnlifted : IntConst → Expr
| .iofNat   => .const ``Int.ofNat []
| .inegSucc => .const ``Int.negSucc []
| .ineg     => .const ``Int.neg []
| .iabs     => .const ``Int.abs []
| .iadd     => .const ``Int.add []
| .isub     => .const ``Int.sub []
| .imul     => .const ``Int.mul []
| .idiv     => .const ``Int.div []
| .imod     => .const ``Int.mod []
| .iediv    => .const ``Int.ediv []
| .iemod    => .const ``Int.emod []
| .ile      => .const ``Int.le []
| .ilt      => .const ``Int.lt []
| .imax     => .const ``Int.max []
| .imin     => .const ``Int.min []

def interpStringConstAsUnlifted : StringConst → Expr
| .strVal s  => Lean.toExpr s
| .slength   => .const ``String.length []
| .sapp      => .const ``String.append []
| .sle       => .const ``String.le []
| .slt       => .const ``String.lt []
| .sprefixof => .const ``String.isPrefixOf []
| .srepall   => .const ``String.replace []

def interpBitVecConstAsUnlifted : BitVecConst → Expr
| .bvVal n i         => mkApp2 (.const ``BitVec.ofNat []) (.lit (.natVal n)) (.lit (.natVal i))
| .bvofNat n         => .app (.const ``BitVec.ofNat []) (.lit (.natVal n))
| .bvtoNat n         => .app (.const ``BitVec.toNat []) (.lit (.natVal n))
| .bvofInt n         => .app (.const ``BitVec.ofInt []) (.lit (.natVal n))
| .bvtoInt n         => .app (.const ``BitVec.toInt []) (.lit (.natVal n))
| .bvmsb n           => .app (.const ``BitVec.msb []) (.lit (.natVal n))
| .bvaOp n op =>
  match op with
  | .add             => .app (.const ``BitVec.add []) (.lit (.natVal n))
  | .sub             => .app (.const ``BitVec.sub []) (.lit (.natVal n))
  | .mul             => .app (.const ``BitVec.mul []) (.lit (.natVal n))
  | .udiv            => .app (.const ``BitVec.smtUDiv []) (.lit (.natVal n))
  | .urem            => .app (.const ``BitVec.umod []) (.lit (.natVal n))
  | .sdiv            => .app (.const ``BitVec.smtSDiv []) (.lit (.natVal n))
  | .srem            => .app (.const ``BitVec.srem []) (.lit (.natVal n))
  | .smod            => .app (.const ``BitVec.smod []) (.lit (.natVal n))
| .bvneg n           => .app (.const ``BitVec.neg []) (.lit (.natVal n))
| .bvabs n           => .app (.const ``BitVec.abs []) (.lit (.natVal n))
| .bvcmp n prop? op  =>
  match prop? with
  | false =>
    match op with
    | .ult           => .app (.const ``BitVec.ult []) (.lit (.natVal n))
    | .ule           => .app (.const ``BitVec.ule []) (.lit (.natVal n))
    | .slt           => .app (.const ``BitVec.slt []) (.lit (.natVal n))
    | .sle           => .app (.const ``BitVec.sle []) (.lit (.natVal n))
  | true =>
    match op with
    | .ult           => .app (.const ``BitVec.propult []) (.lit (.natVal n))
    | .ule           => .app (.const ``BitVec.propule []) (.lit (.natVal n))
    | .slt           => .app (.const ``BitVec.propslt []) (.lit (.natVal n))
    | .sle           => .app (.const ``BitVec.propsle []) (.lit (.natVal n))
| .bvand n           => .app (.const ``BitVec.and []) (.lit (.natVal n))
| .bvor n            => .app (.const ``BitVec.or []) (.lit (.natVal n))
| .bvxor n           => .app (.const ``BitVec.xor []) (.lit (.natVal n))
| .bvnot n           => .app (.const ``BitVec.not []) (.lit (.natVal n))
| .bvshOp n smt? op  =>
  match smt? with
  | false =>
    match op with
    | .shl           => .app (.const ``BitVec.shiftLeft []) (.lit (.natVal n))
    | .lshr          => .app (.const ``BitVec.ushiftRight []) (.lit (.natVal n))
    | .ashr          => .app (.const ``BitVec.sshiftRight []) (.lit (.natVal n))
  | true =>
    match op with
    | .shl           => mkApp2 (.const ``BitVec.smtHshiftLeft []) (.lit (.natVal n)) (.lit (.natVal n))
    | .lshr          => mkApp2 (.const ``BitVec.smtHushiftRight []) (.lit (.natVal n)) (.lit (.natVal n))
    | .ashr          => mkApp2 (.const ``BitVec.smtHsshiftRight []) (.lit (.natVal n)) (.lit (.natVal n))
| .bvappend n m      => mkApp2 (.const ``BitVec.append []) (.lit (.natVal n)) (.lit (.natVal m))
| .bvextract n h l   => mkApp3 (.const ``BitVec.extractLsb []) (.lit (.natVal n)) (.lit (.natVal h)) (.lit (.natVal l))
| .bvrepeat w i      => mkApp2 (.const ``BitVec.replicate []) (.lit (.natVal w)) (.lit (.natVal i))
| .bvzeroExtend w v  => mkApp2 (.const ``BitVec.zeroExtend []) (.lit (.natVal w)) (.lit (.natVal v))
| .bvsignExtend w v  => mkApp2 (.const ``BitVec.signExtend []) (.lit (.natVal w)) (.lit (.natVal v))
