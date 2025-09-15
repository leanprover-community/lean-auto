import Lean
import Auto.Lib.MetaState
import Auto.Embedding.LamBase
open Lean

namespace Auto

namespace LamCstrD

  abbrev Nat.modEq (n a b : Nat) := a % n = b % n
  abbrev Nat.ge (x y : Nat) := Nat.le y x
  abbrev Nat.gt (x y : Nat) := Nat.lt y x
  abbrev Nat.max (x y : Nat) : Nat := Max.max x y
  abbrev Nat.min (x y : Nat) : Nat := Min.min x y
  abbrev Int.modEq (n a b : Int) := a % n = b % n
  abbrev Int.ge (a b : Int) := Int.le b a
  abbrev Int.gt (a b : Int) := Int.lt b a
  abbrev Int.max (x y : Int) : Int := Max.max x y
  abbrev Int.min (x y : Int) : Int := Min.min x y
  abbrev String.ge (a b : String) : Prop := b = a ∨ b < a
  abbrev String.gt (a b : String) : Prop := b < a
  abbrev BitVec.uge (a b : BitVec n) : Bool := BitVec.ule b a
  abbrev BitVec.ugt (a b : BitVec n) : Bool := BitVec.ult b a
  abbrev BitVec.sge (a b : BitVec n) : Bool := BitVec.sle b a
  abbrev BitVec.sgt (a b : BitVec n) : Bool := BitVec.slt b a
  abbrev BitVec.propule (a b : BitVec n) : Prop := a.toFin <= b.toFin
  abbrev BitVec.propult (a b : BitVec n) : Prop := a.toFin < b.toFin
  abbrev BitVec.propsle (a b : BitVec n) : Prop := a.toInt <= b.toInt
  abbrev BitVec.propslt (a b : BitVec n) : Prop := a.toInt < b.toInt
  abbrev BitVec.propuge (a b : BitVec n) : Prop := BitVec.propule b a
  abbrev BitVec.propugt (a b : BitVec n) : Prop := BitVec.propult b a
  abbrev BitVec.propsge (a b : BitVec n) : Prop := BitVec.propsle b a
  abbrev BitVec.propsgt (a b : BitVec n) : Prop := BitVec.propslt b a
  abbrev BitVec.smtHshiftLeft (a : BitVec n) (b : BitVec m) := BitVec.shiftLeft a b.toNat
  abbrev BitVec.smtHushiftRight (a : BitVec n) (b : BitVec m) := BitVec.ushiftRight a b.toNat
  abbrev BitVec.smtHsshiftRight (a : BitVec n) (b : BitVec m) := BitVec.sshiftRight a b.toNat

end LamCstrD


namespace LamExportUtils

  open Embedding.Lam

  -- This section should only be used when exporting terms to external provers

  def exportError.ImpPolyLog :=
    "Import versions of polymorphic logical " ++
    "constants should have been eliminated"

  def collectLamSortAtoms : LamSort → Std.HashSet Nat
  | .atom n => Std.HashSet.emptyWithCapacity.insert n
  | .base _ => Std.HashSet.emptyWithCapacity
  | .func a b => (collectLamSortAtoms a).insertMany (collectLamSortAtoms b)

  def collectLamSortsAtoms (ss : Array LamSort) : Std.HashSet Nat :=
    ss.foldl (fun hs s => hs.insertMany (collectLamSortAtoms s)) Std.HashSet.emptyWithCapacity

  def collectLamSortBitVecLengths : LamSort → Std.HashSet Nat
  | .base (.bv n) => Std.HashSet.emptyWithCapacity.insert n
  | .func a b => (collectLamSortBitVecLengths a).insertMany (collectLamSortBitVecLengths b)
  | _ => Std.HashSet.emptyWithCapacity

  def collectLamSortsBitVecLengths (ss : Array LamSort) : Std.HashSet Nat :=
    ss.foldl (fun hs s => hs.insertMany (collectLamSortBitVecLengths s)) Std.HashSet.emptyWithCapacity

  /-- Collect type atoms in a LamBaseTerm -/
  def collectLamBaseTermAtoms (b : LamBaseTerm) : CoreM (Std.HashSet Nat) := do
    let s? : Option LamSort ← (do
      match b with
      | .eqI _ => throwError (decl_name% ++ " :: " ++ exportError.ImpPolyLog)
      | .forallEI _ => throwError (decl_name% ++ " :: " ++ exportError.ImpPolyLog)
      | .existEI _ => throwError (decl_name% ++ " :: " ++ exportError.ImpPolyLog)
      | .iteI _ => throwError (decl_name% ++ " :: " ++ exportError.ImpPolyLog)
      | .eq s => return .some s
      | .forallE s => return .some s
      | .existE s => return .some s
      | .ite s => return .some s
      | _ => return none)
    if let .some s := s? then
      return collectLamSortAtoms s
    else
      return Std.HashSet.emptyWithCapacity

  /--
    The first hashset is the type atoms
    The second hashset is the term atoms
    The third hashset is the term etoms
    This function is called when we're trying to export terms
      from `λ` to external provers, e.g. Lean/Duper
    Therefore, we expect that `eqI, forallEI, existEI` and ``ite'`
      does not occur in the `LamTerm`
  -/
  def collectLamTermAtoms (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort) :
    LamTerm → CoreM (Std.HashSet Nat × Std.HashSet Nat × Std.HashSet Nat)
  | .atom n => do
    let .some s := lamVarTy[n]?
      | throwError "{decl_name%} :: Unknown term atom {n}"
    return (collectLamSortAtoms s, Std.HashSet.emptyWithCapacity.insert n, Std.HashSet.emptyWithCapacity)
  | .etom n => do
    let .some s := lamEVarTy[n]?
      | throwError "{decl_name%} :: Unknown etom {n}"
    return (collectLamSortAtoms s, Std.HashSet.emptyWithCapacity, Std.HashSet.emptyWithCapacity.insert n)
  | .base b => do
    return (← collectLamBaseTermAtoms b, Std.HashSet.emptyWithCapacity, Std.HashSet.emptyWithCapacity)
  | .bvar _ => pure (Std.HashSet.emptyWithCapacity, Std.HashSet.emptyWithCapacity, Std.HashSet.emptyWithCapacity)
  | .lam s t => do
    let (typeHs, termHs, etomHs) ← collectLamTermAtoms lamVarTy lamEVarTy t
    let sHs := collectLamSortAtoms s
    return (mergeHashSet typeHs sHs, termHs, etomHs)
  | .app _ t₁ t₂ => do
    let (typeHs₁, termHs₁, etomHs₁) ← collectLamTermAtoms lamVarTy lamEVarTy t₁
    let (typeHs₂, termHs₂, etomHs₂) ← collectLamTermAtoms lamVarTy lamEVarTy t₂
    return (mergeHashSet typeHs₁ typeHs₂,
            mergeHashSet termHs₁ termHs₂,
            mergeHashSet etomHs₁ etomHs₂)

  def collectLamTermsAtoms (lamVarTy : Array LamSort) (lamEVarTy : Array LamSort)
    (ts : Array LamTerm) : CoreM (Std.HashSet Nat × Std.HashSet Nat × Std.HashSet Nat) :=
    ts.foldlM (fun (tyHs, aHs, eHs) t => do
      let (tyHs', aHs', eHs') ← collectLamTermAtoms lamVarTy lamEVarTy t
      return (mergeHashSet tyHs tyHs', mergeHashSet aHs aHs', mergeHashSet eHs eHs'))
      (Std.HashSet.emptyWithCapacity, Std.HashSet.emptyWithCapacity, Std.HashSet.emptyWithCapacity)

  def collectLamTermNatConsts : LamTerm → Std.HashSet NatConst
  | .base (.ncst nc) => Std.HashSet.emptyWithCapacity.insert nc
  | .lam _ body => collectLamTermNatConsts body
  | .app _ fn arg => mergeHashSet (collectLamTermNatConsts fn) (collectLamTermNatConsts arg)
  | _ => Std.HashSet.emptyWithCapacity

  def collectLamTermsNatConsts (ts : Array LamTerm) : Std.HashSet NatConst :=
    ts.foldl (fun hs t => mergeHashSet hs (collectLamTermNatConsts t)) Std.HashSet.emptyWithCapacity

  def collectLamTermIntConsts : LamTerm → Std.HashSet IntConst
  | .base (.icst ic) => Std.HashSet.emptyWithCapacity.insert ic
  | .lam _ body => collectLamTermIntConsts body
  | .app _ fn arg => mergeHashSet (collectLamTermIntConsts fn) (collectLamTermIntConsts arg)
  | _ => Std.HashSet.emptyWithCapacity

  def collectLamTermsIntConsts (ts : Array LamTerm) : Std.HashSet IntConst :=
    ts.foldl (fun hs t => mergeHashSet hs (collectLamTermIntConsts t)) Std.HashSet.emptyWithCapacity

  def collectLamTermStringConsts : LamTerm → Std.HashSet StringConst
  | .base (.scst sc) => Std.HashSet.emptyWithCapacity.insert sc
  | .lam _ body => collectLamTermStringConsts body
  | .app _ fn arg => mergeHashSet (collectLamTermStringConsts fn) (collectLamTermStringConsts arg)
  | _ => Std.HashSet.emptyWithCapacity

  def collectLamTermsStringConsts (ts : Array LamTerm) : Std.HashSet StringConst :=
    ts.foldl (fun hs t => mergeHashSet hs (collectLamTermStringConsts t)) Std.HashSet.emptyWithCapacity

  def collectLamTermBitvecs : LamTerm → Std.HashSet BitVecConst
  | .base (.bvcst bvc) => Std.HashSet.emptyWithCapacity.insert bvc
  | .lam _ body => collectLamTermBitvecs body
  | .app _ fn arg => mergeHashSet (collectLamTermBitvecs fn) (collectLamTermBitvecs arg)
  | _ => Std.HashSet.emptyWithCapacity

  def collectLamTermsBitvecs (ts : Array LamTerm) : Std.HashSet BitVecConst :=
    ts.foldl (fun hs t => mergeHashSet hs (collectLamTermBitvecs t)) Std.HashSet.emptyWithCapacity

  def collectLamTermIteSorts : LamTerm → Std.HashSet LamSort
  | .base (.ite s) => Std.HashSet.emptyWithCapacity.insert s
  | .lam _ body => collectLamTermIteSorts body
  | .app _ fn arg => mergeHashSet (collectLamTermIteSorts fn) (collectLamTermIteSorts arg)
  | _ => Std.HashSet.emptyWithCapacity

  def collectLamTermsIteSorts (ts : Array LamTerm) : Std.HashSet LamSort :=
    ts.foldl (fun hs t => mergeHashSet hs (collectLamTermIteSorts t)) Std.HashSet.emptyWithCapacity

end LamExportUtils


namespace Lam2D

  open Embedding Lam LamCstrD

  def interpLamBaseSortAsUnlifted : LamBaseSort → Expr
  | .prop    => .sort .zero
  | .bool    => .const ``Bool []
  | .nat     => .const ``Nat []
  | .int     => .const ``Int []
  | .isto0 p =>
    match p with
    | .xH => .const ``String []
    | .xO .xH => .const ``Empty []
    | _   => .const ``Empty []
  | .bv n    => .app (.const ``BitVec []) (.lit (.natVal n))

  def interpPropConstAsUnlifted : PropConst → CoreM Expr
  | .trueE      => return .const ``True []
  | .falseE     => return .const ``False []
  | .not        => return .const ``Not []
  | .and        => return .const ``And []
  | .or         => return .const ``Or []
  | .imp        => do
    let .some (.defnInfo impVal) := (← getEnv).find? ``ImpF
      | throwError "{decl_name%} :: Unexpected error"
    return impVal.value.instantiateLevelParams impVal.levelParams [.zero, .zero]
  | .iff        => return .const ``Iff []

  def interpBoolConstAsUnlifted : BoolConst → CoreM Expr
  | .ofProp => return .const ``Bool.ofProp []
  | .trueb  => return .const ``true []
  | .falseb => return .const ``false []
  | .notb   => return .const ``not []
  | .andb   => return .const ``and []
  | .orb    => return .const ``or []

  def interpNatConstAsUnlifted : NatConst → CoreM Expr
  | .natVal n => return .lit (.natVal n)
  | .nadd     => return .const ``Nat.add []
  | .nsub     => return .const ``Nat.sub []
  | .nmul     => return .const ``Nat.mul []
  | .ndiv     => return .const ``Nat.div []
  | .nmod     => return .const ``Nat.mod []
  | .nle      => return .const ``Nat.le []
  | .nlt      => return .const ``Nat.lt []
  | .nmax     => return .const ``Nat.max []
  | .nmin     => return .const ``Nat.min []

  def interpIntConstAsUnlifted : IntConst → CoreM Expr
  | .iofNat   => return .const ``Int.ofNat []
  | .inegSucc => return .const ``Int.negSucc []
  | .ineg     => return .const ``Int.neg []
  | .iabs     => return .const ``Int.abs []
  | .iadd     => return .const ``Int.add []
  | .isub     => return .const ``Int.sub []
  | .imul     => return .const ``Int.mul []
  | .idiv     => return .const ``Int.tdiv []
  | .imod     => return .const ``Int.tmod []
  | .iediv    => return .const ``Int.ediv []
  | .iemod    => return .const ``Int.emod []
  | .ile      => return .const ``Int.le []
  | .ilt      => return .const ``Int.lt []
  | .imax     => return .const ``Int.max []
  | .imin     => return .const ``Int.min []

  def interpStringConstAsUnlifted : StringConst → CoreM Expr
  | .strVal s  => return .lit (.strVal s)
  | .slength   => return .const ``String.length []
  | .sapp      => return .const ``String.append []
  | .sle       => return .const ``String.le []
  | .slt       => return .const ``String.lt []
  | .sprefixof => return .const ``String.isPrefixOf []
  | .srepall   => return .const ``String.replace []

  def interpBitVecConstAsUnlifted : BitVecConst → CoreM Expr
  | .bvVal n i         => return mkApp2 (.const ``BitVec.ofNat []) (.lit (.natVal n)) (.lit (.natVal i))
  | .bvofNat n         => return .app (.const ``BitVec.ofNat []) (.lit (.natVal n))
  | .bvtoNat n         => return .app (.const ``BitVec.toNat []) (.lit (.natVal n))
  | .bvofInt n         => return .app (.const ``BitVec.ofInt []) (.lit (.natVal n))
  | .bvtoInt n         => return .app (.const ``BitVec.toInt []) (.lit (.natVal n))
  | .bvmsb n           => return .app (.const ``BitVec.msb []) (.lit (.natVal n))
  | .bvaOp n op =>
    match op with
    | .add             => return .app (.const ``BitVec.add []) (.lit (.natVal n))
    | .sub             => return .app (.const ``BitVec.sub []) (.lit (.natVal n))
    | .mul             => return .app (.const ``BitVec.mul []) (.lit (.natVal n))
    | .udiv            => return .app (.const ``BitVec.smtUDiv []) (.lit (.natVal n))
    | .urem            => return .app (.const ``BitVec.umod []) (.lit (.natVal n))
    | .sdiv            => return .app (.const ``BitVec.smtSDiv []) (.lit (.natVal n))
    | .srem            => return .app (.const ``BitVec.srem []) (.lit (.natVal n))
    | .smod            => return .app (.const ``BitVec.smod []) (.lit (.natVal n))
  | .bvneg n           => return .app (.const ``BitVec.neg []) (.lit (.natVal n))
  | .bvabs n           => return .app (.const ``BitVec.abs []) (.lit (.natVal n))
  | .bvcmp n prop? op  =>
    match prop? with
    | false =>
      match op with
      | .ult           => return .app (.const ``BitVec.ult []) (.lit (.natVal n))
      | .ule           => return .app (.const ``BitVec.ule []) (.lit (.natVal n))
      | .slt           => return .app (.const ``BitVec.slt []) (.lit (.natVal n))
      | .sle           => return .app (.const ``BitVec.sle []) (.lit (.natVal n))
    | true =>
      match op with
      | .ult           => return .app (.const ``BitVec.propult []) (.lit (.natVal n))
      | .ule           => return .app (.const ``BitVec.propule []) (.lit (.natVal n))
      | .slt           => return .app (.const ``BitVec.propslt []) (.lit (.natVal n))
      | .sle           => return .app (.const ``BitVec.propsle []) (.lit (.natVal n))
  | .bvand n           => return .app (.const ``BitVec.and []) (.lit (.natVal n))
  | .bvor n            => return .app (.const ``BitVec.or []) (.lit (.natVal n))
  | .bvxor n           => return .app (.const ``BitVec.xor []) (.lit (.natVal n))
  | .bvnot n           => return .app (.const ``BitVec.not []) (.lit (.natVal n))
  | .bvshOp n smt? op  =>
    match smt? with
    | false =>
      match op with
      | .shl           => return .app (.const ``BitVec.shiftLeft []) (.lit (.natVal n))
      | .lshr          => return .app (.const ``BitVec.ushiftRight []) (.lit (.natVal n))
      | .ashr          => return .app (.const ``BitVec.sshiftRight []) (.lit (.natVal n))
    | true =>
      match op with
      | .shl           => return mkApp2 (.const ``BitVec.smtHshiftLeft []) (.lit (.natVal n)) (.lit (.natVal n))
      | .lshr          => return mkApp2 (.const ``BitVec.smtHushiftRight []) (.lit (.natVal n)) (.lit (.natVal n))
      | .ashr          => return mkApp2 (.const ``BitVec.smtHsshiftRight []) (.lit (.natVal n)) (.lit (.natVal n))
  | .bvappend n m      => return mkApp2 (.const ``BitVec.append []) (.lit (.natVal n)) (.lit (.natVal m))
  | .bvextract n h l   => return mkApp3 (.const ``BitVec.extractLsb []) (.lit (.natVal n)) (.lit (.natVal h)) (.lit (.natVal l))
  | .bvrepeat w i      => return mkApp2 (.const ``BitVec.replicate []) (.lit (.natVal w)) (.lit (.natVal i))
  | .bvzeroExtend w v  => return mkApp2 (.const ``BitVec.zeroExtend []) (.lit (.natVal w)) (.lit (.natVal v))
  | .bvsignExtend w v  => return mkApp2 (.const ``BitVec.signExtend []) (.lit (.natVal w)) (.lit (.natVal v))

  /--
    Takes a `s : LamSort` and produces the `un-lifted` version of `s.interp`
      (note that `s.interp` is lifted)
  -/
  def interpLamSortAsUnlifted (tyVal : Std.HashMap Nat Expr) : LamSort → CoreM Expr
  | .atom n => do
    let .some e := tyVal.get? n
      | throwError "{decl_name%} :: Cannot find fvarId assigned to type atom {n}"
    return e
  | .base b => return Lam2D.interpLamBaseSortAsUnlifted b
  | .func s₁ s₂ => do
    return .forallE `_ (← interpLamSortAsUnlifted tyVal s₁) (← interpLamSortAsUnlifted tyVal s₂) .default

  def interpOtherConstAsUnlifted (tyVal : Std.HashMap Nat Expr) (oc : OtherConst) : MetaM Expr := do
    let .some (.defnInfo constIdVal) := (← getEnv).find? ``constId
      | throwError "{decl_name%} :: Unexpected error"
    let constIdExpr := fun params => constIdVal.value.instantiateLevelParams constIdVal.levelParams params
    match oc with
    | .smtAttr1T _ sattr sterm => do
      let tyattr ← interpLamSortAsUnlifted tyVal sattr
      let sortattr ← Expr.normalizeType (← Meta.inferType tyattr)
      let Expr.sort lvlattr := sortattr
        | throwError "{decl_name%} :: Unexpected sort {sortattr}"
      let tyterm ← interpLamSortAsUnlifted tyVal sterm
      let sortterm ← Expr.normalizeType (← Meta.inferType tyterm)
      let Expr.sort lvlterm := sortterm
        | throwError "{decl_name%} :: Unexpected sort {sortterm}"
      return Lean.mkApp2 (constIdExpr [lvlattr, lvlterm]) tyattr tyterm

  def interpLamBaseTermAsUnlifted (tyVal : Std.HashMap Nat Expr) : LamBaseTerm → MetaM Expr
  | .pcst pc    => Lam2D.interpPropConstAsUnlifted pc
  | .bcst bc    => Lam2D.interpBoolConstAsUnlifted bc
  | .ncst nc    => Lam2D.interpNatConstAsUnlifted nc
  | .icst ic    => Lam2D.interpIntConstAsUnlifted ic
  | .scst sc    => Lam2D.interpStringConstAsUnlifted sc
  | .bvcst bvc  => Lam2D.interpBitVecConstAsUnlifted bvc
  | .ocst oc    => interpOtherConstAsUnlifted tyVal oc
  | .eqI _      => throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
  | .forallEI _ => throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
  | .existEI _  => throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
  | .iteI _     => throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
  | .eq s       => do
    return ←  Meta.mkAppOptM ``Eq #[← interpLamSortAsUnlifted tyVal s]
  | .forallE s  => do
    let ty ← interpLamSortAsUnlifted tyVal s
    let sort ← Expr.normalizeType (← Meta.inferType ty)
    let Expr.sort lvl := sort
      | throwError "{decl_name%} :: Unexpected sort {sort}"
    let .some (.defnInfo forallVal) := (← getEnv).find? ``forallF
      | throwError "{decl_name%} :: Unexpected error"
    let forallFExpr := forallVal.value.instantiateLevelParams forallVal.levelParams [lvl, .zero]
    return mkAppN forallFExpr #[← interpLamSortAsUnlifted tyVal s]
  | .existE s  => do
    return ← Meta.mkAppOptM ``Exists #[← interpLamSortAsUnlifted tyVal s]
  | .ite s     => do
    return ← Meta.mkAppOptM ``Bool.ite' #[← interpLamSortAsUnlifted tyVal s]

  /--
    Takes a `t : LamTerm` and produces the `un-lifted` version of `t.interp`.
    `lctx` is for pretty printing

    Note that `etom`s generated by the verified checker do not directly correspond
    to Lean expressions. Therefore, we need to introduce new free variables to
    represent `etom`s.
  -/
  def interpLamTermAsUnlifted
    (tyVal : Std.HashMap Nat Expr) (varVal : Std.HashMap Nat Expr) (etomVal : Std.HashMap Nat Expr)
    (lctx : Nat) : LamTerm → MetaM Expr
  | .atom n => do
    let .some e := varVal.get? n
      | throwError "{decl_name%} :: Cannot find fvarId assigned to term atom {n}"
    return e
  | .etom n => do
    let .some efvar := etomVal.get? n
      | throwError "{decl_name%} :: Cannot find fvarId assigned to etom {n}"
    return efvar
  | .base b => interpLamBaseTermAsUnlifted tyVal b
  | .bvar n => return .bvar n
  | .lam s t => do
    let sinterp ← interpLamSortAsUnlifted tyVal s
    let tinterp ← interpLamTermAsUnlifted tyVal varVal etomVal lctx.succ t
    let name := (`eb!).appendIndexAfter lctx
    return .lam name sinterp tinterp .default
  | .app _ fn arg => do
    let fninterp ← interpLamTermAsUnlifted tyVal varVal etomVal lctx fn
    let arginterp ← interpLamTermAsUnlifted tyVal varVal etomVal lctx arg
    return .app fninterp arginterp

end Lam2D


namespace Lam2D

  open Embedding.Lam

  def natConstSimpNFList : List (Name × Expr) :=
    let natc := mkConst ``Nat
    [
      (``Nat.add, mkApp4
        (.const ``HAdd.hAdd [.zero, .zero, .zero]) natc natc natc
        (mkApp2 (mkConst ``instHAdd [.zero]) natc (mkConst ``instAddNat))),
      (``Nat.sub, mkApp4
        (.const ``HSub.hSub [.zero, .zero, .zero]) natc natc natc
        (mkApp2 (mkConst ``instHSub [.zero]) natc (mkConst ``instSubNat))),
      (``Nat.mul, mkApp4
        (.const ``HMul.hMul [.zero, .zero, .zero]) natc natc natc
        (mkApp2 (mkConst ``instHMul [.zero]) natc (mkConst ``instMulNat))),
      (``Nat.div, mkApp4
        (.const ``HDiv.hDiv [.zero, .zero, .zero]) natc natc natc
        (mkApp2 (mkConst ``instHDiv [.zero]) natc (mkConst ``Nat.instDiv))),
      (``Nat.mod, mkApp4
        (.const ``HMod.hMod [.zero, .zero, .zero]) natc natc natc
        (mkApp2 (mkConst ``instHMod [.zero]) natc (mkConst ``Nat.instMod))),
      (``Nat.le, mkApp2 (.const ``LE.le [.zero]) natc (mkConst ``instLENat)),
      (``Nat.lt,  mkApp2 (.const ``LT.lt [.zero]) natc (mkConst ``instLTNat)),
      (``Nat.max, mkApp2 (.const ``Max.max [.zero]) natc (mkConst ``Nat.instMax)),
      (``Nat.min, mkApp2 (.const ``Min.min [.zero]) natc (mkConst ``instMinNat))
    ]

  open LamCstrD in
  def intConstSimpNFList : List (Name × Expr) :=
    let intc := mkConst ``Int
    -- **TODO: Int.abs**
    [
      (``Int.ofNat  , mkApp2 (.const ``Nat.cast [.zero]) intc (mkConst ``instNatCastInt)),
      (``Int.neg    , mkApp2 (.const ``Neg.neg [.zero]) intc (mkConst ``Int.instNegInt)),
      (``Int.add    , mkApp4
        (.const ``HAdd.hAdd [.zero, .zero, .zero]) intc intc intc
        (mkApp2 (.const ``instHAdd [.zero]) intc (mkConst ``Int.instAdd))),
      (``Int.sub    , mkApp4
        (.const ``HSub.hSub [.zero, .zero, .zero]) intc intc intc
        (mkApp2 (.const ``instHSub [.zero]) intc (mkConst ``Int.instSub))),
      (``Int.mul    , mkApp4
        (.const ``HMul.hMul [.zero, .zero, .zero]) intc intc intc
        (mkApp2 (.const ``instHMul [.zero]) intc (mkConst ``Int.instMul))),
      (``Int.ediv    , mkApp4
        (.const ``HDiv.hDiv [.zero, .zero, .zero]) intc intc intc
        (mkApp2 (.const ``instHDiv [.zero]) intc (mkConst ``Int.instDiv))),
      (``Int.emod    , mkApp4
        (.const ``HMod.hMod [.zero, .zero, .zero]) intc intc intc
        (mkApp2 (.const ``instHMod [.zero]) intc (mkConst ``Int.instMod))),
      (``Int.le     , mkApp2 (.const ``LE.le [.zero]) intc (mkConst ``Int.instLEInt)),
      (``Int.lt     , mkApp2 (.const ``LT.lt [.zero]) intc (mkConst ``Int.instLTInt)),
      (``Int.max    , mkApp2 (.const ``Max.max [.zero]) intc (mkConst ``Int.instMax)),
      (``Int.min    , mkApp2 (.const ``Min.min [.zero]) intc (mkConst ``Int.instMin))
    ]

  def stringConstSimpNFList : List (Name × Expr) :=
    let stringc := mkConst ``String
    -- **TODO: String.le**
    [
      (``String.append, mkApp4
        (.const ``HAppend.hAppend [.zero, .zero, .zero]) stringc stringc stringc
        (mkApp2 (.const ``instHAppendOfAppend [.zero]) stringc (mkConst ``String.instAppend))),
      (``String.lt, mkApp2 (.const ``LT.lt [.zero]) stringc (mkConst ``String.instLT)),
    ]

  open LamCstrD in
  def bitVecConstSimpNFList : List (Name × Expr) :=
    let natc := mkConst ``Nat
    let bitVecc := mkConst ``BitVec
    -- **TODO: BitVec.abs**
    [
      (``BitVec.add             , .lam `n natc (mkApp4
        (.const ``HAdd.hAdd [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHAdd [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instAdd) (.bvar 0)))) .default),
      (``BitVec.sub             , .lam `n natc (mkApp4
        (.const ``HSub.hSub [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHSub [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instSub) (.bvar 0)))) .default),
      (``BitVec.mul             , .lam `n natc (mkApp4
        (.const ``HMul.hMul [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHMul [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instMul) (.bvar 0)))) .default),
      (``BitVec.udiv            , .lam `n natc (mkApp4
        (.const ``HDiv.hDiv [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHDiv [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instDiv) (.bvar 0)))) .default),
      (``BitVec.umod            , .lam `n natc (mkApp4
        (.const ``HMod.hMod [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHMod [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instMod) (.bvar 0)))) .default),
      (``BitVec.neg             , .lam `n natc (mkApp2
        (.const ``Neg.neg [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instNeg) (.bvar 0))) .default),
      (``BitVec.propult         , .lam `n natc (mkApp2
        (.const ``LT.lt [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``instLTBitVec) (.bvar 0))) .default),
      (``BitVec.propule         , .lam `n natc (mkApp2
        (.const ``LE.le [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``instLEBitVec) (.bvar 0))) .default),
      (``BitVec.and             , .lam `n natc (mkApp4
        (.const ``HAnd.hAnd [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHAndOfAndOp [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instAndOp) (.bvar 0)))) .default),
      (``BitVec.or              , .lam `n natc (mkApp4
        (.const ``HOr.hOr [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHOrOfOrOp [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instOrOp) (.bvar 0)))) .default),
      (``BitVec.xor             , .lam `n natc (mkApp4
        (.const ``HXor.hXor [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0)) (.app bitVecc (.bvar 0))
        (mkApp2 (.const ``instHXorOfXorOp [.zero]) (.app bitVecc (.bvar 0)) (.app (mkConst ``BitVec.instXorOp) (.bvar 0)))) .default),
      (``BitVec.not             , .lam `n natc (mkApp2
        (.const ``Complement.complement [.zero]) (.app bitVecc (.bvar 0))
        (.app (mkConst ``BitVec.instComplement) (.bvar 0))) .default),
      (``BitVec.shiftLeft       , .lam `n natc (mkApp4
        (.const ``HShiftLeft.hShiftLeft [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) natc (.app bitVecc (.bvar 0))
        (.app (mkConst ``BitVec.instHShiftLeftNat) (.bvar 0))) .default),
      (``BitVec.ushiftRight     , .lam `n natc (mkApp4
        (.const ``HShiftRight.hShiftRight [.zero, .zero, .zero]) (.app bitVecc (.bvar 0)) natc (.app bitVecc (.bvar 0))
        (.app (mkConst ``BitVec.instHShiftRightNat) (.bvar 0))) .default),
      (``BitVec.smtHshiftLeft   , .lam `n natc (.lam `m natc (.lam `a (.app bitVecc (.bvar 1)) (.lam `b (.app bitVecc (.bvar 1)) (mkApp6
          (.const ``HShiftLeft.hShiftLeft [.zero, .zero, .zero]) (.app bitVecc (.bvar 3)) natc (.app bitVecc (.bvar 3))
          (.app (mkConst ``BitVec.instHShiftLeftNat) (.bvar 3)) (.bvar 1) (mkApp2 (mkConst ``BitVec.toNat) (.bvar 2) (.bvar 0))
        ) .default ) .default) .default) .default),
      (``BitVec.smtHushiftRight , .lam `n natc (.lam `m natc (.lam `a (.app bitVecc (.bvar 1)) (.lam `b (.app bitVecc (.bvar 1)) (mkApp6
          (.const ``HShiftRight.hShiftRight [.zero, .zero, .zero]) (.app bitVecc (.bvar 3)) natc (.app bitVecc (.bvar 3))
          (.app (mkConst ``BitVec.instHShiftRightNat) (.bvar 3)) (.bvar 1) (mkApp2 (mkConst ``BitVec.toNat) (.bvar 2) (.bvar 0))
        ) .default ) .default) .default) .default),
      (``BitVec.append          , .lam `n natc (.lam `m natc (mkApp4
        (.const ``HAppend.hAppend [.zero, .zero, .zero]) (.app bitVecc (.bvar 1)) (.app bitVecc (.bvar 0))
        (.app bitVecc (mkApp6
          (.const ``HAdd.hAdd [.zero, .zero, .zero]) natc natc natc
          (mkApp2 (.const ``instHAdd [.zero]) natc (mkConst ``instAddNat)) (.bvar 1) (.bvar 0)))
          (mkApp2 (.const ``BitVec.instHAppendHAddNat []) (.bvar 1) (.bvar 0))) .default) .default),
    ]

  def lamBaseTermSimpNFList : List (Name × Expr) :=
    natConstSimpNFList ++ intConstSimpNFList ++ stringConstSimpNFList ++ bitVecConstSimpNFList

  def lamBaseTermSimpNFMap : Std.HashMap Name Expr := Std.HashMap.ofList lamBaseTermSimpNFList

  section CheckDefEq

    private def checkLamBaseTermSimpNFMap : MetaM Unit :=
      for (name, e) in lamBaseTermSimpNFList do
        if !(← Meta.isTypeCorrect e) then
          throwError "{e} is not type correct"
        let e' := mkConst name
        if !(← Meta.withNewMCtxDepth (Meta.isDefEq e' e)) then
          throwError "{e'} is not definitionally equal to {e}"

    run_meta checkLamBaseTermSimpNFMap

  end CheckDefEq

  def approxSimpNF (e : Expr) : CoreM Expr := do
    let eRep := e.replace (fun sub =>
      match sub with
      | .const name _ => lamBaseTermSimpNFMap.get? name
      | _ => .none)
    let eRep ← Core.betaReduce eRep
    let replaceNatCast (e : Expr) : Option Expr :=
      match e with
      | mkApp3 (.const ``Nat.cast [.zero]) (.const ``Int []) (.const ``instNatCastInt []) (.lit (.natVal n)) =>
        let litn : Expr := .lit (.natVal n)
        mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Int []) litn (.app (.const ``instOfNat []) litn)
      | _ => none
    return eRep.replace replaceNatCast

end Lam2D
