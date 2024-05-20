import Lean
import Auto.Embedding.LamChecker
import Auto.IR.SMT
import Auto.Solver.SMT
import Auto.Translation.LamUtils
open Lean

initialize
  registerTraceClass `auto.lamFOL2SMT
  registerTraceClass `auto.lamFOL2SMT.nameSuggestion

-- LamFOL2SMT : First-order fragment of simply-typed lambda calculus to SMT IR

namespace Auto

-- Open `Lam`
open Embedding.Lam
-- Open `SMT`
open IR.SMT

namespace SMT

/-- High-level construct -/
private inductive LamAtomic where
  /- Sort atom -/
  | sort     : Nat → LamAtomic
  /- Term atom -/
  | term     : Nat → LamAtomic
  | etom     : Nat → LamAtomic
  /-
    · To SMT solvers `.bvofNat` is the same as `.bvofInt`
    · `.bvtoInt` can be defined using `.bvtoNat`
  -/
  | bvOfNat  : Nat → LamAtomic
  | bvToNat  : Nat → LamAtomic
  | compCtor : LamTerm → LamAtomic
  | compProj : LamTerm → LamAtomic
deriving Inhabited, Hashable, BEq

private def LamAtomic.toString : LamAtomic → String
| .sort n     => s!"sort {n}"
| .term n     => s!"term {n}"
| .etom n     => s!"etom {n}"
| .bvOfNat n  => s!"bvOfNat {n}"
| .bvToNat n  => s!"bvToNat {n}"
| .compCtor t => s!"compCtor {t}"
| .compProj t => s!"compProj {t}"

instance : ToString LamAtomic where
  toString := LamAtomic.toString

def LamAtomic.toLeanExpr
  (tyValMap varValMap etomValMap : HashMap Nat Expr)
  (atomic : LamAtomic) : MetaM Expr:=
  match atomic with
  | .sort n => do
    let .some e := tyValMap.find? n
      | throwError "SMT.printValuation :: Unknown sort atom {n}"
    return e
  | .term n => do
    let .some e := varValMap.find? n
      | throwError "SMT.printValuation :: Unknown term atom {n}"
    return e
  | .etom n => do
    let .some e := etomValMap.find? n
      | throwError "SMT.printValuation :: Unknown etom {n}"
    return e
  | .bvOfNat n => do
    let e := Expr.app (.const ``BitVec.ofNat []) (.lit (.natVal n))
    return e
  | .bvToNat n => do
    let e := Expr.app (.const ``BitVec.toNat []) (.lit (.natVal n))
    return e
  | .compCtor t => do
    let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
    return e
  | .compProj t => do
    let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
    return e

structure SMTNamingInfo where
  tyVal     : Array (Expr × Level)
  varVal    : Array (Expr × LamSort)
  lamEVarTy : Array LamSort

def SMTNamingInfo.exprToSuggestion (e : Expr) : MetaM String := do
    let ppSyntax := (← PrettyPrinter.delab e).raw
    return toString (← PrettyPrinter.formatTerm ppSyntax)

def SMTNamingInfo.suggestNameForSort (sni : SMTNamingInfo) (s : LamSort) := do
  let suggestion := ((← go s).take 1).toLower
  trace[auto.lamFOL2SMT.nameSuggestion] "`{suggestion}` for LamSort `{s}`"
  return suggestion
where
  go : LamSort → MetaM String
  | .atom n => do
    let .some (e, _) := sni.tyVal[n]?
      | throwError "lamSortAtom2String :: Unexpected sort atom {repr (LamSort.atom n)}"
    exprToSuggestion e
  | .base b => return b.toString
  -- Suggest name based on return type
  | .func _ argTy => go argTy

def SMTNamingInfo.suggestNameForAtomic (sni : SMTNamingInfo) (a : LamAtomic) : MetaM String := do
  let suggestion ← go a
  trace[auto.lamFOL2SMT.nameSuggestion] "`{suggestion}` for LamAtomic `{a}`"
  return suggestion
where
  go : LamAtomic → MetaM String
  | .sort n => do
    let .some (e, _) := sni.tyVal[n]?
      | throwError "lamSortAtom2String :: Unexpected sort atom {repr (LamSort.atom n)}"
    exprToSuggestion e
  | .term n => do
    let .some (e, _) := sni.varVal[n]?
      | throwError "lamTermAtom2String :: Unexpected term atom {repr (LamTerm.atom n)}"
    exprToSuggestion e
  | .etom n => return s!"sk{n}"
  | .bvOfNat n => exprToSuggestion (Expr.app (.const ``BitVec.ofNat []) (.lit (.natVal n)))
  | .bvToNat n => exprToSuggestion (Expr.app (.const ``BitVec.toNat []) (.lit (.natVal n)))
  -- **TODO**
  | .compCtor _ => return "cC"
  -- **TODO**
  | .compProj _ => return "cP"

private def lamBaseSort2SSort : LamBaseSort → SSort
| .prop   => .app (.symb "Bool") #[]
| .bool   => .app (.symb "Bool") #[]
-- `Nat ≅ {x : Int | x ≥ 0}`
| .nat    => .app (.symb "Int") #[]
| .int    => .app (.symb "Int") #[]
| .isto0 p =>
  match p with
  | .xH => .app (.symb "String") #[]
  | .xO .xH => .app (.symb "Empty") #[]
  | _   => .app (.symb "Empty") #[]
| .bv n   => .app (.indexed "BitVec" #[.inr n]) #[]

private def lamSortAtom2String (sni : SMTNamingInfo) (n : Nat) : TransM LamAtomic String := do
  if !(← hIn (.sort n)) then
    let name ← h2Symb (.sort n) (← sni.suggestNameForAtomic (.sort n))
    addCommand (.declSort name 0)
  return ← h2Symb (.sort n) .none

private def lamSort2SSortAux (sni : SMTNamingInfo) : LamSort → TransM LamAtomic SSort
| .atom n => do return .app (.symb (← lamSortAtom2String sni n)) #[]
| .base b => return lamBaseSort2SSort b
| .func _ _ => throwError "lamSort2STermAux :: Unexpected error. Higher order input?"

/-- Only translates first-order types -/
private def lamSort2SSort (sni : SMTNamingInfo) : LamSort → TransM LamAtomic (List SSort × SSort)
| .func argTy resTy => do
  let (smargs, smres) ← lamSort2SSort sni resTy
  let smarg ← lamSort2SSortAux sni argTy
  return (smarg :: smargs, smres)
| s => return ([], ← lamSort2SSortAux sni s)

private def addNatConstraint? (sni : SMTNamingInfo) (name : String) (s : LamSort) : TransM LamAtomic Unit := do
  let resTy := s.getResTy
  if !(resTy == .base .nat) then
    return
  let args ← (Array.mk s.getArgTys).mapM (fun s => do return (s, ← IR.SMT.disposableName (← sni.suggestNameForSort s)))
  let fnApp := STerm.qStrApp name (args.zipWithIndex.map (fun (_, n) => .bvar (args.size - 1 - n)))
  let mut fnConstr := STerm.qStrApp ">=" #[fnApp, .sConst (.num 0)]
  for (argTy, argName) in args.reverse do
    if argTy == .base .nat then
      fnConstr := .qStrApp "=>" #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], fnConstr]
    fnConstr := .forallE argName (← lamSort2SSortAux sni argTy) fnConstr
  addCommand (.assert fnConstr)

private def int2STerm : Int → STerm
| .ofNat n   => .sConst (.num n)
| .negSucc n => .qIdApp (QualIdent.ofString "-") #[.sConst (.num (Nat.succ n))]

private def lamBvOfNat2String (sni : SMTNamingInfo) (n : Nat) : TransM LamAtomic String := do
  if !(← hIn (.bvOfNat n)) then
    let name ← h2Symb (.bvOfNat n) (← sni.suggestNameForAtomic (.bvOfNat n))
    let (argSorts, resSort) ← lamSort2SSort sni (.func (.base .int) (.base (.bv n)))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvOfNat n) .none

private def lamBvToNat2String (sni : SMTNamingInfo) (n : Nat) : TransM LamAtomic String := do
  if !(← hIn (.bvToNat n)) then
    let name ← h2Symb (.bvToNat n) (← sni.suggestNameForAtomic (.bvToNat n))
    let (argSorts, resSort) ← lamSort2SSort sni (.func (.base (.bv n)) (.base .int))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvToNat n) .none

private def bitVec2STerm (n i : Nat) : STerm :=
  let digs := (Nat.toDigits 2 (i % (2^n))).map (fun c => c == '1')
  let digs := (List.range (n - digs.length)).map (fun _ => false) ++ digs
  .sConst (.binary digs)

private def lamBaseTerm2STerm_Arity3 (arg1 arg2 arg3 : STerm) : LamBaseTerm → TransM LamAtomic STerm
| .scst .srepall => return .qStrApp "str.replace_all" #[arg1, arg2, arg3]
| t              => throwError "lamTerm2STerm :: The arity of {repr t} is not 3"

private def lamBaseTerm2STerm_Arity2 (arg1 arg2 : STerm) : LamBaseTerm → TransM LamAtomic STerm
| .pcst .and  => return .qStrApp "and" #[arg1, arg2]
| .pcst .or   => return .qStrApp "or" #[arg1, arg2]
| .pcst .imp  => return .qStrApp "=>" #[arg1, arg2]
| .pcst .iff  => return .qStrApp "=" #[arg1, arg2]
| .bcst .andb => return .qStrApp "and" #[arg1, arg2]
| .bcst .orb  => return .qStrApp "or" #[arg1, arg2]
| .ncst .nadd => return .qStrApp "+" #[arg1, arg2]
| .ncst .nsub => return .qStrApp "nsub" #[arg1, arg2]
| .ncst .nmul => return .qStrApp "*" #[arg1, arg2]
| .ncst .ndiv => return .qStrApp "iediv" #[arg1, arg2]
| .ncst .nmod => return .qStrApp "iemod" #[arg1, arg2]
| .ncst .nle  => return .qStrApp "<=" #[arg1, arg2]
| .ncst .nlt  => return .qStrApp "<" #[arg1, arg2]
| .ncst .nmax => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg2, arg1]
| .ncst .nmin => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg1, arg2]
| .icst .iadd => return .qStrApp "+" #[arg1, arg2]
| .icst .isub => return .qStrApp "-" #[arg1, arg2]
| .icst .imul => return .qStrApp "*" #[arg1, arg2]
| .icst .idiv => return .qStrApp "itdiv" #[arg1, arg2]
| .icst .imod => return .qStrApp "itmod" #[arg1, arg2]
| .icst .iediv => return .qStrApp "iediv" #[arg1, arg2]
| .icst .iemod => return .qStrApp "iemod" #[arg1, arg2]
| .icst .ile  => return .qStrApp "<=" #[arg1, arg2]
| .icst .ilt  => return .qStrApp "<" #[arg1, arg2]
| .icst .imax => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg2, arg1]
| .icst .imin => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg1, arg2]
| .scst .sapp => return .qStrApp "str.++" #[arg1, arg2]
| .scst .sle  => return .qStrApp "str.<=" #[arg1, arg2]
| .scst .slt  => return .qStrApp "str.<" #[arg1, arg2]
| .scst .sprefixof => return .qStrApp "str.prefixof" #[arg1, arg2]
| .bvcst (.bvaOp _ op) =>
  match op with
  | .add => return .qStrApp "bvadd" #[arg1, arg2]
  | .sub => return .qStrApp "bvadd" #[arg1, .qStrApp "bvneg" #[arg2]]
  | .mul => return .qStrApp "bvmul" #[arg1, arg2]
  | .udiv => return .qStrApp "bvudiv" #[arg1, arg2]
  | .urem => return .qStrApp "bvurem" #[arg1, arg2]
  | .sdiv => return .qStrApp "bvsdiv" #[arg1, arg2]
  | .srem => return .qStrApp "bvsrem" #[arg1, arg2]
  | .smod => return .qStrApp "bvsmod" #[arg1, arg2]
| .bvcst (.bvcmp _ _ op) =>
  match op with
  | .ult => return .qStrApp "bvult" #[arg1, arg2]
  | .ule => return .qStrApp "bvule" #[arg1, arg2]
  | .slt => return .qStrApp "bvslt" #[arg1, arg2]
  | .sle => return .qStrApp "bvsle" #[arg1, arg2]
| .bvcst (.bvand _) => return .qStrApp "bvand" #[arg1, arg2]
| .bvcst (.bvor _) => return .qStrApp "bvor" #[arg1, arg2]
| .bvcst (.bvxor _) => return .qStrApp "bvxor" #[arg1, arg2]
| .bvcst (.bvshOp _ smt? op) =>
  match smt? with
  | false =>
    throwError "lamTerm2STerm :: Non-smt shift operations should not occur here"
  | true =>
    match op with
    | .shl => return .qStrApp "bvshl" #[arg1, arg2]
    | .lshr => return .qStrApp "bvlshr" #[arg1, arg2]
    | .ashr => return .qStrApp "bvashr" #[arg1, arg2]
| .bvcst (.bvappend _ _) => return .qStrApp "concat" #[arg1, arg2]
| .ocst (.smtAttr1T name _ _) => return .attrApp name arg1 arg2
| t           => throwError "lamTerm2STerm :: The arity of {repr t} is not 2"

private def lamBaseTerm2STerm_Arity1 (sni : SMTNamingInfo) (arg : STerm) : LamBaseTerm → TransM LamAtomic STerm
| .pcst .not             => return .qStrApp "not" #[arg]
| .bcst .ofProp          => return arg
| .bcst .notb            => return .qStrApp "not" #[arg]
| .icst .iofNat          => return arg
| .icst .inegSucc        => return .qStrApp "-" #[int2STerm (-1), arg]
| .icst .ineg            => return .qStrApp "-" #[int2STerm 0, arg]
| .icst .iabs            => return .qStrApp "abs" #[arg]
| .scst .slength         => return .qStrApp "str.len" #[arg]
-- To SMT solvers `.bvofNat` is the same as `.bvofInt`
| .bvcst (.bvofNat n)    => do
  let name ← solverName
  if name == .z3 || name == .cvc5 then
    return .qIdApp (.ident (.indexed "int2bv" #[.inr n])) #[arg]
  else
    return .qStrApp (← lamBvOfNat2String sni n) #[arg]
| .bvcst (.bvtoNat n)    => do
  let name ← solverName
  if name == .z3 || name == .cvc5 then
    return .qStrApp "bv2nat" #[arg]
  else
    return .qStrApp (← lamBvToNat2String sni n) #[arg]
| .bvcst (.bvofInt n)    => do
  let name ← solverName
  if name == .z3 || name == .cvc5 then
    return .qIdApp (.ident (.indexed "int2bv" #[.inr n])) #[arg]
  else
    return .qStrApp (← lamBvOfNat2String sni n) #[arg]
| .bvcst (.bvtoInt n)    => do
  let name ← solverName
  let msbExpr := mkSMTMsbExpr n arg
  if name == .z3 || name == .cvc5 then
    let arg1 := .qStrApp "-" #[.qStrApp "bv2nat" #[arg], .sConst (.num (2 ^ n))]
    let arg2 := .qStrApp "bv2nat" #[arg]
    return .qStrApp "ite" #[msbExpr, arg1, arg2]
  else
    let arg1 := .qStrApp "-" #[.qStrApp (← lamBvToNat2String sni n) #[arg], .sConst (.num (2 ^ n))]
    let arg2 := .qStrApp (← lamBvToNat2String sni n) #[arg]
    return .qStrApp "ite" #[msbExpr, arg1, arg2]
-- @BitVec.msb n a = not ((a &&& (1 <<< (n - 1))) = 0#n)
| .bvcst (.bvmsb n)      => return mkSMTMsbExpr n arg
| .bvcst (.bvneg _)      => return .qStrApp "bvneg" #[arg]
| .bvcst (.bvabs _)      => return .qStrApp "bvabs" #[arg]
| .bvcst (.bvnot _)      => return .qStrApp "bvnot" #[arg]
| .bvcst (.bvextract _ h l) => do
  let l := min h l
  return .qIdApp (.ident (.indexed "extract" #[.inr h, .inr l])) #[arg]
| .bvcst (.bvrepeat _ i) => return .qIdApp (.ident (.indexed "repeat" #[.inr i])) #[arg]
| .bvcst (.bvzeroExtend w v) =>
  if v ≥ w then
    return .qIdApp (.ident (.indexed "zero_extend" #[.inr (v - w)])) #[arg]
  else
    return .qIdApp (.ident (.indexed "extract" #[.inr (v - 1), .inr 0])) #[arg]
| .bvcst (.bvsignExtend w v) =>
  if v ≥ w then
    return .qIdApp (.ident (.indexed "sign_extend" #[.inr (v - w)])) #[arg]
  else
    return .qIdApp (.ident (.indexed "extract" #[.inr (v - 1), .inr 0])) #[arg]
| t               => throwError "lamTerm2STerm :: The arity of {repr t} is not 1"
where
  solverName : MetaM Solver.SMT.SolverName := do
    return Solver.SMT.auto.smt.solver.name.get (← getOptions)
  mkSMTMsbExpr (n : Nat) (arg : STerm) : STerm :=
    let andExpr := .qStrApp "bvand" #[arg, .qStrApp "bvshl" #[bitVec2STerm n 1, bitVec2STerm n (n - 1)]]
    .qStrApp "not" #[.qStrApp "=" #[andExpr, bitVec2STerm n 0]]

private def lamBaseTerm2STerm_Arity0 : LamBaseTerm → TransM LamAtomic STerm
| .pcst .trueE        => return .qStrApp "true" #[]
| .pcst .falseE       => return .qStrApp "false" #[]
| .bcst .trueb        => return .qStrApp "true" #[]
| .bcst .falseb       => return .qStrApp "false" #[]
| .ncst (.natVal n)   => return .sConst (.num n)
| .scst (.strVal s)   => return .sConst (.str s)
| .bvcst (.bvVal n i) => return bitVec2STerm n i
| t                   => throwError "lamTerm2STerm :: The arity of {repr t} is not 0"

def lamTermAtom2String (sni : SMTNamingInfo) (lamVarTy : Array LamSort) (n : Nat) : TransM LamAtomic (LamSort × String) := do
  let .some s := lamVarTy[n]?
    | throwError "lamTermAtom2String :: Unexpected term atom {repr (LamTerm.atom n)}"
  -- Empty type is not inhabited
  if s == .base .empty then
    addCommand (.assert (.qStrApp "false" #[]))
  if !(← hIn (.term n)) then
    let name ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
    let (argSorts, resSort) ← lamSort2SSort sni s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addNatConstraint? sni name s
  return (s, ← h2Symb (.term n) .none)

def lamTermEtom2String (sni : SMTNamingInfo) (lamEVarTy : Array LamSort) (n : Nat) : TransM LamAtomic (LamSort × String) := do
  let .some s := lamEVarTy[n]?
    | throwError "lamTerm2STerm :: Unexpected etom {repr (LamTerm.etom n)}"
  -- Empty type is not inhabited
  if s == .base .empty then
    addCommand (.assert (.qStrApp "false" #[]))
  if !(← hIn (.etom n)) then
    let name ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
    let (argSorts, resSort) ← lamSort2SSort sni s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addNatConstraint? sni name s
  return (s, ← h2Symb (.etom n) .none)

private def lamTerm2STermAux (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort) (args : Array STerm) :
  LamTerm → TransM LamAtomic STerm
| .atom n => do
  let (s, name) ← lamTermAtom2String sni lamVarTy n
  if args.size != s.getArgTys.length then
    throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
  return .qIdApp (QualIdent.ofString name) args
| .etom n => do
  let (s, name) ← lamTermEtom2String sni lamEVarTy n
  if args.size != s.getArgTys.length then
    throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
  return .qIdApp (QualIdent.ofString name) args
| .base b =>
  match args with
  | #[]           => lamBaseTerm2STerm_Arity0 b
  | #[u₁]         => lamBaseTerm2STerm_Arity1 sni u₁ b
  | #[u₁, u₂]     => lamBaseTerm2STerm_Arity2 u₁ u₂ b
  | #[u₁, u₂, u₃] => lamBaseTerm2STerm_Arity3 u₁ u₂ u₃ b
  | _         => throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
| t => throwError "lamTerm2STerm :: Unexpected head term {repr t}"

def lamQuantified2STerm (sni : SMTNamingInfo) (forall? : Bool) (s : LamSort) (body : TransM LamAtomic STerm) : TransM LamAtomic STerm := do
  -- Empty type is not inhabited
  if s == .base .empty then
    return .qStrApp "true" #[]
  let dname ← disposableName (← sni.suggestNameForSort s)
  let s' ← lamSort2SSortAux sni s
  let mut body' ← body
  if s == .base .nat then
    let connective := if forall? then "=>" else "and"
    body' := .qStrApp connective #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], body']
  match forall? with
  | true => return .forallE dname s' body'
  | false => return .existE dname s' body'

private partial def lamTerm2STerm (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort) :
  LamTerm → TransM LamAtomic STerm
| .base b => lamBaseTerm2STerm_Arity0 b
| .bvar n => return .bvar n
| .app _ (.app _ (.base (.eqI _)) _) _ =>
  throwError ("lamTerm2STerm :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.base (.forallEI _)) (.lam _ _) =>
  throwError ("lamTerm2STerm :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.base (.existEI _)) (.lam _ _) =>
  throwError ("lamTerm2STerm :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.app _ (.app _ (.base (.iteI _)) _) _) _ =>
  throwError ("lamTerm2STerm :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.app _ (.base (.eq _)) arg₁) arg₂ => do
  let arg₁' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₂
  return .qIdApp (QualIdent.ofString "=") #[arg₁', arg₂']
| .app _ (.base (.forallE _)) (.lam s body) => do
  lamQuantified2STerm sni true s (lamTerm2STerm sni lamVarTy lamEVarTy body)
| .app _ (.base (.existE _)) (.lam s body) => do
  lamQuantified2STerm sni false s (lamTerm2STerm sni lamVarTy lamEVarTy body)
| .app _ (.app _ (.app _ (.base (.ite _)) cond) arg₁) arg₂ => do
  let cond' ← lamTerm2STerm sni lamVarTy lamEVarTy cond
  let arg₁' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₂
  return .qStrApp "ite" #[cond', arg₁', arg₂']
| t => do
  let (ts, t) := splitApp t
  let ts' ← ts.mapM (lamTerm2STerm sni lamVarTy lamEVarTy)
  lamTerm2STermAux sni lamVarTy lamEVarTy ts' t
where
  splitApp : LamTerm → Array LamTerm × LamTerm
  | .app _ fn arg =>
    let (ts, t) := splitApp fn
    (ts.push arg, t)
  | t => (#[], t)

private def lamMutualIndInfo2STerm (sni : SMTNamingInfo) (mind : MutualIndInfo) :
  TransM LamAtomic (IR.SMT.Command ×
    Array (String × LamSort × LamTerm) ×
    Array (String × LamSort × LamTerm)) := do
  let mut infos := #[]
  let mut compCtors := #[]
  let mut compProjs := #[]
  -- Go through `type` and call `h2Symb` on all the atoms so that there won't
  --   be declared during the following `lamSort2SSort`
  for ⟨type, _, _⟩ in mind do
    let .atom sn := type
      | throwError "lamMutualIndInfo2STerm :: Inductive type {type} is not a sort atom"
    -- Do not use `lamSortAtom2String` because we don't want to `declare-sort`
    let _ ← h2Symb (.sort sn) (← sni.suggestNameForAtomic (.sort sn))
  for ⟨type, ctors, projs⟩ in mind do
    let .atom sn := type
      | throwError "lamMutualIndInfo2STerm :: Unexpected error"
    let mut projInfos : Array (LamSort × String) := #[]
    if let .some projs := projs then
      if ctors.length != 1 then
        throwError "lamMutualIndInfo2STerm :: Unexpected error"
      for (s, t) in projs do
        let mut projname := ""
        match t with
        | .atom n => projname ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
        | .etom n => projname ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
        | t       =>
          projname ← h2Symb (.compProj t) (← sni.suggestNameForAtomic (.compProj t))
          compProjs := compProjs.push (projname, s, t)
        projInfos := projInfos.push (s, projname)
    let sname ← h2Symb (.sort sn) .none
    let mut cstrDecls : Array ConstrDecl := #[]
    for (s, t) in ctors do
      let mut ctorname := ""
      match t with
      -- Do not use `lamSortAtom2String` because we don't want to `declare-fun`
      | .atom n => ctorname ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
      -- Do not use `lamSortEtom2String` because we don't want to `declare-fun`
      | .etom n => ctorname ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
      | t       =>
        ctorname ← h2Symb (.compCtor t) (← sni.suggestNameForAtomic (.compCtor t))
        compCtors := compCtors.push (ctorname, s, t)
      let (argTys, _) ← lamSort2SSort sni s
      let mut selDecls := #[]
      if projs.isSome then
        if argTys.length != projInfos.size then
          throwError "lamMutualIndInfo2STerm :: Unexpected error"
        selDecls := ((Array.mk argTys).zip projInfos).map (fun (argTy, _, name) => (name, argTy))
      else
        selDecls := (Array.mk argTys).zipWithIndex.map (fun (argTy, idx) =>
          (ctorname ++ s!"_sel{idx}", argTy))
      cstrDecls := cstrDecls.push ⟨ctorname, selDecls⟩
    infos := infos.push (sname, 0, ⟨#[], cstrDecls⟩)
  return (.declDtypes infos, compCtors, compProjs)

private def compEqn
  (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort)
  (compInfo : String × LamSort × LamTerm) : TransM LamAtomic IR.SMT.Command := do
  let (name, s, t) := compInfo
  let argTys := s.getArgTys
  let sbvars := (List.range argTys.length).map (fun n => .bvar (argTys.length - 1 - n))
  let slhs := .qStrApp name ⟨sbvars⟩
  let srhs := ← lamTerm2STerm sni lamVarTy lamEVarTy (LamTerm.bvarAppsRev t argTys).headBeta
  let mut eqn := pure (.qStrApp "=" #[slhs, srhs])
  for s in argTys.reverse do
    eqn := lamQuantified2STerm sni true s eqn
  return .assert (← eqn)

def sortAuxDecls : Array IR.SMT.Command :=
  #[.declSort "Empty" 0]

def termAuxDecls : Array IR.SMT.Command :=
  #[.defFun false "nsub" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp ">=" #[.qStrApp "x" #[], .qStrApp "y" #[]], .qStrApp "-" #[.qStrApp "x" #[], .qStrApp "y" #[]], .sConst (.num 0)]),
    .defFun false "itdiv" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .qStrApp "x" #[],
        .qStrApp "ite" #[.qStrApp ">=" #[.qStrApp "x" #[], .sConst (.num 0)],
          .qStrApp "div" #[.qStrApp "x" #[], .qStrApp "y" #[]],
          .qStrApp "-" #[.qStrApp "div" #[.qStrApp "-" #[.qStrApp "x" #[]], .qStrApp "y" #[]]]]]),
    .defFun false "itmod" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .qStrApp "x" #[],
        .qStrApp "ite" #[.qStrApp ">=" #[.qStrApp "x" #[], .sConst (.num 0)],
          .qStrApp "mod" #[.qStrApp "x" #[], .qStrApp "y" #[]],
          .qStrApp "-" #[.qStrApp "mod" #[.qStrApp "-" #[.qStrApp "x" #[]], .qStrApp "y" #[]]]]]),
    .defFun false "iediv" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .sConst (.num 0), .qStrApp "div" #[.qStrApp "x" #[], .qStrApp "y" #[]]]),
    .defFun false "iemod" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .qStrApp "x" #[], .qStrApp "mod" #[.qStrApp "x" #[], .qStrApp "y" #[]]])
   ]

/--
  `printFn : (tyValMap : _) → (varValMap : _) → (etomValMap : _) → MetaM α`
-/
def withExprValuation
  {α : Type} [Inhabited α] (sni : SMTNamingInfo) (h2lMap : HashMap LamAtomic String)
  (printFn : HashMap Nat Expr → HashMap Nat Expr → HashMap Nat Expr → MetaM α) :
  MetaM α := do
  let tyValMap := HashMap.ofList (sni.tyVal.zipWithIndex.map (fun ((e, _), n) => (n, e))).data
  let varValMap := HashMap.ofList (sni.varVal.zipWithIndex.map (fun ((e, _), n) => (n, e))).data
  let etomsWithName := h2lMap.toArray.filterMap (fun (atomic, name) =>
    match atomic with | .etom n => .some (n, name) | _ => .none)
  let declInfos ← etomsWithName.mapM (fun (n, name) => do
    let .some s := sni.lamEVarTy[n]?
      | throwError "SMT.printValuation :: Unknown etom {n}"
    let type ← Lam2D.interpLamSortAsUnlifted tyValMap s
    return ((name : Name), .default, fun _ => pure type))
  Meta.withLocalDecls declInfos (fun etomFVars => do
    let etomValMap := HashMap.ofList ((etomsWithName.zip etomFVars).map (fun ((n, _), e) => (n, e))).data
    printFn tyValMap varValMap etomValMap)

end SMT

open SMT in
/--
  `facts` should not contain import versions of `eq, ∀` or `∃`
  `valid_fact_{i}` corresponds to the `i`-th entry in `facts`
-/
def lamFOL2SMT
  (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort)
  (facts : Array LamTerm) (minds : Array MutualIndInfo) :
  TransM LamAtomic (Array IR.SMT.Command × Array STerm) := do
  let _ ← sortAuxDecls.mapM addCommand
  let _ ← termAuxDecls.mapM addCommand
  for mind in minds do
    let (dsdecl, compCtors, compProjs) ← lamMutualIndInfo2STerm sni mind
    trace[auto.lamFOL2SMT] "MutualIndInfo translated to command {dsdecl}"
    addCommand dsdecl
    let compCtorEqns ← compCtors.mapM (compEqn sni lamVarTy lamEVarTy)
    let _ ← compCtorEqns.mapM addCommand
    let compProjEqns ← compProjs.mapM (compEqn sni lamVarTy lamEVarTy)
    let _ ← compProjEqns.mapM addCommand
  let mut validFacts := #[]
  for (t, idx) in facts.zipWithIndex do
    let sterm ← lamTerm2STerm sni lamVarTy lamEVarTy t
    validFacts := validFacts.push sterm
    trace[auto.lamFOL2SMT] "λ term {repr t} translated to SMT term {sterm}"
    addCommand (.assert (.attr sterm #[.symb "named" s!"valid_fact_{idx}"]))
  let commands ← getCommands
  return (commands, validFacts)

end Auto
