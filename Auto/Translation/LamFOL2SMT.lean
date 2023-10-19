import Lean
import Auto.Embedding.LamBase
import Auto.Translation.LamReif
import Auto.IR.SMT
open Lean

initialize
  registerTraceClass `auto.lamFOL2SMT

-- LamFOL2SMT : First-order fragment of simply-typed lambda calculus to SMT IR

namespace Auto

-- Open `Lam`
open Embedding.Lam
-- Open `SMT`
open IR.SMT

/-- High-level construct -/
private inductive LamAtom where
  | sort : Nat → LamAtom
  | term : Nat → LamAtom
  | etom : Nat → LamAtom
  | bvOfInt : Nat → LamAtom
  | bvToInt : Nat → LamAtom
  | bvRotLeft : Nat → LamAtom
  | bvRotRight : Nat → LamAtom
deriving Inhabited, Hashable, BEq

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

private def lamSortAtom2String (n : Nat) : TransM LamAtom String := do
  if !(← hIn (.sort n)) then
    let name ← h2Symb (.sort n)
    addCommand (.declSort name 0)
  return ← h2Symb (.sort n)

private def lamSort2SSortAux : LamSort → TransM LamAtom SSort
| .atom n => do return .app (.symb (← lamSortAtom2String n)) #[]
| .base b => return lamBaseSort2SSort b
| .func _ _ => throwError "lamSort2STermAux :: Unexpected error. Higher order input?"

/-- Only translates first-order types -/
private def lamSort2SSort : LamSort → TransM LamAtom (List SSort × SSort)
| .func argTy resTy => do
  let (smargs, smres) ← lamSort2SSort resTy
  let smarg ← lamSort2SSortAux argTy
  return (smarg :: smargs, smres)
| s => return ([], ← lamSort2SSortAux s)

private def addNatConstraint? (name : String) (s : LamSort) : TransM LamAtom Unit := do
  let resTy := s.getResTy
  if !(resTy == .base .nat) then
    return
  let args ← (Array.mk s.getArgTys).mapM (fun s => do return (s, ← IR.SMT.disposableName))
  let fnApp := STerm.qStrApp name (args.zipWithIndex.map (fun (_, n) => .bvar (args.size - 1 - n)))
  let mut fnConstr := STerm.qStrApp ">=" #[fnApp, .sConst (.num 0)]
  for (argTy, argName) in args.reverse do
    if argTy == .base .nat then
      fnConstr := .qStrApp "=>" #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], fnConstr]
    fnConstr := .forallE argName (← lamSort2SSortAux argTy) fnConstr
  addCommand (.assert fnConstr)

private def Int2STerm : Int → STerm
| .ofNat n   => .sConst (.num n)
| .negSucc n => .qIdApp (QualIdent.ofString "-") #[.sConst (.num (Nat.succ n))]

private def lamBvOfInt2String (n : Nat) : TransM LamAtom String := do
  if !(← hIn (.bvOfInt n)) then
    let name ← h2Symb (.bvOfInt n)
    let (argSorts, resSort) ← lamSort2SSort (.func (.base .int) (.base (.bv n)))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvOfInt n)

private def lamBvToInt2String (n : Nat) : TransM LamAtom String := do
  if !(← hIn (.bvToInt n)) then
    let name ← h2Symb (.bvToInt n)
    let (argSorts, resSort) ← lamSort2SSort (.func (.base (.bv n)) (.base .int))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvToInt n)

private def lamBvRotLeft2String (n : Nat) : TransM LamAtom String := do
  if !(← hIn (.bvRotLeft n)) then
    let name ← h2Symb (.bvRotLeft n)
    let (argSorts, resSort) ← lamSort2SSort (.func (.base (.bv n)) (.func (.base .int) (.base (.bv n))))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvRotLeft n)

private def lamBvRotRight2String (n : Nat) : TransM LamAtom String := do
  if !(← hIn (.bvRotRight n)) then
    let name ← h2Symb (.bvRotRight n)
    let (argSorts, resSort) ← lamSort2SSort (.func (.base (.bv n)) (.func (.base .int) (.base (.bv n))))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvRotRight n)

private def lamBaseTerm2STerm_Arity3 (arg1 arg2 arg3 : STerm) : LamBaseTerm → TransM LamAtom STerm
| .scst .srepall => return .qStrApp "str.replace_all" #[arg1, arg2, arg3]
| t              => throwError "lamTerm2STerm :: The arity of {repr t} is not 3"

private def lamBaseTerm2STerm_Arity2 (arg1 arg2 : STerm) : LamBaseTerm → TransM LamAtom STerm
| .and        => return .qStrApp "and" #[arg1, arg2]
| .or         => return .qStrApp "or" #[arg1, arg2]
| .imp        => return .qStrApp "=>" #[arg1, arg2]
| .iff        => return .qStrApp "=" #[arg1, arg2]
| .bcst .andb => return .qStrApp "and" #[arg1, arg2]
| .bcst .orb  => return .qStrApp "or" #[arg1, arg2]
| .ncst .nadd => return .qStrApp "+" #[arg1, arg2]
| .ncst .nsub => return .qStrApp "nsub" #[arg1, arg2]
| .ncst .nmul => return .qStrApp "*" #[arg1, arg2]
| .ncst .ndiv => return .qStrApp "iediv" #[arg1, arg2]
| .ncst .nmod => return .qStrApp "iemod" #[arg1, arg2]
| .ncst .nle  => return .qStrApp "<=" #[arg1, arg2]
| .ncst .nlt  => return .qStrApp "<" #[arg1, arg2]
| .icst .iadd => return .qStrApp "+" #[arg1, arg2]
| .icst .isub => return .qStrApp "-" #[arg1, arg2]
| .icst .imul => return .qStrApp "*" #[arg1, arg2]
| .icst .idiv => return .qStrApp "itdiv" #[arg1, arg2]
| .icst .imod => return .qStrApp "itmod" #[arg1, arg2]
| .icst .iediv => return .qStrApp "iediv" #[arg1, arg2]
| .icst .iemod => return .qStrApp "iemod" #[arg1, arg2]
| .icst .ile  => return .qStrApp "<=" #[arg1, arg2]
| .icst .ilt  => return .qStrApp "<" #[arg1, arg2]
| .scst .sapp => return .qStrApp "str.++" #[arg1, arg2]
| .scst .sle  => return .qStrApp "str.<=" #[arg1, arg2]
| .scst .slt  => return .qStrApp "str.<" #[arg1, arg2]
| .scst .sprefixof => return .qStrApp "str.prefixof" #[arg1, arg2]
| .bvcst (.bvadd _) => return .qStrApp "bvadd" #[arg1, arg2]
| .bvcst (.bvsub _) => return .qStrApp "bvadd" #[arg1, .qStrApp "bvneg" #[arg2]]
| .bvcst (.bvudiv _) => return .qStrApp "bvudiv" #[arg1, arg2]
| .bvcst (.bvurem _) => return .qStrApp "bvurem" #[arg1, arg2]
| .bvcst (.bvsdiv _) => return .qStrApp "bvsdiv" #[arg1, arg2]
| .bvcst (.bvsrem _) => return .qStrApp "bvsrem" #[arg1, arg2]
| .bvcst (.bvsmod _) => return .qStrApp "bvsmod" #[arg1, arg2]
| .bvcst (.bvult _) => return .qStrApp "bvult" #[arg1, arg2]
| .bvcst (.bvule _) => return .qStrApp "bvule" #[arg1, arg2]
| .bvcst (.bvslt _) => return .qStrApp "bvslt" #[arg1, arg2]
| .bvcst (.bvsle _) => return .qStrApp "bvsle" #[arg1, arg2]
| .bvcst (.bvand _) => return .qStrApp "bvand" #[arg1, arg2]
| .bvcst (.bvor _) => return .qStrApp "bvor" #[arg1, arg2]
| .bvcst (.bvxor _) => return .qStrApp "bvxor" #[arg1, arg2]
| .bvcst (.bvshl _) => throwError "std type mismatches smt-lib"
| .bvcst (.bvlshr _) => throwError "std type mismatches smt-lib"
| .bvcst (.bvashr _) => throwError "std type mismatches smt-lib"
| .bvcst (.bvrotateLeft w) =>
  match arg2 with
  | .sConst (.num n) => return .qIdApp (.ident (.indexed "rotate_left" #[.inr n])) #[arg1]
  | _ => return .qStrApp (← lamBvRotLeft2String w) #[arg1, arg2]
| .bvcst (.bvrotateRight w) =>
  match arg2 with
  | .sConst (.num n) => return .qIdApp (.ident (.indexed "rotate_right" #[.inr n])) #[arg1]
  | _ => return .qStrApp (← lamBvRotRight2String w) #[arg1, arg2]
| .bvcst (.bvappend _ _) => return .qStrApp "concat" #[arg1, arg2]
| .bvcst (.bvextract _ h l) => do
  let l := min h l
  return .qIdApp (.ident (.indexed "extract" #[.inr h, .inr l])) #[arg1, arg2]
| .bvcst (.bvzeroExtend _ _) => throwError "std type mismatches smt-lib"
| .bvcst (.bvsignExtend _ v) => return .qIdApp (.ident (.indexed "sign_extend" #[.inr v])) #[arg1, arg2]
| t           => throwError "lamTerm2STerm :: The arity of {repr t} is not 2"

private def lamBaseTerm2STerm_Arity1 (arg : STerm) : LamBaseTerm → TransM LamAtom STerm
| .not            => return .qStrApp "not" #[arg]
| .bcst .ofProp   => return arg
| .bcst .notb     => return .qStrApp "not" #[arg]
| .icst .iofNat   => return arg
| .icst .inegSucc => return .qStrApp "-" #[Int2STerm (-1), arg]
| .icst .iabs     => return .qStrApp "abs" #[arg]
| .icst .ineg     => return .qStrApp "-" #[Int2STerm 0, arg]
| .scst .slength  => return .qStrApp "str.len" #[arg]
| .bvcst (.bvofNat n) => do return .qStrApp (← lamBvOfInt2String n) #[arg]
| .bvcst (.bvtoNat n) => do return .qStrApp (← lamBvToInt2String n) #[arg]
| .bvcst (.bvofInt n) => do return .qStrApp (← lamBvOfInt2String n) #[arg]
| .bvcst (.bvtoInt n) => do return .qStrApp (← lamBvToInt2String n) #[arg]
| .bvcst (.bvneg _) => return .qStrApp "bvneg" #[arg]
| .bvcst (.bvabs _) => return .qStrApp "bvabs" #[arg]
| .bvcst (.bvrepeat _ i) => return .qIdApp (.ident (.indexed "repeat" #[.inr i])) #[arg]
| t               => throwError "lamTerm2STerm :: The arity of {repr t} is not 1"

private def BitVec2STerm (n i : Nat) : STerm :=
  let digs := (Nat.toDigits 2 (i % (2^n))).map (fun c => c == '1')
  let digs := (List.range (n - digs.length)).map (fun _ => false) ++ digs
  .sConst (.binary digs)

private def lamBaseTerm2STerm_Arity0 : LamBaseTerm → TransM LamAtom STerm
| .trueE              => return .qStrApp "true" #[]
| .falseE             => return .qStrApp "false" #[]
| .bcst .trueb        => return .qStrApp "true" #[]
| .bcst .falseb       => return .qStrApp "false" #[]
| .ncst (.natVal n)   => return .sConst (.num n)
| .icst (.intVal n)   => return Int2STerm n
| .scst (.strVal s)   => return .sConst (.str s)
| .bvcst (.bvVal n i) => return BitVec2STerm n i
| t                   => throwError "lamTerm2STerm :: The arity of {repr t} is not 0"

def lamTermAtom2String (lamVarTy : Array LamSort) (n : Nat) : TransM LamAtom (LamSort × String) := do
  let .some s := lamVarTy[n]?
    | throwError "lamTermAtom2String :: Unexpected term atom {repr (LamTerm.atom n)}"
  -- Empty type is not inhabited
  if s == .base .empty then
    addCommand (.assert (.qStrApp "false" #[]))
  if !(← hIn (.term n)) then
    let name ← h2Symb (.term n)
    let (argSorts, resSort) ← lamSort2SSort s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addNatConstraint? name s
  return (s, ← h2Symb (.term n))

def lamTermEtom2String (lamEVarTy : Array LamSort) (n : Nat) : TransM LamAtom (LamSort × String) := do
  let .some s := lamEVarTy[n]?
    | throwError "lamTerm2STerm :: Unexpected etom {repr (LamTerm.etom n)}"
  -- Empty type is not inhabited
  if s == .base .empty then
    addCommand (.assert (.qStrApp "false" #[]))
  if !(← hIn (.etom n)) then
    let name ← h2Symb (.etom n)
    let (argSorts, resSort) ← lamSort2SSort s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addNatConstraint? name s
  return (s, ← h2Symb (.etom n))

private def lamTerm2STermAux (lamVarTy lamEVarTy : Array LamSort) (args : Array STerm) :
  LamTerm → TransM LamAtom STerm
| .atom n => do
  let (s, name) ← lamTermAtom2String lamVarTy n
  if args.size != s.getArgTys.length then
    throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
  return .qIdApp (QualIdent.ofString name) args
| .etom n => do
  let (s, name) ← lamTermEtom2String lamEVarTy n
  if args.size != s.getArgTys.length then
    throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
  return .qIdApp (QualIdent.ofString name) args
| .base b =>
  match args with
  | #[]           => lamBaseTerm2STerm_Arity0 b
  | #[u₁]         => lamBaseTerm2STerm_Arity1 u₁ b
  | #[u₁, u₂]     => lamBaseTerm2STerm_Arity2 u₁ u₂ b
  | #[u₁, u₂, u₃] => lamBaseTerm2STerm_Arity3 u₁ u₂ u₃ b
  | _         => throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
| t => throwError "lamTerm2STerm :: Unexpected head term {repr t}"

private partial def lamTerm2STerm (lamVarTy lamEVarTy : Array LamSort) :
  LamTerm → TransM LamAtom STerm
| .base b => lamBaseTerm2STerm_Arity0 b
| .bvar n => return .bvar n
| .app _ (.app _ (.base (.eqI _)) _) _ =>
  throwError ("lamTerm2STerm :: " ++ LamReif.exportError.ImpPolyLog)
| .app _ (.base (.forallEI _)) (.lam _ _) =>
  throwError ("lamTerm2STerm :: " ++ LamReif.exportError.ImpPolyLog)
| .app _ (.base (.existEI _)) (.lam _ _) =>
  throwError ("lamTerm2STerm :: " ++ LamReif.exportError.ImpPolyLog)
| .app _ (.app _ (.app _ (.base (.condI _)) _) _) _ =>
  throwError ("lamTerm2STerm :: " ++ LamReif.exportError.ImpPolyLog)
| .app _ (.app _ (.base (.eq _)) arg₁) arg₂ => do
  let arg₁' ← lamTerm2STerm lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm lamVarTy lamEVarTy arg₂
  return .qIdApp (QualIdent.ofString "=") #[arg₁', arg₂']
| .app _ (.base (.forallE _)) (.lam s body) => do
  -- Empty type is not inhabited
  if s == .base .empty then
    return .qStrApp "true" #[]
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let mut body' ← lamTerm2STerm lamVarTy lamEVarTy body
  if s == .base .nat then
    body' := .qStrApp "=>" #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], body']
  return .forallE dname s' body'
| .app _ (.base (.existE _)) (.lam s body) => do
  -- Empty type is not inhabited
  if s == .base .empty then
    return .qStrApp "false" #[]
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let mut body' ← lamTerm2STerm lamVarTy lamEVarTy body
  if s == .base .nat then
    body' := .qStrApp "=>" #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], body']
  return .existE dname s' body'
| .app _ (.app _ (.app _ (.base (.cond _)) cond) arg₁) arg₂ => do
  let cond' ← lamTerm2STerm lamVarTy lamEVarTy cond
  let arg₁' ← lamTerm2STerm lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm lamVarTy lamEVarTy arg₂
  return .qStrApp "ite" #[cond', arg₁', arg₂']
| t => do
  let (ts, t) := splitApp t
  let ts' ← ts.mapM (lamTerm2STerm lamVarTy lamEVarTy)
  lamTerm2STermAux lamVarTy lamEVarTy ts' t
where
  splitApp : LamTerm → Array LamTerm × LamTerm
  | .app _ fn arg =>
    let (ts, t) := splitApp fn
    (ts.push arg, t)
  | t => (#[], t)

private def lamMutualIndInfo2STerm (mind : MutualIndInfo) : TransM LamAtom IR.SMT.Command := do
  let mut infos := #[]
  -- Go through `type` and call `h2Symb` on all the atoms so that there won't
  --   be declared during the following `lamSort2SSort`
  for ⟨type, _⟩ in mind do
    let .atom sn := type
      | throwError "lamMutualIndInfo2STerm :: Inductive type {type} is not a sort atom"
    -- Do not use `lamSortAtom2String` because we don't want to `declare-sort`
    let _ ← h2Symb (.sort sn)
  for ⟨type, ctors⟩ in mind do
    let .atom sn := type
      | throwError "lamMutualIndInfo2STerm :: Unexpected error"
    let sname ← h2Symb (.sort sn)
    let mut cstrDecls : Array ConstrDecl := #[]
    for (s, t) in ctors do
      let ctorname ← (do
        match t with
        -- Do not use `lamSortAtom2String` because we don't want to `declare-fun`
        | .atom n => h2Symb (.term n)
        -- Do not use `lamSortEtom2String` because we don't want to `declare-fun`
        | .etom n => h2Symb (.etom n)
        | _ => throwError "")
      let (argTys, _) ← lamSort2SSort s
      let selDecls := (Array.mk argTys).zipWithIndex.map (fun (argTy, idx) =>
        (ctorname ++ s!"_sel{idx}", argTy))
      cstrDecls := cstrDecls.push ⟨ctorname, selDecls⟩
    infos := infos.push (sname, 0, ⟨#[], cstrDecls⟩)
  return .declDtypes infos

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

/-- `facts` should not contain import versions of `eq, ∀` or `∃` -/
def lamFOL2SMT
  (lamVarTy lamEVarTy : Array LamSort)
  (facts : Array LamTerm) (minds : Array MutualIndInfo) :
  TransM LamAtom (Array IR.SMT.Command) := do
  let _ ← sortAuxDecls.mapM addCommand
  let _ ← termAuxDecls.mapM addCommand
  for mind in minds do
    let ddecls ← lamMutualIndInfo2STerm mind
    trace[auto.lamFOL2SMT] "MutualIndInfo translated to command {ddecls}"
    addCommand ddecls
  for t in facts do
    let sterm ← lamTerm2STerm lamVarTy lamEVarTy t
    trace[auto.lamFOL2SMT] "λ term {repr t} translated to SMT term {sterm}"
    addCommand (.assert sterm)
  getCommands

end Auto