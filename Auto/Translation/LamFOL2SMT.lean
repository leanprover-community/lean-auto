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
  | _   => .app (.symb "Empty") #[]
| .bv n   => .app (.indexed "BitVec" (.inr n)) #[]

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
| .ncst .nge  => return .qStrApp ">=" #[arg1, arg2]
| .ncst .nlt  => return .qStrApp "<" #[arg1, arg2]
| .ncst .ngt  => return .qStrApp ">" #[arg1, arg2]
| .icst .iadd => return .qStrApp "+" #[arg1, arg2]
| .icst .isub => return .qStrApp "-" #[arg1, arg2]
| .icst .imul => return .qStrApp "*" #[arg1, arg2]
| .icst .idiv => return .qStrApp "itdiv" #[arg1, arg2]
| .icst .imod => return .qStrApp "itmod" #[arg1, arg2]
| .icst .iediv => return .qStrApp "iediv" #[arg1, arg2]
| .icst .iemod => return .qStrApp "iemod" #[arg1, arg2]
| .icst .ile  => return .qStrApp "<=" #[arg1, arg2]
| .icst .ige  => return .qStrApp ">=" #[arg1, arg2]
| .icst .ilt  => return .qStrApp "<" #[arg1, arg2]
| .icst .igt  => return .qStrApp ">" #[arg1, arg2]
| .scst .sapp => return .qStrApp "str.++" #[arg1, arg2]
| .scst .sle  => return .qStrApp "str.<=" #[arg1, arg2]
| .scst .sge  => return .qStrApp "str.<=" #[arg2, arg1]
| .scst .slt  => return .qStrApp "str.<" #[arg1, arg2]
| .scst .sgt  => return .qStrApp "str.<" #[arg2, arg1]
| .scst .sprefixof => return .qStrApp "str.prefixof" #[arg1, arg2]
| t           => throwError "lamTerm2STerm :: The arity of {repr t} is not 2"

private def lamBaseTerm2STerm_Arity1 (arg : STerm) : LamBaseTerm → TransM LamAtom STerm
| .not            => return .qStrApp "not" #[arg]
| .bcst .notb     => return .qStrApp "not" #[arg]
| .icst .iofNat   => return arg
| .icst .inegSucc => return .qStrApp "-" #[Int2STerm (-1), arg]
| .icst .iabs     => return .qStrApp "abs" #[arg]
| .icst .ineg     => return .qStrApp "-" #[Int2STerm 0, arg]
| .scst .slength  => return .qStrApp "str.len" #[arg]
| t               => throwError "lamTerm2STerm :: The arity of {repr t} is not 1"

private def Bitvec2STerm (bv : List Bool) : STerm := .sConst (.binary bv)

private def lamBaseTerm2STerm_Arity0 : LamBaseTerm → TransM LamAtom STerm
| .trueE            => return .qStrApp "true" #[]
| .falseE           => return .qStrApp "false" #[]
| .bcst .trueb      => return .qStrApp "true" #[]
| .bcst .falseb     => return .qStrApp "false" #[]
| .ncst (.natVal n) => return .sConst (.num n)
| .icst (.intVal n) => return Int2STerm n
| .scst (.strVal s) => return .sConst (.str s)
| .bvVal bv         => return Bitvec2STerm bv
| t                 => throwError "lamTerm2STerm :: The arity of {repr t} is not 0"

def lamTermAtom2String (lamVarTy : Array LamSort) (n : Nat) : TransM LamAtom (LamSort × String) := do
  let .some s := lamVarTy[n]?
    | throwError "lamTermAtom2String :: Unexpected term atom {repr (LamTerm.atom n)}"
  if !(← hIn (.term n)) then
    let name ← h2Symb (.term n)
    let (argSorts, resSort) ← lamSort2SSort s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addNatConstraint? name s
  return (s, ← h2Symb (.term n))

def lamTermEtom2String (lamEVarTy : Array LamSort) (n : Nat) : TransM LamAtom (LamSort × String) := do
  let .some s := lamEVarTy[n]?
    | throwError "lamTerm2STerm :: Unexpected etom {repr (LamTerm.etom n)}"
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
| .app _ (.app _ (.base (.eq _)) arg₁) arg₂ => do
  let arg₁' ← lamTerm2STerm lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm lamVarTy lamEVarTy arg₂
  return .qIdApp (QualIdent.ofString "=") #[arg₁', arg₂']
| .app _ (.base (.forallE _)) (.lam s body) => do
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let mut body' ← lamTerm2STerm lamVarTy lamEVarTy body
  if s == .base .nat then
    body' := .qStrApp "=>" #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], body']
  return .forallE dname s' body'
| .app _ (.base (.existE _)) (.lam s body) => do
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let mut body' ← lamTerm2STerm lamVarTy lamEVarTy body
  if s == .base .nat then
    body' := .qStrApp "=>" #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], body']
  return .existE dname s' body'
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

def sortAuxDefs : Array IR.SMT.Command :=
  #[.declSort "Empty" 0]

def intAuxDefs : Array IR.SMT.Command :=
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
  let _ ← sortAuxDefs.mapM addCommand
  let _ ← intAuxDefs.mapM addCommand
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