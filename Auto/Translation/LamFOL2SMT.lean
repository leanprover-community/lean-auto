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
| .int    => .app (.symb "Int") #[]
| .string => .app (.symb "String") #[]
| .real   => .app (.symb "Real") #[]
| .bv n   => .app (.indexed "BitVec" (.inr n)) #[]

private def lamSort2SSortAux : LamSort → TransM LamAtom SSort
| .atom n => do
  if !(← hIn (.sort n)) then
    let name ← h2Symb (.sort n)
    addCommand (.declSort name 0)
  return .app (.symb (← h2Symb (.sort n))) #[]
| .base b => return lamBaseSort2SSort b
| .func _ _ => throwError "lamSort2STermAux :: Unexpected error. Higher order input?"

/-- Only translates first-order types -/
private def lamSort2SSort : LamSort → TransM LamAtom (List SSort × SSort)
| .func argTy resTy => do
  let (smargs, smres) ← lamSort2SSort resTy
  let smarg ← lamSort2SSortAux argTy
  return (smarg :: smargs, smres)
| s => return ([], ← lamSort2SSortAux s)

private def Int2STerm : Int → STerm
| .ofNat n   => .sConst (.num n)
| .negSucc n => .qIdApp (QualIdent.ofString "-") #[.sConst (.num (Nat.succ n))]

private def CstrReal2STerm : CstrReal → STerm
| .zero => .sConst (.num 0)
| .one  => .sConst (.num 1)

private def lamBaseTerm2STerm_Arity2 (arg1 arg2 : STerm) : LamBaseTerm → TransM LamAtom STerm
| .and        => return .qStrApp "and" #[arg1, arg2]
| .or         => return .qStrApp "or" #[arg1, arg2]
| .imp        => return .qStrApp "=>" #[arg1, arg2]
| .iff        => return .qStrApp "=" #[arg1, arg2]
| .bcst .andb => return .qStrApp "and" #[arg1, arg2]
| .bcst .orb  => return .qStrApp "or" #[arg1, arg2]
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
| t           => throwError "lamTerm2STerm :: The arity of {repr t} is not 2"

private def lamBaseTerm2STerm_Arity1 (arg : STerm) : LamBaseTerm → TransM LamAtom STerm
| .not        => return .qStrApp "not" #[arg]
| .bcst .notb => return .qStrApp "not" #[arg]
| .icst .iabs => return .qStrApp "abs" #[arg]
| .icst .ineg => return .qStrApp "-" #[Int2STerm 0, arg]
| t           => throwError "lamTerm2STerm :: The arity of {repr t} is not 1"

private def Bitvec2STerm (bv : List Bool) : STerm := .sConst (.binary bv)

private def lamBaseTerm2STerm_Arity0 : LamBaseTerm → TransM LamAtom STerm
| .trueE            => return .qStrApp "true" #[]
| .falseE           => return .qStrApp "false" #[]
| .bcst .trueb      => return .qStrApp "true" #[]
| .bcst .falseb     => return .qStrApp "false" #[]
| .icst (.intVal n) => return Int2STerm n
| .scst (.strVal s) => return .sConst (.str s)
| .realVal c        => return CstrReal2STerm c
| .bvVal bv         => return Bitvec2STerm bv
| t                 => throwError "lamTerm2STerm :: The arity of {repr t} is not 0"

private def lamTerm2STermAux (lamVarTy lamEVarTy : Array LamSort) (args : Array STerm) :
  LamTerm → TransM LamAtom STerm
| .atom n => do
  if !(← hIn (.term n)) then
    let name ← h2Symb (.term n)
    let .some s := lamVarTy[n]?
      | throwError "lamTerm2STerm :: Unexpected term atom {repr (LamTerm.atom n)}"
    let (argSorts, resSort) ← lamSort2SSort s
    if args.size != argSorts.length then
      throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return .qIdApp (QualIdent.ofString (← h2Symb (.term n))) args
| .etom n => do
  if !(← hIn (.etom n)) then
    let name ← h2Symb (.etom n)
    let .some s := lamEVarTy[n]?
      | throwError "lamTerm2STerm :: Unexpected etom {repr (LamTerm.etom n)}"
    let (argSorts, resSort) ← lamSort2SSort s
    if args.size != argSorts.length then
      throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return .qIdApp (QualIdent.ofString (← h2Symb (.etom n))) args
| .base b =>
  match args with
  | #[]       => lamBaseTerm2STerm_Arity0 b
  | #[u₁]     => lamBaseTerm2STerm_Arity1 u₁ b
  | #[u₁, u₂] => lamBaseTerm2STerm_Arity2 u₁ u₂ b
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
  let body' ← lamTerm2STerm lamVarTy lamEVarTy body
  return .forallE dname s' body'
| .app _ (.base (.existE _)) (.lam s body) => do
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let body' ← lamTerm2STerm lamVarTy lamEVarTy body
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

def intAuxDefs : Array IR.SMT.Command :=
  #[.defFun false "itdiv" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
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
def lamFOL2SMT (lamVarTy lamEVarTy : Array LamSort)
  (facts : Array LamTerm) : TransM LamAtom (Array IR.SMT.Command) := do
  let _ ← intAuxDefs.mapM addCommand
  for t in facts do
    let sterm ← lamTerm2STerm lamVarTy lamEVarTy t
    trace[auto.lamFOL2SMT] "λ term {repr t} translated to SMT term {sterm}"
    addCommand (.assert sterm)
  getCommands

end Auto