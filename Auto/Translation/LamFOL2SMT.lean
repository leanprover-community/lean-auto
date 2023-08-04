import Lean
import Auto.Embedding.LamBase
import Auto.Translation.LamReif
import Auto.IR.SMT
open Lean

-- LamFOL2SMT : First-order fragment of simply-typed lambda calculus
--   to SMT IR

namespace Auto

-- Open `Lam`
open Embedding.Lam
-- Open `SMT`
open IR.SMT

-- High-level construct
private inductive LamAtom where
  | sort : Nat → LamAtom
  | term : Nat → LamAtom
deriving Inhabited, Hashable, BEq

private def lamBaseSort2SSort : LamBaseSort → SSort
| .prop => .app (.symb "Bool") #[]
| .int  => .app (.symb "Int") #[]
| .real => .app (.symb "Real") #[]
| .bv n => .app (.indexed "BitVec" (.inr n)) #[]

private def lamSort2SSortAux : LamSort → TransM LamAtom SSort
| .atom n => do
  if !(← hIn (.sort n)) then
    let name ← h2Symb (.sort n)
    addCommand (.declSort name 0)
  return .app (.symb (← h2Symb (.sort n))) #[]
| .base b => return lamBaseSort2SSort b
| .func _ _ => throwError "lamSort2STermAux :: Unexpected error. Higher-order input?"

-- Only translates first-order types
private def lamSort2SSort : LamSort → TransM LamAtom (List SSort × SSort)
| .func argTy resTy => do
  let (smargs, smres) ← lamSort2SSort resTy
  let smarg ← lamSort2SSortAux argTy
  return (smarg :: smargs, smres)
| s => return ([], ← lamSort2SSortAux s)

private def lamBaseTerm2STerm_Arity2 (arg1 arg2 : STerm) : LamBaseTerm → TransM LamAtom STerm
| .and    => return .qIdApp (QualIdent.ofString "and") #[arg1, arg2]
| .or     => return .qIdApp (QualIdent.ofString "or") #[arg1, arg2]
| .imp    => return .qIdApp (QualIdent.ofString "=>") #[arg1, arg2]
| .iff    => return .qIdApp (QualIdent.ofString "xor") #[arg1, arg2]
| t       => throwError "lamTerm2STerm :: The arity of {repr t} is not 2"

private def lamBaseTerm2STerm_Arity1 (arg : STerm) : LamBaseTerm → TransM LamAtom STerm
| .not => return .qIdApp (QualIdent.ofString "not") #[arg]
| t    => throwError "lamTerm2STerm :: The arity of {repr t} is not 1"

private def Int2STerm : Int → STerm
| .ofNat n   => .sConst (.num n)
| .negSucc n => .qIdApp (QualIdent.ofString "-") #[.sConst (.num (Nat.succ n))]

private def CstrReal2STerm : CstrReal → STerm
| .zero => .sConst (.num 0)
| .one  => .sConst (.num 1)

private def Bitvec2STerm (bv : List Bool) : STerm := .sConst (.binary bv)

private def lamBaseTerm2STerm_Arity0 : LamBaseTerm → TransM LamAtom STerm
| .trueE     => return .qIdApp (QualIdent.ofString "true") #[]
| .falseE    => return .qIdApp (QualIdent.ofString "false") #[]
| .intVal n  => return Int2STerm n
| .realVal c => return CstrReal2STerm c
| .bvVal bv  => return Bitvec2STerm bv
| t          => throwError "lamTerm2STerm :: The arity of {repr t} is not 0"

private def lamTerm2STermAux (lamVarTy : Array LamSort) (args : Array STerm) :
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
| .base b =>
  match args with
  | #[]       => lamBaseTerm2STerm_Arity0 b
  | #[u₁]     => lamBaseTerm2STerm_Arity1 u₁ b
  | #[u₁, u₂] => lamBaseTerm2STerm_Arity2 u₁ u₂ b
  | _         => throwError "lamTerm2STerm :: Argument number mismatch. Higher order input?"
| t => throwError "lamTerm2STerm :: Unexpected head term {repr t}"

private partial def lamTerm2STerm (lamVarTy : Array LamSort) :
  LamTerm → TransM LamAtom STerm
| .base b => lamBaseTerm2STerm_Arity0 b
| .bvar n => return .bvar n
| .app (.app (.base (.eq _)) arg₁) arg₂ => do
  let arg₁' ← lamTerm2STerm lamVarTy arg₁
  let arg₂' ← lamTerm2STerm lamVarTy arg₂
  return .qIdApp (QualIdent.ofString "=") #[arg₁', arg₂']
| .app (.base (.forallE _)) (.lam s body) => do
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let body' ← lamTerm2STerm lamVarTy body
  return .forallE dname s' body'
| .app (.base (.existE _)) (.lam s body) => do
  let s' ← lamSort2SSortAux s
  let dname ← disposableName
  let body' ← lamTerm2STerm lamVarTy body
  return .existE dname s' body'
| t => do
  let (ts, t) := splitApp t
  let ts' ← ts.mapM (lamTerm2STerm lamVarTy)
  lamTerm2STermAux lamVarTy ts' t
where
  splitApp : LamTerm → Array LamTerm × LamTerm
  | .app fn arg =>
    let (ts, t) := splitApp fn
    (ts.push arg, t)
  | t => (#[], t)

def lamFOL2SMT (s : LamReif.State) : TransM LamAtom (Array IR.SMT.Command) := do
  let assertions := s.assertions
  let lamVarTy : Array LamSort := s.lamVarTy.map (·.2)
  for (_, lterm) in assertions do
    let sterm ← lamTerm2STerm lamVarTy lterm
    addCommand (.assert sterm)
  getCommands

end Auto