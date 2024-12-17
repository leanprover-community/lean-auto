import Lean

open Lean

namespace EvalAuto

def Name.getConstsOfModule (module : Name) : CoreM (Array Name) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throwError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, _) ← readModuleData mFile
  return mod.constNames

/-- Used as a wrapper in other functions -/
def Name.getCi (name : Name) (parentFunc : Name) : CoreM ConstantInfo := do
  let .some ci := (← getEnv).find? name
    | throwError "{parentFunc} :: Cannot find name {name}"
  return ci

/-- Used as a wrapper in other functions -/
def Name.hasValue (name : Name) (parentFunc : Name) : CoreM Bool := do
  return (← Name.getCi name parentFunc).value?.isSome

/-- Used as a wrapper in other functions -/
def Name.getValue (name : Name) (parentFunc : Name) : CoreM Expr := do
  let .some v := (← Name.getCi name parentFunc).value?
    | throwError "{parentFunc} :: {name} has no value"
  return v

def Name.isTheorem (name : Name) : CoreM Bool := do
  let .some ci := (← getEnv).find? name
    | throwError "Name.isTheorem :: Cannot find name {name}"
  let .thmInfo _ := ci
    | return false
  return true

/--
  A constant is a human theorem iff it is a theorem and has a
  declaration range. Roughly speaking, a constant have a declaration
  range iff it is defined (presumably by a human) in a `.lean` file
-/
def Name.isHumanTheorem (name : Name) : CoreM Bool := do
  let hasDeclRange := (← Lean.findDeclarationRanges? name).isSome
  let isTheorem ← Name.isTheorem name
  let notProjFn := !(← Lean.isProjectionFn name)
  return hasDeclRange && isTheorem && notProjFn

def allHumanTheorems : CoreM (Array Name) := do
  let allConsts := (← getEnv).constants.toList.map Prod.fst
  let allHumanTheorems ← allConsts.filterM Name.isHumanTheorem
  return Array.mk allHumanTheorems

/-- Return the theorems that occurs in an expression -/
def Expr.getUsedTheorems (e : Expr) : CoreM (Array Name) :=
  e.getUsedConstants.filterM Name.isTheorem

/-- Return the theorems that are used in the declaration body of a constant -/
def Name.getUsedTheorems (name : Name) : CoreM (Array Name) := do
  let v ← Name.getValue name decl_name%
  Expr.getUsedTheorems v

/-- Return true if the expression `e` only uses constants present in `names` -/
def Expr.onlyUsesConsts (e : Expr) (names : Array Name) : Bool :=
  e.getUsedConstants.all (fun name => names.contains name)

/-- Return true if the declaration body of `name` only
  uses constants present in `names` -/
def Name.onlyUsesConsts (name : Name) (names : Array Name) : CoreM Bool := do
  let v ← Name.getValue name decl_name%
  return Expr.onlyUsesConsts v names

/-- Return true if the type `name` only uses constants present in `names` -/
def Name.onlyUsesConstsInType (name : Name) (names : Array Name) : CoreM Bool := do
  let ci ← Name.getCi name decl_name%
  return Expr.onlyUsesConsts ci.type names

/-- Used to filter out theorems known to SMT solvers and native provers-/
def logicConsts : Array Name := #[
    ``True, ``False,
    ``Not, ``And, ``Or, ``Iff,
    ``Eq
  ]

/-- Used to filter out theorems known to SMT solvers -/
def boolConsts : Array Name := #[
    ``Bool,
    ``true, ``false,
    ``Bool.and, ``Bool.or, ``Bool.xor, ``Bool.not,
    ``BEq, ``BEq.beq, ``bne, ``instBEqOfDecidableEq, ``instDecidableEqBool,
    ``ite, ``cond,
    ``Decidable, ``Decidable.decide
  ]

/-- Used to filter out theorems known to SMT solvers -/
def natConsts : Array Name := #[
    ``Nat,
    ``OfNat.ofNat, ``instOfNatNat,
    ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod,
    ``HAdd, ``HAdd.hAdd, ``instHAdd, ``instAddNat,
    ``HSub, ``HSub.hSub, ``instHSub, ``instSubNat,
    ``HMul, ``HMul.hMul, ``instHMul, ``instMulNat,
    ``HDiv, ``HDiv.hDiv, ``instHDiv, ``Nat.instDiv,
    ``HMod, ``HMod.hMod, ``instHMod, ``Nat.instMod,
    ``LE, ``LE.le, ``instLENat,
    ``LT, ``LT.lt, ``instLTNat,
    ``GE.ge, ``GT.gt
  ]

/- **TODO:** Int theorems -/

def Name.onlyLogicInType (name : Name) :=
  Name.onlyUsesConstsInType name logicConsts

def Name.onlyBoolLogicInType (name : Name) :=
  Name.onlyUsesConstsInType name (logicConsts ++ boolConsts)

def Name.onlyNatBoolLogicInType (name : Name) :=
  Name.onlyUsesConstsInType name (logicConsts ++ boolConsts ++ natConsts)

/-- Obtain Logic, Bool and Nat theorems -/
def analyze : CoreM (Array (Array Name)) := do
  let a ← allHumanTheorems
  let logicThms ← a.filterM Name.onlyLogicInType
  let boolThms ← a.filterM (fun name =>
    return (!(← Name.onlyLogicInType name)) && (← Name.onlyBoolLogicInType name))
  let natThms ← a.filterM (fun name =>
    return (!(← Name.onlyBoolLogicInType name)) && (← Name.onlyNatBoolLogicInType name))
  return #[logicThms, boolThms, natThms]

end EvalAuto
