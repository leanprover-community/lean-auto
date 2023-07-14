import Lean
import Auto.Util.MonadUtils
open Lean

-- smt-lib 2

namespace Auto

namespace IR.SMT

-- <index>      ::= <numeral> | <symbol>
-- <identifier> ::= <symbol> | (_ <symbol> <index>+)

private instance : Hashable (String ⊕ Nat) where
  hash : String ⊕ Nat → UInt64
  | .inl s => hash ("0" ++ s)
  | .inr n => hash ("1" ++ toString n)

inductive SIdent where
  | symb    : String → SIdent
  | indexed : String → (String ⊕ Nat) → SIdent
deriving BEq, Hashable, Inhabited

instance : ToString SIdent where
  toString : SIdent → String
  | .symb s => "|" ++ s ++ "|"
  | .indexed s idx =>
    match idx with
    | .inl idx => s!"(_ {s} {idx})"
    | .inr idx => s!"(_ {s} {idx})"

inductive SSort where
  | bvar : Nat → SSort -- Only useful in sort declarations
  | app : SIdent → Array SSort → SSort
deriving BEq, Hashable, Inhabited

private def SSort.toString_Aux : SSort → List SIdent → String
| .bvar i, binders =>
  if h : i < binders.length then
    s!"{binders[i]}"
  else
    panic!"SSort.toString :: Loose bound variable"
| .app i ⟨[]⟩, _ => s!"{i}"
| .app i ⟨a :: as⟩, binders =>
  let intro := s!"({i} "
  let head := SSort.toString_Aux a binders ++ " "
  let tail := String.intercalate " " (go as binders)
  intro ++ head ++ tail ++ ")"
where go : List SSort → List SIdent →  List String 
| [], _ => []
| a :: as, binders => SSort.toString_Aux a binders :: go as binders

def SSort.toString (s : SSort) (binders : Array SIdent) : String :=
  SSort.toString_Aux s binders.data

-- Caution : Do not use this in define-sort, because sort
--   there might contain bvars
instance : ToString SSort where
  toString s := SSort.toString s #[]

-- 〈qual_identifier〉 ::= 〈identifier〉 | ( as 〈identifier〉 〈sort〉 )
inductive QualIdent where
  | ident   : SIdent → QualIdent
  | qualed  : SIdent → SSort → QualIdent
deriving BEq, Hashable, Inhabited

def QualIdent.ofString (s : String) : QualIdent := .ident (.symb s)

instance : ToString QualIdent where
  toString : QualIdent → String
  | .ident i => toString i
  | .qualed i s => s!"(as {i} {s})"

structure MatchCase (α : Sort u) where
  constr : String
  args   : Array String
  body   : α

inductive STerm where
  | sConst  : STerm
  | bvar    : Nat → STerm                      -- De bruijin index
  | qIdApp  : QualIdent → Array STerm → STerm  -- Application of function symbol to array of terms
  | letE    : (name : String) → (binding : STerm) → (body : STerm) → STerm
  | forallE : (name : String) → (binderType : SSort) → (body : STerm) → STerm
  | existsE : (name : String) → (binderType : SSort) → (body : STerm) → STerm
  | matchE  : (matchTerm : STerm) → Array (MatchCase STerm) → STerm

private def STerm.toString_Aux : STerm → List SIdent → String
  | .sConst, _         => panic!"STerm.toString :: Unimplemented"
  | .bvar i, binders   =>
    if let some si := binders.get? i then
      ToString.toString si
    else
      panic!"STerm.toString :: Loose bound variable"
  | .qIdApp si ⟨[]⟩, _   => ToString.toString si
  | .qIdApp si ⟨a :: as⟩, binders =>
    let intro := s!"({si} "
    let tail := String.intercalate " " (STerm.toString_Aux a binders :: goQIdApp as binders)
    intro ++ tail ++ ")"
  | .letE name binding body, binders =>
    let binders := (SIdent.symb name) :: binders
    let intro := s!"(let ({SIdent.symb name} "
    let binding := STerm.toString_Aux binding binders ++ ") "
    let body := STerm.toString_Aux body binders ++ ")"
    intro ++ binding ++ body
  | .forallE name binderType body, binders =>
    let binders := (SIdent.symb name) :: binders
    let intro := s!"(forall ({SIdent.symb name} "
    let binderType := ToString.toString binderType ++ ") "
    let body := STerm.toString_Aux body binders ++ ")"
    intro ++ binderType ++ body
  | .existsE name binderType body, binders =>
    let binders := (SIdent.symb name) :: binders
    let intro := s!"(exists ({SIdent.symb name} "
    let binderType := ToString.toString binderType ++ ") "
    let body := STerm.toString_Aux body binders ++ ")"
    intro ++ binderType ++ body
  | .matchE _ ⟨[]⟩, _ => panic!"STerm.toString :: Zero match branches"
  | .matchE matchTerm ⟨a :: as⟩, binders =>
    let intro := s!"(match " ++ STerm.toString_Aux matchTerm binders ++ " ("
    let intro := intro ++ goMatchBranch a binders
    let body := String.join ((goMatchBody as binders).map (fun s => " " ++ s)) ++ "))"
    intro ++ body
where
  goQIdApp : List STerm → List SIdent → List String
    | [], _ => []
    | a :: as, binders => STerm.toString_Aux a binders :: goQIdApp as binders
  goMatchBranch : MatchCase STerm → List SIdent → String
    | ⟨constr, args, body⟩, binders =>
      if args.size == 0 then
        let body := " " ++ STerm.toString_Aux body binders ++ ")"
        let pattern := "(" ++ (ToString.toString (SIdent.symb constr))
        pattern ++ body
      else
        let binders := args.data.map .symb ++ binders
        let body := " " ++ STerm.toString_Aux body binders ++ ")"
        let args := args.data.map (fun x => ToString.toString (SIdent.symb x))
        let pattern := "((" ++ String.intercalate " " (ToString.toString (SIdent.symb constr) :: args) ++ ")"
        pattern ++ body
  goMatchBody : List (MatchCase STerm) → List SIdent → List String
    | [], _ => []
    | a :: as, binders => goMatchBranch a binders :: goMatchBody as binders

def STerm.toString (s : STerm) (binders : Array SIdent) : String :=
  STerm.toString_Aux s binders.data

instance : ToString STerm where
  toString s := STerm.toString s #[]

--〈selector_dec〉 ::= ( 〈symbol〉 〈sort〉 )
--〈constructor_dec〉 ::= ( 〈symbol〉 〈selector_dec〉∗ )
structure ConstrDecl where
  name     : String
  selDecls : Array (String × SSort)

private def ConstrDecl.toString : ConstrDecl → Array SIdent → String
| ⟨name, selDecls⟩, binders =>
  let pre := s!"({SIdent.symb name}"
  let selDecls := selDecls.map (fun (name, sort) => s!"({SIdent.symb name}" ++ SSort.toString sort binders ++ ")")
  String.intercalate " " (pre :: selDecls.data) ++ ")"

--〈sorted_var〉   ::= ( 〈symbol〉 〈sort〉 )
--〈datatype_dec〉 ::= ( 〈constructor_dec〉+ ) | ( par ( 〈symbol〉+ ) ( 〈constructor_dec〉+ ) )
--〈function_dec〉 ::= ( 〈symbol〉 ( 〈sorted_var〉∗ ) 〈sort〉 )
--〈function_def〉 ::= 〈symbol〉 ( 〈sorted_var〉∗ ) 〈sort〉 〈term〉
-- command   ::= ( assert 〈term〉 )
--               ( check-sat )
--               ...
--               ( declare-fun 〈symbol〉 ( 〈sort〉∗ ) 〈sort〉 )
--               ( declare-sort 〈symbol〉 〈numeral〉 )
--               ( define-fun 〈function_def〉 )
--               ( define-fun-rec 〈function_def〉 )
--               ( define-sort 〈symbol〉 ( 〈symbol〉∗ ) 〈sort〉 )
--               ( declare-datatype 〈symbol〉 〈datatype_dec〉)
--               ...
--               ( set-logic 〈symbol 〉 )
inductive Command where
  | assert    : (prop : STerm) → Command
  | setLogic  : String → Command
  | checkSat  : Command
  | declFun   : (name : String) → (argSorts : Array SSort) → (resSort : SSort) → Command
  | declSort  : (name : String) → (arity : Nat) → Command
  | defFun    : (isRec : Bool) → (name : String) → (args : Array (String × SSort)) →
                  (resTy : SSort) → (body : STerm) → Command
  | defSort   : (name : String) → (args : Array String) → (body : SSort) → Command
  | declDtype : (name : String) → (params : Array String) → (cstrDecls : Array ConstrDecl) → Command

def Command.toString : Command → String
| .assert prop                         =>
  s!"(assert {prop})"
| .setLogic l                          =>
  "(set-logic " ++ l ++ ")"
| .checkSat                            =>
  "(check-sat)"
| .declFun name argSorts resSort       =>
  let pre := s!"(declare-fun {SIdent.symb name} ("
  let argSorts := String.intercalate " " (argSorts.map ToString.toString).data ++ ") "
  let trail := s!"{resSort})"
  pre ++ argSorts ++ trail
| .declSort name arity                 => s!"(declare-sort {SIdent.symb name} {arity})"
| .defFun isRec name args resTy body =>
  let pre := if isRec then "(define-fun-rec " else "(define-fun "
  let pre := pre ++ ToString.toString (SIdent.symb name) ++ " "
  let binders := "(" ++ String.intercalate " " (args.map (fun (name, sort) => s!"({SIdent.symb name} {sort})")).data ++ ") "
  let trail := s!"{resTy} " ++ STerm.toString body (args.map (fun (name, _) => SIdent.symb name)) ++ ")"
  pre ++ binders ++ trail
| .defSort name args body              =>
  let pre := s!"(define-sort {SIdent.symb name} ("
  let sargs := String.intercalate " " args.data ++ ") "
  let trail := SSort.toString body (args.map SIdent.symb) ++ ")"
  pre ++ sargs ++ trail
| .declDtype name params cstrDecls     =>
  let pre := s!"(decare-datatype {SIdent.symb name} ("
  let sparams :=
    if params.size == 0 then ""
    else "par ("  ++ String.intercalate " " params.data ++ ") "
  let scstrDecls := cstrDecls.map (fun d => ConstrDecl.toString d (params.map SIdent.symb))
  let scstrDecls := "(" ++ String.intercalate " " scstrDecls.data ++ ")))"
  pre ++ sparams ++ scstrDecls

instance : ToString Command where
  toString := Command.toString

section

  -- Type of (terms in higher-level logic)
  variable (ω : Type) [BEq ω] [Hashable ω]

  -- The main purpose of this state is for name generation
  --   and symbol declaration/definition, so we do not distinguish
  --   between sort identifiers, datatype identifiers
  --   and function identifiers
  structure State where
    -- Map from high-level construct to symbol
    h2lMap : HashMap ω String    := HashMap.empty
    -- Inverse of `h2lMap`
    -- Map from symbol to high-level construct
    l2hMap : HashMap String ω    := HashMap.empty
    -- State of low-level name generator
    --   To avoid collision with keywords, we only
    --   generate non-annotated identifiers `smti_<idx>`
    idx       : Nat              := 0
    -- List of commands
    commands  : Array Command    := #[]

  abbrev TransM := StateRefT (State ω) MetaM
  
  variable {ω : Type} [BEq ω] [Hashable ω]

  @[always_inline]
  instance : Monad (TransM ω) :=
    let i := inferInstanceAs (Monad (TransM ω));
    { pure := i.pure, bind := i.bind }
  
  instance : Inhabited (TransM ω α) where
    default := fun _ => throw default
  
  def getH2lMap : TransM ω (HashMap ω String) := do
    return (← get).h2lMap

  def getL2hMap : TransM ω (HashMap String ω) := do
    return (← get).l2hMap

  def getCommands : TransM ω (Array Command) := do
    return (← get).commands

  def getIdx : TransM ω Nat := do
    return (← get).idx

  def getMapSize : TransM ω Nat := do
    let size := (← getH2lMap).size
    assert! ((← getL2hMap).size == size)
    return size

  def setH2lMap (m : HashMap ω String) : TransM ω Unit :=
    modify (fun s => {s with h2lMap := m})

  def setL2hMap (m : HashMap String ω) : TransM ω Unit :=
    modify (fun s => {s with l2hMap := m})

  def setCommands (cmds : Array Command) : TransM ω Unit :=
    modify (fun s => {s with commands := cmds})

  def setIdx (m : Nat) : TransM ω Unit :=
    modify (fun s => {s with idx := m})
  
  def hIn (e : ω) : TransM ω Bool := do
    return (← getH2lMap).contains e

  -- Note that this function is idempotent
  partial def h2Symb (cstr : ω) : TransM ω String := do
    let l2hMap ← getL2hMap
    let h2lMap ← getH2lMap
    if h2lMap.contains cstr then
      return h2lMap.find! cstr
    let mut idx ← getIdx
    let mut currName : String := ""
    while true do
      currName := s!"smti_{idx}"
      if !l2hMap.contains currName then
        break
    setL2hMap (l2hMap.insert currName cstr)
    setH2lMap (h2lMap.insert cstr currName)
    setIdx (idx + 1)
    return currName

  def addCommand (c : Command) : TransM ω Unit := do
    let commands ← getCommands
    setCommands (commands.push c)
  
end

end IR.SMT

end Auto