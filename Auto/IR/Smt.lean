import Lean
open Lean

-- smt-lib 2

namespace Auto

namespace IR.Smt

-- <index>      ::= <numeral> | <symbol>
-- <identifier> ::= <symbol> | (_ <symbol> <index>+)

inductive SIdent where
  | symb    : String → SIdent
  | indexed : String → (String ⊕ Nat) → SIdent

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

def SSort.toString : SSort → List SIdent → String
| .bvar i, binders =>
  if h : i < binders.length then
    s!"{binders[i]}"
  else
    panic!"SSort.toString :: Loose bound variable"
| .app i ⟨[]⟩, _ => s!"{i}"
| .app i ⟨a :: as⟩, binders =>
  let intro := s!"({i} "
  let head := SSort.toString a binders ++ " "
  let tail := String.intercalate " " (go as binders)
  intro ++ head ++ tail ++ ")"
where go : List SSort → List SIdent →  List String 
| [], _ => []
| a :: as, binders => SSort.toString a binders :: go as binders

-- Caution : Do not use this in define-sort, because sort
--   there might contain bvars
instance : ToString SSort where
  toString s := SSort.toString s []

-- 〈qual_identifier〉 ::= 〈identifier〉 | ( as 〈identifier〉 〈sort〉 )
inductive QualIdent where
  | ident   : SIdent → QualIdent
  | qualed  : SIdent → SSort → QualIdent

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
  | qId     : QualIdent → STerm                -- Function symbol
  | qIdApp  : QualIdent → Array STerm → STerm  -- Application of function symbol to array of terms
  | letE    : (name : String) → (binding : STerm) → (body : STerm) → STerm
  | forallE : (name : String) → (binderType : SSort) → (body : STerm) → STerm
  | existsE : (name : String) → (binderType : SSort) → (body : STerm) → STerm
  | matchE  : (matchTerm : STerm) → Array (MatchCase STerm) → STerm

def STerm.toString : STerm → List SIdent → String
  | .sConst, _         => panic!"STerm.toString :: Unimplemented"
  | .bvar i, binders   =>
    if let some si := binders.get? i then
      ToString.toString si
    else
      panic!"STerm.toString :: Loose bound variable"
  | .qId si, _          => ToString.toString si
  | .qIdApp si ⟨[]⟩, _   => ToString.toString si
  | .qIdApp si ⟨a :: as⟩, binders =>
    let intro := s!"({si} "
    let tail := String.intercalate " " (STerm.toString a binders :: goQIdApp as binders)
    intro ++ tail ++ ")"
  | .letE name binding body, binders =>
    let binders := (SIdent.symb name) :: binders
    let intro := s!"(let ({SIdent.symb name} "
    let binding := STerm.toString binding binders ++ ") "
    let body := STerm.toString body binders ++ ")"
    intro ++ binding ++ body
  | .forallE name binderType body, binders =>
    let binders := (SIdent.symb name) :: binders
    let intro := s!"(forall ({SIdent.symb name} "
    let binderType := ToString.toString binderType ++ ") "
    let body := STerm.toString body binders ++ ")"
    intro ++ binderType ++ body
  | .existsE name binderType body, binders =>
    let binders := (SIdent.symb name) :: binders
    let intro := s!"(exists ({SIdent.symb name} "
    let binderType := ToString.toString binderType ++ ") "
    let body := STerm.toString body binders ++ ")"
    intro ++ binderType ++ body
  | .matchE _ ⟨[]⟩, _ => panic!"STerm.toString :: Zero match branches"
  | .matchE matchTerm ⟨a :: as⟩, binders =>
    let intro := s!"(match " ++ STerm.toString matchTerm binders ++ " ("
    let intro := intro ++ goMatchBranch a binders
    let body := String.join ((goMatchBody as binders).map (fun s => " " ++ s)) ++ "))"
    intro ++ body
where
  goQIdApp : List STerm → List SIdent → List String
    | [], _ => []
    | a :: as, binders => STerm.toString a binders :: goQIdApp as binders
  goMatchBranch : MatchCase STerm → List SIdent → String
    | ⟨constr, args, body⟩, binders =>
      if args.size == 0 then
        let body := " " ++ STerm.toString body binders ++ ")"
        let pattern := "(" ++ (ToString.toString (SIdent.symb constr))
        pattern ++ body
      else
        let binders := args.data.map .symb ++ binders
        let body := " " ++ STerm.toString body binders ++ ")"
        let args := args.data.map (fun x => ToString.toString (SIdent.symb x))
        let pattern := "((" ++ String.intercalate " " (ToString.toString (SIdent.symb constr) :: args) ++ ")"
        pattern ++ body
  goMatchBody : List (MatchCase STerm) → List SIdent → List String
    | [], _ => []
    | a :: as, binders => goMatchBranch a binders :: goMatchBody as binders

instance : ToString STerm where
  toString s := STerm.toString s []

--〈selector_dec〉 ::= ( 〈symbol〉 〈sort〉 )
--〈constructor_dec〉 ::= ( 〈symbol〉 〈selector_dec〉∗ )
structure ConstrDecl where
  name     : String
  selDecls : Array (String × SSort)

private def ConstrDecl.toString : ConstrDecl → List SIdent → String
| ⟨name, selDecls⟩, binders =>
  let pre := s!"({SIdent.symb name}"
  let selDecls := selDecls.map (fun (name, sort) => s!"({SIdent.symb name}" ++ SSort.toString sort binders ++ ")")
  String.intercalate " " (pre :: selDecls.data) ++ ")"

--〈sorted_var〉   ::= ( 〈symbol〉 〈sort〉 )
--〈datatype_dec〉 ::= ( 〈constructor_dec〉+ ) | ( par ( 〈symbol〉+ ) ( 〈constructor_dec〉+ ) )
--〈function_dec〉 ::= ( 〈symbol〉 ( 〈sorted_var〉∗ ) 〈sort〉 )
--〈function_def〉 ::= 〈symbol〉 ( 〈sorted_var〉∗ ) 〈sort〉 〈term〉
-- command   ::= ( assert 〈term〉 )
--               ...
--               ( declare-fun 〈symbol〉 ( 〈sort〉∗ ) 〈sort〉 )
--               ( declare-sort 〈symbol〉 〈numeral〉 )
--               ( define-fun 〈function_def〉 )
--               ( define-fun-rec 〈function_def〉 )
--               ( define-sort 〈symbol〉 ( 〈symbol〉∗ ) 〈sort〉 )
--               ( declare-datatype 〈symbol〉 〈datatype_dec〉)
--               ...
inductive Decl where
  | declFun   : (name : String) → (argSorts : Array SSort) → (resSort : SSort) → Decl
  | declSort  : (name : String) → (arity : Nat) → Decl
  | defFun    : (isRec : Bool) → (name : String) → (args : Array (String × SSort)) →
                  (resTy : SSort) → (body : STerm) → Decl
  | defSort   : (name : String) → (args : Array String) → (body : SSort) → Decl
  | declDtype : (name : String) → (params : Array String) → (cstrDecls : Array ConstrDecl) → Decl

def Decl.toString : Decl → String
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
  let trail := s!"{resTy} " ++ STerm.toString body (args.map (fun (name, _) => SIdent.symb name)).data ++ ")"
  pre ++ binders ++ trail
| .defSort name args body              =>
  let pre := s!"(define-sort {SIdent.symb name} ("
  let sargs := String.intercalate " " args.data ++ ") "
  let trail := SSort.toString body (args.data.map SIdent.symb) ++ ")"
  pre ++ sargs ++ trail
| .declDtype name params cstrDecls     =>
  let pre := s!"(decare-datatype {SIdent.symb name} ("
  let sparams :=
    if params.size == 0 then ""
    else "par ("  ++ String.intercalate " " params.data ++ ") "
  let scstrDecls := cstrDecls.map (fun d => ConstrDecl.toString d (params.data.map SIdent.symb))
  let scstrDecls := "(" ++ String.intercalate " " scstrDecls.data ++ ")))"
  pre ++ sparams ++ scstrDecls

end IR.Smt

end Auto