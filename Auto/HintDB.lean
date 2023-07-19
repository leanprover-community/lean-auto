import Lean
open Lean

namespace Auto

-- Hint database is a collection of lemmas that users
--   can supply to a tactic. Users only need to provide
--   the name of the hint database to the tactic.
-- Each hint database has a name, which is internally stored as a string.
-- User can add a lemma to a hint database (internally, .addLemma),
--   or combine several existing hint databases to form a larger
--   hint database (internally, .union), or both.
--   Note that .union is dynamic.
inductive HintDB where
  | empty     : HintDB
  | addLemma  : (lem : Name) → (hintdb : HintDB) → HintDB
  | union     : (hintdb₁ : String) → (hintdb₂ : String) → HintDB
  | minus     : (minuend : String) → (subtrahend : String) → HintDB
deriving BEq, Hashable, Inhabited, Repr

abbrev HintDBExtension :=
  SimplePersistentEnvExtension (String × HintDB) (HashMap String HintDB)

initialize hintDBExt : HintDBExtension ← registerSimplePersistentEnvExtension {
  name          := `HintDBExt
  addImportedFn := fun _ => {},
  addEntryFn    := fun s n => s.insert n.1 n.2
}

def registerHintDB : IO Unit :=
  registerBuiltinAttribute {
    name  := `hintDB
    descr := "Use this attribute to register lemmas to hint databases"
    applicationTime := .afterTypeChecking
    add   := fun decl stx _ => do
      let dbname := (← Attribute.Builtin.getIdent stx).getId.toString
      let state := hintDBExt.getState (← getEnv)
      if let some db := state.find? dbname then
        let state' := state.insert dbname (.addLemma decl db)
        modifyEnv fun env => hintDBExt.modifyState env fun _ => state'
      else
        throwError "Please declare hint database {dbname} before adding lemma to it"
  }

initialize registerHintDB

open Elab Command

syntax (name := printHintDB) "#printHintDB" ident : command
syntax (name := appendToHintDB) "#appendToHintDB" ident "+=" ident : command
syntax (name := composeHintDB) "#composeHintDB" ident ":=" "[" ident,* "]" : command

@[command_elab printHintDB]
def elabPrintHintDB : CommandElab := fun stx => do
  match stx with
  | `(printHintDB | #printHintDB $dbnam) => sorry
  | _ => sorry

@[command_elab appendToHintDB]
def elabAppendToHintDB : CommandElab := fun stx => do
  match stx with
  | `(appendToHintDB | #appendToHintDB $to += $fr) => sorry
  | _ => sorry

@[command_elab composeHintDB]
def elabComposeHintDB : CommandElab := fun stx => do
  match stx with
  | `(composeHintDB | #composeHintDB $db := [$[$dbs],*]) => sorry
  | _ => sorry

end Auto