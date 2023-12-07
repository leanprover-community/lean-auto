import Lean
open Lean

namespace Auto

/--
  Lemma database is a collection of lemmas that users
    can supply to a tactic. Users only need to provide
    the name of the lemma database to the tactic.
  Each lemma database has a name, which is internally stored as a string.
  User can add a lemma to a lemma database (internally, .addLemma),
    or combine several existing lemma databases to form a larger
    lemma database (internally, .compose), or both.
    Note that .compose is dynamic.
-/
inductive LemDB where
  | empty     : LemDB
  | addLemma  : (lem : Name) → (lemdb : LemDB) → LemDB
  | compose   : (lemdbs : Array String) → LemDB
deriving BEq, Hashable, Inhabited, Repr

abbrev LemDBExtension :=
  SimplePersistentEnvExtension (String × LemDB) (HashMap String LemDB)

initialize lemDBExt : LemDBExtension ← registerSimplePersistentEnvExtension {
  name          := `LemDBExt
  addImportedFn := fun _ => {},
  addEntryFn    := fun s n => s.insert n.1 n.2
}

partial def LemDB.toHashSet : LemDB → AttrM (HashSet Name)
| .empty => pure HashSet.empty
| .addLemma lem hdb => do
    let hset ← hdb.toHashSet
    return hset.insert lem
| .compose hdbs => do
    let state := lemDBExt.getState (← getEnv)
    let mut ret := HashSet.empty
    for hdb in hdbs do
      let some hdb := state.find? hdb
        | throwError "LemDB.toHashSet :: Unknown lemma database {hdb}"
      let hset ← hdb.toHashSet
      ret := ret.insertMany hset
    return ret

private def throwUnregisteredLemDB (dbname action : String) : AttrM α := do
  let cmdstr := "#declare_lemdb " ++ dbname
  throwError ("Please declare lemma database using " ++
    s!"command {repr cmdstr} before {action}")

def registerLemDB : IO Unit :=
  registerBuiltinAttribute {
    name  := `lemdb
    descr := "Use this attribute to register lemmas to lemma databases"
    applicationTime := .afterTypeChecking
    add   := fun decl stx _ => do
      let dbname := (← Attribute.Builtin.getIdent stx).getId.toString
      let state := lemDBExt.getState (← getEnv)
      if let some db := state.find? dbname then
        let state' := state.insert dbname (.addLemma decl db)
        modifyEnv fun env => lemDBExt.modifyState env fun _ => state'
      else
        throwUnregisteredLemDB dbname "adding lemma to it"
    erase := fun _ => do
      throwError "Lemmas cannot be erased from lemma database"
  }

def findLemDB (dbname : Name) : CoreM (Option LemDB) := do
  let dbname := dbname.toString
  let state := lemDBExt.getState (← getEnv)
  if let some db := state.find? dbname then
    return .some db
  else
    return .none

initialize registerLemDB

open Elab Command

syntax (name := declarelemdb) "#declare_lemdb" ident : command
syntax (name := printlemdb) "#print_lemdb" ident : command
syntax (name := composelemdb) "#compose_lemdb" ident "[" ident,* "]" : command

@[command_elab declarelemdb]
def elabdeclarelemdb : CommandElab := fun stx => do
  match stx with
  | `(declarelemdb | #declare_lemdb $dbname) =>
    let dbname := dbname.getId.toString
    let state := lemDBExt.getState (← getEnv)
    if let some db := state.find? dbname then
      throwError "Lemma database {repr db} has already been declared"
    else
      let state' := state.insert dbname .empty
      modifyEnv fun env => lemDBExt.modifyState env fun _ => state'
  | _ => throwUnsupportedSyntax

@[command_elab printlemdb]
def elabprintlemdb : CommandElab := fun stx => do
  match stx with
  | `(printlemdb | #print_lemdb $dbname) =>
    let .some db ← liftCoreM <| findLemDB dbname.getId
      | liftCoreM <| throwUnregisteredLemDB dbname.getId.toString "printing it"
    let hset ← liftCoreM (db.toHashSet)
    logInfoAt stx m!"{hset.toList}"
  | _ => throwUnsupportedSyntax

@[command_elab composelemdb]
def elabcomposelemdb : CommandElab := fun stx => do
  match stx with
  | `(composelemdb | #compose_lemdb $db [$[$dbs],*]) =>
    let db := db.getId.toString
    let dbs := dbs.map (fun x => x.getId.toString)
    let state := lemDBExt.getState (← getEnv)
    for db in dbs do
      if !state.contains db then
        throwError "Unknown lemma database {repr db}"
    if let some db := state.find? db then
      throwError "Lemma database {repr db} has already been declared"
    else
      let state' := state.insert db (.compose dbs)
      modifyEnv fun env => lemDBExt.modifyState env fun _ => state'
  | _ => throwUnsupportedSyntax

end Auto
