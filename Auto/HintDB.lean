import Lean
open Lean

namespace Auto

/--
  Hint database is a collection of lemmas that users
    can supply to a tactic. Users only need to provide
    the name of the hint database to the tactic.
  Each hint database has a name, which is internally stored as a string.
  User can add a lemma to a hint database (internally, .addLemma),
    or combine several existing hint databases to form a larger
    hint database (internally, .compose), or both.
    Note that .compose is dynamic.
-/
inductive HintDB where
  | empty     : HintDB
  | addLemma  : (lem : Name) → (hintdb : HintDB) → HintDB
  | compose     : (hintdbs : Array String) → HintDB
deriving BEq, Hashable, Inhabited, Repr

abbrev HintDBExtension :=
  SimplePersistentEnvExtension (String × HintDB) (HashMap String HintDB)

initialize hintDBExt : HintDBExtension ← registerSimplePersistentEnvExtension {
  name          := `HintDBExt
  addImportedFn := fun _ => {},
  addEntryFn    := fun s n => s.insert n.1 n.2
}

partial def HintDB.toHashSet : HintDB → AttrM (HashSet Name)
| .empty => pure HashSet.empty
| .addLemma lem hdb => do
    let hset ← hdb.toHashSet
    return hset.insert lem
| .compose hdbs => do
    let state := hintDBExt.getState (← getEnv)
    let mut ret := HashSet.empty
    for hdb in hdbs do
      let some hdb := state.find? hdb
        | throwError "HintDB.toHashSet :: Unknown hint database {hdb}"
      let hset ← hdb.toHashSet
      ret := ret.insertMany hset
    return ret 

private def throwUnregisteredHintDB (dbname action : String) : AttrM Unit := do
  let cmdstr := "#declare_hintdb " ++ dbname
  throwError ("Please declare hint database using " ++
    s!"command {repr cmdstr} before " ++ action ++ " it")

def registerHintDB : IO Unit :=
  registerBuiltinAttribute {
    name  := `hintdb
    descr := "Use this attribute to register lemmas to hint databases"
    applicationTime := .afterTypeChecking
    add   := fun decl stx _ => do
      let dbname := (← Attribute.Builtin.getIdent stx).getId.toString
      let state := hintDBExt.getState (← getEnv)
      if let some db := state.find? dbname then
        let state' := state.insert dbname (.addLemma decl db)
        modifyEnv fun env => hintDBExt.modifyState env fun _ => state'
      else
        throwUnregisteredHintDB dbname "adding lemma to"
    erase := fun _ => do
      throwError "Lemmas cannot be erased from hint database"
  }

initialize registerHintDB

open Elab Command

syntax (name := declarehintdb) "#declare_hintdb" ident : command
syntax (name := printhintdb) "#print_hintdb" ident : command
syntax (name := composehintdb) "#compose_hintdb" ident "[" ident,* "]" : command

@[command_elab declarehintdb]
def elabdeclarehintdb : CommandElab := fun stx => do
  match stx with
  | `(declarehintdb | #declare_hintdb $dbname) =>
    let dbname := dbname.getId.toString
    let state := hintDBExt.getState (← getEnv)
    if let some db := state.find? dbname then
      throwError "Hint database {repr db} has already been declared"
    else
      let state' := state.insert dbname .empty
      modifyEnv fun env => hintDBExt.modifyState env fun _ => state'
  | _ => throwUnsupportedSyntax

@[command_elab printhintdb]
def elabprinthintdb : CommandElab := fun stx => do
  match stx with
  | `(printhintdb | #print_hintdb $dbname) =>
    let dbname := dbname.getId.toString
    let state := hintDBExt.getState (← getEnv)
    if let some db := state.find? dbname then
      let hset ← liftCoreM (db.toHashSet)
      logInfoAt stx m!"{hset.toList}"
    else
      liftCoreM <| throwUnregisteredHintDB dbname "printing"
  | _ => throwUnsupportedSyntax

@[command_elab composehintdb]
def elabcomposehintdb : CommandElab := fun stx => do
  match stx with
  | `(composehintdb | #compose_hintdb $db [$[$dbs],*]) =>
    let db := db.getId.toString
    let dbs := dbs.map (fun x => x.getId.toString)
    let state := hintDBExt.getState (← getEnv)
    for db in dbs do
      if !state.contains db then
        throwError "Unknown hint database {repr db}"
    if let some db := state.find? db then
      throwError "Hint database {repr db} has already been declared"
    else
      let state' := state.insert db (.compose dbs)
      modifyEnv fun env => hintDBExt.modifyState env fun _ => state'
  | _ => throwUnsupportedSyntax

end Auto