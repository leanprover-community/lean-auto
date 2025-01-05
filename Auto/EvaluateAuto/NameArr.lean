import Lean
open Lean

namespace EvalAuto

/--
  Whether a name is a valid filename
-/
def Name.canBeFilename (n : Name) : Bool :=
  n.components.all (fun n =>
    match n with
    | .str _ s =>
      match s.get? 0 with
      | .some c => s.all (fun c => c.isAlphanum || c == '_' || c == '\'')
      | .none => false
    | _ => false)

/--
  Unique string representation of array of names
  We use `.` to separate fields of a name, and `\n` to separate names.
  A `.` is appended to the end of each name.
  A `\n` is further appended to the end of the last name.
  We use `\` to escape `.` and `\n` occurring in the fields of names, i.e.,
    `\.` represents literal `.`, `\\n` represents literal `\n`, and
    `\\` represents literal `\`.
  To distinguish `mkStr` and `mkNum`, we prepend `\` to all `mkNum` fields
-/
def NameArray.repr (ns : Array Name) : String :=
  let strRepr (s : String) : String :=
    ((s.replace "\\" "\\\\").replace "." "\\.").replace "\n" "\\\n"
  let compRepr (c : Name) : String :=
    match c with
    | .anonymous => ""
    | .mkNum _ n => s!"\\{n}"
    | .mkStr _ s => strRepr s
  let nameRepr (n : Name) : String :=
    String.join (n.components.map (fun c => compRepr c ++ "."))
  String.join (ns.map (fun n => nameRepr n ++ "\n")).toList

/-
  Parse string representation of array of names
  We use `.` to separate fields of a name, and `\n` to separate names
  We use `\` to escape `.` and `\n` occurring in the fields of names, i.e.,
    `\.` represents literal `.`, `\\n` represents literal `\n`, and
    `\\` represents literal `\`.
  To distinguish `mkStr` and `mkNum`, we prepend `\` to all `mkNum` fields
-/
def NameArray.parse (repr : String) : Array Name := Id.run <| do
  let mut curField := ""
  let mut curFields : Array (String ⊕ Nat) := #[]
  let mut allNames : Array Name := #[]
  let mut escape := false
  let mut num := false
  for c in repr.data do
    if !escape && c == '.' then
      if num then
        curFields := curFields.push (.inr ((String.toNat? curField).getD 0))
      else
        curFields := curFields.push (.inl curField)
      curField := ""
      num := false
      continue
    if !escape && c == '\n' then
      let curName := curFields.foldl (fun prev sn =>
        match sn with
        | .inl s => Name.mkStr prev s
        | .inr n => Name.mkNum prev n) .anonymous
      allNames := allNames.push curName
      curFields := #[]
      continue
    if escape && c.isDigit then
      num := true
    if c == '\\' then
      if escape then
        escape := false
        curField := curField.push c
      else
        escape := true
    else
      escape := false
      curField := curField.push c
  return allNames

def NameArray.save (ns : Array Name) (fname : String) : IO Unit := do
  let fd ← IO.FS.Handle.mk fname .write
  fd.putStr (NameArray.repr ns)

def NameArray.load (fname : String) : IO (Array Name) := do
  let fd ← IO.FS.Handle.mk fname .read
  return NameArray.parse (← fd.readToEnd)

end EvalAuto
