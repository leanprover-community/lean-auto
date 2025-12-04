import Lean

open Lean

namespace EvalAuto

abbrev EvalProc := IO.Process.Child ⟨.piped, .null, .null⟩

abbrev EvalTakenProc := IO.Process.Child ⟨.null, .null, .null⟩

def EvalProc.create (path : String) (args : Array String) : IO EvalProc :=
  IO.Process.spawn {stdin := .piped, stdout := .null, stderr := .null, cmd := path, args := args}

def bashRepr (s : String) :=
  "\"" ++ String.join (s.toList.map go) ++ "\""
where
  go : Char → String
  | '$' => "\\$"
  | '`' => "\\`"
  | '\"' => "\\\""
  | '\\' => "\\\\"
  | c => String.ofList [c]

def runLeanFileUsingNewLeanProcess
  (leanFile : String) (memoryLimitKb : Nat) (timeLimitS : Nat) :
  CoreM EvalTakenProc := do
  let evalProc ← EvalProc.create "bash" #[]
  evalProc.stdin.putStrLn s!"ulimit -v {memoryLimitKb}"
  evalProc.stdin.putStrLn ("echo " ++ bashRepr leanFile ++ s!" | timeout {timeLimitS} lake env lean --stdin")
  let (_, evalProc) ← evalProc.takeStdin
  return evalProc

/--
  This function runs `funName funArgs` on all constants in `names`,
  using a new Lean process

  This should be run importing all the modules associated with constants in
  `names ++ #[funName]`, and should be run with a `cwd`
  where `lake env` creates an environment in which `funName` and all the
  constants in `names` are available
-/
def runFunctionOnConstsUsingNewLeanProcess
  (names : Array Name) (funName : Name) (funArgs : Array String)
  (memoryLimitKb : Nat) (timeLimitS : Nat) : CoreM EvalTakenProc := do
  let imports ← getModuleImports (names ++ #[funName])
  let funStr := funName.toString ++ String.join (funArgs.toList.map (fun arg => " " ++ arg))
  let leanFile := evalFile imports names funStr
  runLeanFileUsingNewLeanProcess leanFile memoryLimitKb timeLimitS
where
  evalFile (imports : Array Name) (names : Array Name) (funStr : String) : String :=
    let importStrs := imports.map (fun n => s!"import {n}")
    let thmsStrs : List String :=
      match names.toList.getLast? with
      | .some last =>
        names.toList.dropLast.map (fun n => s!"  {repr n},") ++ [s!"  {repr last}"]
      | .none => []
    let all := importStrs ++ #[
      "",
      "def thms : Array Lean.Name := #["
    ] ++ thmsStrs ++ #[
      "]"
    ] ++ #[
      "",
      s!"#eval thms.mapM (fun n => {funStr} n)"
    ]
    String.intercalate "\n" all.toList
  getModuleImports (names : Array Name) : CoreM (Array Name) := do
    let mut ret : Std.HashSet Name := {}
    for name in names do
      let .some modName ← findModuleOf? name
        | throwError "{decl_name%} :: Cannot find the module that defines {name}"
      ret := ret.insert modName
    return ret.toArray

end EvalAuto
