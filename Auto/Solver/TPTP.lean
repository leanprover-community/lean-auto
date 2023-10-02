import Lean
import Auto.IR.TPTP_TH0
open Lean

initialize
  registerTraceClass `auto.tptp.printQuery
  registerTraceClass `auto.tptp.result

namespace Auto

namespace Solver.TPTP

inductive SolverName where
  | zipperposition
  -- zipperposition + E theorem prover, portfolio
  | zeport
deriving BEq, Hashable, Inhabited

instance : ToString SolverName where
  toString : SolverName → String
  | .zipperposition => "zipperposition"
  | .zeport => "zeport"

instance : Lean.KVMap.Value SolverName where
  toDataValue n := toString n
  ofDataValue?
  | "zipperposition" => some .zipperposition
  | "zeport" => some .zeport
  | _ => none

register_option tptp.solver.name : SolverName := {
  defValue := SolverName.zipperposition
  descr := "Name of the designated TPTP solver"
}

register_option tptp.zeport.path : String := {
  defValue := "zeport"
  descr := "Path to the zipperposition-E portfolio"
}

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

private def createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

def queryZipperposition (query : String) : MetaM Unit := do
  let solver ← createAux "zipperposition" #["-i=tptp", "--mode=ho-competitive", "-t=10"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let result ← solver.stdout.readToEnd
  trace[auto.tptp.result] "Result: {result}"
  solver.kill

def queryZEPort (query : String) : MetaM Unit := do
  let path := tptp.zeport.path.get (← getOptions)
  -- To avoid concurrency issue, use `attempt`
  attempt <| IO.FS.createDir "./.zeport_ignore"
  let mut idx := 0
  -- Synchronization
  while true do
    try
      IO.FS.createDir s!"./.zeport_ignore/tmp{idx}"
      break
    catch e =>
      let estr := toString (← (Exception.toMessageData e).format)
      if estr.extract ⟨0⟩ ⟨44⟩ != "already exists (error code: 17, file exists)" then
        throwError "queryZEPort :: Unexpected error"
      idx := idx + (← IO.rand 0 100)
  IO.FS.withFile s!"./.zeport_ignore/problem{idx}.p" .writeNew (fun stream =>
    stream.putStr query)
  let solver ← createAux "python3" #[path, s!"./.zeport_ignore/problem{idx}.p", "10", s!"./.zeport_ignore/tmp{idx}"]
  let stderr ← solver.stderr.readToEnd
  let stdout ← solver.stdout.readToEnd
  trace[auto.tptp.result] "Result: \nstderr: {stderr}\nstdout: {stdout}"
  solver.kill
  IO.FS.removeFile s!"./.zeport_ignore/problem{idx}.p"
  -- For synchronization, remove directory in the end
  IO.FS.removeDir s!"./.zeport_ignore/tmp{idx}"
where attempt (action : MetaM Unit) := try action catch _ => pure ()

def querySolver (query : String) : MetaM Unit := do
  match tptp.solver.name.get (← getOptions) with
  | .zipperposition => queryZipperposition query
  | .zeport => queryZEPort query

end Solver.TPTP

end Auto