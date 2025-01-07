import Lean
import Auto.IR.TPTP_TH0
import Auto.Parser.TPTP
import Auto.Embedding.LamBase
open Lean

initialize
  registerTraceClass `auto.tptp.result
  registerTraceClass `auto.tptp.printQuery
  registerTraceClass `auto.tptp.printProof
  registerTraceClass `auto.tptp.premiseSelection

register_option auto.tptp : Bool := {
  defValue := false
  descr := "Enable/Disable TPTP"
}

register_option auto.tptp.trust : Bool := {
  defValue := false
  descr :=
    "When this option is set to `true`, auto closes the " ++
    "goal by `autoTPTPSorry` if TPTP solver proves the problem"
}

axiom autoTPTPSorry.{u} (α : Sort u) : α

register_option auto.tptp.premiseSelection : Bool := {
  defValue := true
  descr := "Enable/Disable premise selection by TPTP solvers"
}

register_option auto.tptp.timeout : Nat := {
  defValue := 10
  descr := "Time limit for TPTP solvers (seconds)"
}

namespace Auto

open Parser.TPTP

namespace Solver.TPTP

inductive ZEPortType where
  | fo
  | lams
deriving BEq, Hashable, Inhabited, Repr

inductive SolverName where
  -- Disable TPTP prover
  | zipperposition
  -- zipperposition + E theorem prover, portfolio
  | zeport (zept : ZEPortType)
  -- E prover, higher-order version
  | eproverHo
  | vampire
deriving BEq, Hashable, Inhabited, Repr

instance : ToString SolverName where
  toString : SolverName → String
  | .zipperposition => "zipperposition"
  | .zeport zept =>
    match zept with
    | .fo => "zeport-fo"
    | .lams => "zeport-lams"
  | .eproverHo => "eprover-ho"
  | .vampire => "vampire"

instance : Lean.KVMap.Value SolverName where
  toDataValue n := toString n
  ofDataValue?
  | "zipperposition" => some .zipperposition
  | "zeport-fo" => some (.zeport .fo)
  | "zeport-lams" => some (.zeport .lams)
  | "eprover-ho" => some .eproverHo
  | "vampire" => some .vampire
  | _ => none

end Auto.Solver.TPTP

open Auto.Solver.TPTP in
register_option auto.tptp.solver.name : SolverName := {
  defValue := SolverName.zipperposition
  descr := "Name of the designated TPTP solver"
}

register_option auto.tptp.zipperposition.path : String := {
  defValue := "zipperposition"
  descr := "Path to zipperposition, defaults to \"zipperposition\""
}

register_option auto.tptp.zeport.path : String := {
  defValue := "zeport"
  descr := "Path to the zipperposition-E portfolio"
}

register_option auto.tptp.eproverHo.path : String := {
  defValue := "eprover-ho"
  descr := "Path to higher-order version of E theorem prover"
}

register_option auto.tptp.vampire.path : String := {
  defValue := "vampire"
  descr := "Path to vampire prover"
}

namespace Auto.Solver.TPTP

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

private def createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

def queryZipperposition (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.zipperposition.path.get (← getOptions)
  let tlim := auto.tptp.timeout.get (← getOptions)
  let solver ← createAux path #["-i=tptp", "-o=tptp", "--mode=ho-competitive", s!"-t={tlim}"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  let proven := (stdout.splitOn "SZS status Unsatisfiable").length >= 2
  return (proven, stdout)

def queryZEPort (zept : ZEPortType) (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.zeport.path.get (← getOptions)
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
        throwError "{decl_name%} :: Unexpected error"
      idx := idx + (← IO.rand 0 100)
  IO.FS.withFile s!"./.zeport_ignore/problem{idx}.p" .writeNew (fun stream => stream.putStr query)
  let solver ← createSolver path idx
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  IO.FS.removeFile s!"./.zeport_ignore/problem{idx}.p"
  -- For synchronization, remove directory in the end
  IO.FS.removeDirAll s!"./.zeport_ignore/tmp{idx}"
  let proven := (stdout.splitOn "SZS status Unsatisfiable").length >= 2
  return (proven, stdout)
where
  attempt (action : MetaM Unit) : MetaM Unit := try action catch _ => pure ()
  createSolver (path : String) (idx : Nat) := do
    let path := if ("A" ++ path).back == '/' then path else path ++ "/"
    let tlim := auto.tptp.timeout.get (← getOptions)
    match zept with
    | .fo => createAux "python3" #[path ++ "portfolio.fo.parallel.py", s!"./.zeport_ignore/problem{idx}.p", s!"{tlim}", "true"]
    | .lams => createAux "python3" #[path ++ "portfolio.lams.parallel.py", s!"./.zeport_ignore/problem{idx}.p", s!"{tlim}", s!"./.zeport_ignore/tmp{idx}", "true"]

def queryE (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.eproverHo.path.get (← getOptions)
  let tlim := auto.tptp.timeout.get (← getOptions)
  let solver ← createAux path #["--tstp-format", s!"--cpu-limit={tlim}"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  let proven := (stdout.splitOn "Proof found!").length >= 2
  return (proven, stdout)

def queryVampire (query : String) : MetaM (Bool × String) := do
  let path := auto.tptp.vampire.path.get (← getOptions)
  let tlim := auto.tptp.timeout.get (← getOptions)
  let solver ← createAux path #["--mode", "casc", "--time_limit", s!"{tlim}"]
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  trace[auto.tptp.result] "Result: \nstderr:\n{stderr}\nstdout:\n{stdout}"
  solver.kill
  let proven := (stdout.splitOn "Refutation found. Thanks to Tanya!").length >= 2
  return (proven, stdout)

def querySolver (query : String) : MetaM (Bool × Array Parser.TPTP.Command) := do
  if !(auto.tptp.get (← getOptions)) then
    throwError "{decl_name%} :: Unexpected error"
  let (proven, stdout) ← (do
    match auto.tptp.solver.name.get (← getOptions) with
    | .zipperposition => queryZipperposition query
    | .zeport zept    => queryZEPort zept query
    | .eproverHo      => queryE query
    | .vampire        => queryVampire query)
  return (proven, ← Parser.TPTP.parse stdout)

end Solver.TPTP

end Auto
