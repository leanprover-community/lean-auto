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
deriving BEq, Hashable, Inhabited

instance : ToString SolverName where
  toString : SolverName → String
  | .zipperposition => "zipperposition"

instance : Lean.KVMap.Value SolverName where
  toDataValue n := toString n
  ofDataValue?
  | "zipperposition" => some .zipperposition
  | _ => none

register_option tptp.solver.name : SolverName := {
  defValue := SolverName.zipperposition
  descr := "Name of the designated TPTP solver"
}

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

def createSolver (name : SolverName) : MetaM SolverProc := do
  match name with
  | .zipperposition => createAux "zipperposition" #["-i=tptp", "--mode=ho-competititve", "-t=10"]
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

def querySolver (query : String) : MetaM Unit := do
  let name := tptp.solver.name.get (← getOptions)
  let solver ← createSolver name
  solver.stdin.putStr s!"{query}\n"
  let (_, solver) ← solver.takeStdin
  let result ← solver.stdout.readToEnd
  trace[auto.tptp.result] "Result: {result}"
  solver.kill

end Solver.TPTP

end Auto