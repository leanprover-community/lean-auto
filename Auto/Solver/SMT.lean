import Lean
import Auto.IR.SMT
import Auto.Parser.SMTSexp
open Lean

initialize
  registerTraceClass `auto.smt.printCommands
  registerTraceClass `auto.smt.result

register_option auto.smt : Bool := {
  defValue := false
  descr := "Enable/Disable SMT Solver"
}

register_option auto.smt.trust : Bool := {
  defValue := false
  descr := "When this option is set to `true`, auto closes the " ++
    "goal by `sorry` if SMT solver returns `unsat`."
}

namespace Auto

open IR.SMT
open Parser.SMTSexp

namespace Solver.SMT

inductive SolverName where
  | z3
  | cvc4
  | cvc5
deriving BEq, Hashable, Inhabited

instance : ToString SolverName where
  toString : SolverName → String
  | .z3   => "z3"
  | .cvc4 => "cvc4"
  | .cvc5 => "cvc5"

instance : Lean.KVMap.Value SolverName where
  toDataValue n := toString n
  ofDataValue?
  | "z3"   => some .z3
  | "cvc4" => some .cvc4
  | "cvc5" => some .cvc5
  | _      => none

register_option auto.smt.solver.name : SolverName := {
  defValue := SolverName.z3
  descr := "Name of the designated SMT solver"
}

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

private def emitCommand (p : SolverProc) (c : IR.SMT.Command) : IO Unit := do
  p.stdin.putStr s!"{c}\n"
  p.stdin.flush

private def emitCommands (p : SolverProc) (c : Array IR.SMT.Command) : IO Unit := do
  let _ ← c.mapM (emitCommand p)

private def getSexp (s : String) : MetaM (Sexp × String) :=
  match parseSexp s ⟨0⟩ {} with
  | .complete se p => return (se, Substring.toString ⟨s, p, s.endPos⟩)
  | .incomplete _ _ => throwError s!"getSexp :: Incomplete input {s}"
  | .malformed => throwError s!"getSexp :: Malformed (prefix of) input {s}"

def createSolver (name : SolverName) : MetaM SolverProc := do
  match name with
  | .z3   => createAux "z3" #["-in", "-smt2", "-T:10"]
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 => createAux "cvc5" #["--tlimit=10000", "--produce-models"]
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

axiom autoSMTSorry.{u} (α : Sort u) : α

/-- Only put declarations in the query -/
def querySolver (query : Array IR.SMT.Command) : MetaM (Option Sexp) := do
  if !(auto.smt.get (← getOptions)) then
    throwError "querySolver :: Unexpected error"
  let name := auto.smt.solver.name.get (← getOptions)
  let solver ← createSolver name
  emitCommand solver (.setOption (.produceProofs true))
  emitCommand solver (.setOption (.produceUnsatCores true))
  emitCommands solver query
  emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  let (checkSatResponse, _) ← getSexp stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    let (model, _) ← getSexp stdout
    solver.kill
    trace[auto.smt.result] "{name} says Sat, model:\n{model}\nstderr:\n{stderr}"
    return .none
  | .atom (.symb "unsat") =>
    emitCommand solver .getUnsatCore
    emitCommand solver .getProof
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    let (unsatCore, stdout) ← getSexp stdout
    let (proof, _) ← getSexp stdout
    solver.kill
    trace[auto.smt.result] "{name} says Unsat, unsat core\n {unsatCore}\n:proof:\n {proof}\nstderr:\n{stderr}"
    return .some proof
  | _ =>
    trace[auto.smt.result] "{name} produces unexpected check-sat response\n {checkSatResponse}"
    return .none

end Solver.SMT

end Auto
