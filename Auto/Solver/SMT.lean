import Lean
import Auto.IR.SMT
import Auto.Parser.SMTSexp
open Lean

initialize
  registerTraceClass `auto.smt.printCommands
  registerTraceClass `auto.smt.result

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

register_option smt.solver.name : SolverName := {
  defValue := SolverName.z3
  descr := "Name of the designated SMT solver"
}

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

private def emitCommand (p : SolverProc) (c : IR.SMT.Command) : IO Unit := do
  p.stdin.putStr s!"{c}\n"
  p.stdin.flush

private def emitCommands (p : SolverProc) (c : Array IR.SMT.Command) : IO Unit := do
  let _ ← c.mapM (emitCommand p)

private def getSexp (sp : SolverProc) : MetaM Sexp := do
  let mut s ← sp.stdout.getLine
  let mut partialRes : PartialResult := {}
  while true do
    match parseSexp s ⟨0⟩ partialRes with
    | .complete se p =>
      if p != s.endPos then
        let redundant := Substring.toString ⟨s, p, s.endPos⟩
        if redundant.toList.any (fun c => !Lexer.SMTSexp.whitespace.contains c) then
          IO.println s!"getSexp :: Warning, redundant input {repr redundant}"
      return se
    | .incomplete pr p =>
      let remain := Substring.toString ⟨s, p, s.endPos⟩
      let new ← sp.stdout.getLine
      s := remain ++ "\n" ++ new
      partialRes := pr
    | .malformed =>
      throwError s!"getSexp :: Malformed (prefix of) input {s}"
  throwError "getSexp :: Unexpected error"

def createSolver (name : SolverName) : MetaM SolverProc := do
  match name with
  | .z3   => createAux "z3" #["-in", "-smt2", "-T:10"]
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 => createAux "cvc5" #["--tlimit=10000"]
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

-- Only put declarations in the query
def querySolver (query : Array IR.SMT.Command) : MetaM Unit := do
  let name := smt.solver.name.get (← getOptions)
  let solver ← createSolver name
  emitCommand solver (.setOption (.produceProofs true))
  emitCommands solver query
  emitCommand solver .checkSat
  let checkSatResponse ← getSexp solver
  match checkSatResponse with
  | .atom (.symb "sat") =>
    emitCommand solver .getModel
    let model ← getSexp solver
    solver.kill
    trace[auto.smt.result] "{name} says Sat, model:\n {model}"
  | .atom (.symb "unsat") =>
    emitCommand solver .getProof
    let proof ← getSexp solver
    solver.kill
    trace[auto.smt.result] "{name} says Unsat, proof:\n {proof}"
  | _ => trace[auto.smt.result] "{name} produces unexpected check-sat response\n {checkSatResponse}"

end Solver.SMT

end Auto