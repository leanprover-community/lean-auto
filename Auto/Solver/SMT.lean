import Lean
import Auto.IR.SMT

open Lean

namespace Auto

open IR.SMT

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

private def emitCommand (p : SolverProc) (c : IR.SMT.Command) := do
  p.stdin.putStr s!"{c}\n"
  p.stdin.flush

private def getSexp (p : SolverProc) : MetaM Sexp := do
  sorry

def createSolver (name : SolverName) : MetaM SolverProc := do
  match name with
  | .z3   => createAux "z3" #["-in", "-smt2"]
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 => throwError "cvc5 is not supported"
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout :=.piped, stderr := .piped,
                      cmd := path, args := args}

end Solver.SMT

end Auto