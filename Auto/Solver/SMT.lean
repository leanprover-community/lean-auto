import Lean
import Auto.IR.SMT
import Auto.Parser.SMTParser
open Lean

initialize
  registerTraceClass `auto.smt.printCommands
  registerTraceClass `auto.smt.result
  registerTraceClass `auto.smt.proof
  registerTraceClass `auto.smt.model
  registerTraceClass `auto.smt.stderr
  registerTraceClass `auto.smt.printValuation
  registerTraceClass `auto.smt.unsatCore.smtTerms
  registerTraceClass `auto.smt.unsatCore.leanExprs
  registerTraceClass `auto.smt.unsatCore.deriv

register_option auto.smt : Bool := {
  defValue := false
  descr := "Enable/Disable SMT"
}

register_option auto.smt.trust : Bool := {
  defValue := false
  descr :=
    "When this option is set to `true`, auto closes the " ++
    "goal by `autoSMTSorry` if SMT solver returns `unsat`"
}

axiom autoSMTSorry.{u} (α : Sort u) : α

register_option auto.smt.timeout : Nat := {
  defValue := 10
  descr := "Time limit for smt solvers (seconds)"
}

def auto.smt.save.doc : String :=
  "To save smt commands to a file, set `auto.smt.savepath` to the output path" ++
  ", and set `auto.smt.save` to `true`. To skip querying solvers, " ++
  "set `auto.smt.solver.name` to `none`."

register_option auto.smt.save : Bool := {
  defValue := false
  descr := auto.smt.save.doc
}

register_option auto.smt.savepath : String := {
  defValue := ""
  descr := auto.smt.save.doc
}

register_option auto.smt.rconsProof : Bool := {
  defValue := false
  descr := "Enable/Disable proof reconstruction"
}

register_option auto.smt.dumpHints : Bool := {
  defValue := false
  descr := "Enable/Disable dumping cvc5 hints (experimental)"
}

register_option auto.smt.sygus_inst : Bool := {
  defValue := false
  descr := "Enable/Diable the --sygus-inst flag when calling cvc5"
}

register_option auto.smt.dumpHints.limitedRws : Bool := {
  defValue := true
  descr := "Only dump rewrites from quantifier instantiations as hints (experimental)"
}

namespace Auto

namespace Solver.SMT

inductive SolverName where
  | none
  | z3
  | cvc4
  | cvc5
deriving BEq, Hashable, Inhabited, Repr

instance : ToString SolverName where
  toString : SolverName → String
  | .none => "none"
  | .z3   => "z3"
  | .cvc4 => "cvc4"
  | .cvc5 => "cvc5"

instance : Lean.KVMap.Value SolverName where
  toDataValue n := toString n
  ofDataValue?
  | "none" => some .none
  | "z3"   => some .z3
  | "cvc4" => some .cvc4
  | "cvc5" => some .cvc5
  | _      => none

end Auto.Solver.SMT

open Auto.Solver.SMT in
register_option auto.smt.solver.name : SolverName := {
  defValue := SolverName.z3
  descr := "Name of the designated SMT solver. Use `none` to disable solver querying."
}

namespace Auto.Solver.SMT

open IR.SMT
open Parser.SMTTerm

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

private def emitCommand (p : SolverProc) (c : IR.SMT.Command) : IO Unit := do
  p.stdin.putStr s!"{c}\n"
  p.stdin.flush

private def emitCommands (p : SolverProc) (c : Array IR.SMT.Command) : IO Unit := do
  let _ ← c.mapM (emitCommand p)

def createSolver (name : SolverName) : MetaM SolverProc := do
  let tlim := auto.smt.timeout.get (← getOptions)
  match name with
  | .none => throwError "{decl_name%} :: Unexpected error"
  | .z3   => createAux "z3" #["-in", "-smt2", s!"-T:{tlim}"]
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 =>
    let dumpHints := auto.smt.dumpHints.get (← getOptions)
    let limitedRws := auto.smt.dumpHints.limitedRws.get (← getOptions)
    let sygusInst := auto.smt.sygus_inst.get (← getOptions)
    let mut flags := #[s!"--tlimit={tlim * 1000}", "--produce-models", "--enum-inst"]
    if dumpHints then
      flags := flags ++ #["--dump-hints", "--proof-granularity=dsl-rewrite"]
    if limitedRws then
      flags := flags.push "--hints-only-rw-insts"
    if sygusInst then
      flags := flags.push "--sygus-inst"
    createAux "cvc5" flags
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

axiom autoSMTSorry.{u} (α : Sort u) : α

def getTerm (s : String) : MetaM (Parser.SMTTerm.Term × String) := do
  match ← lexTerm s ⟨0⟩ {} with
  | .complete se p => return (se, Substring.toString ⟨s, p, s.endPos⟩)
  | .incomplete _ _ => throwError s!"getTerm {decl_name%} :: Incomplete input {s}"
  | .malformed => throwError s!"getTerm {decl_name%} :: Malformed (prefix of) input {s}"

/--
  Recover id of valid facts from unsat core. Refer to `lamFOL2SMT`
-/
def validFactOfUnsatCore (unsatCore : Parser.SMTTerm.Term) : MetaM (Array Nat) := do
  let .app unsatCore := unsatCore
    | throwError "{decl_name%} :: Malformed unsat core `{unsatCore}`"
  let mut ret := #[]
  for sexp in unsatCore do
    let .atom (.symb name) := sexp
      | continue
    if name.take 11 == "valid_fact_" then
      let .some n := (name.drop 11).toNat?
        | throwError "{decl_name%} :: The id {name.drop 11} of {name} is invalid"
      ret := ret.push n
  return ret

/-- Only put declarations in the query -/
def querySolver (query : Array IR.SMT.Command) : MetaM (Option (Parser.SMTTerm.Term × String)) := do
  if !(auto.smt.get (← getOptions)) then
    throwError "{decl_name%} :: Unexpected error"
  if (auto.smt.solver.name.get (← getOptions) == .none) then
    logInfo s!"{decl_name%} :: Skipped"
    return .none
  let name := auto.smt.solver.name.get (← getOptions)
  let solver ← createSolver name
  emitCommand solver (.setOption (.produceProofs true))
  emitCommand solver (.setOption (.produceUnsatCores true))
  emitCommands solver query
  emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  let (checkSatResponse, _) ← getTerm stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    let (model, _) ← getTerm stdout
    solver.kill
    trace[auto.smt.result] "{name} says Sat"
    trace[auto.smt.model] "Model:\n{model}"
    trace[auto.smt.stderr] "stderr:\n{stderr}"
    return .none
  | .atom (.symb "unsat") =>
    emitCommand solver .getUnsatCore
    emitCommand solver .getProof
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    let (unsatCore, stdout) ← getTerm stdout
    solver.kill
    trace[auto.smt.result] "{name} says Unsat, unsat core:\n{unsatCore}"
    trace[auto.smt.proof] "Proof:\n{stdout}"
    trace[auto.smt.stderr] "stderr:\n{stderr}"
    return .some (unsatCore, stdout)
  | _ =>
    trace[auto.smt.result] "{name} produces unexpected check-sat response\n {checkSatResponse}"
    solver.kill
    return .none

/-- solverHints includes:
    - preprocessFacts : List (Parser.SMTTerm.Term)
    - theoryLemmas : List (Parser.SMTTerm.Term)
    - instantiations : List (Parser.SMTTerm.Term)
    - computationLemmas : List (Parser.SMTTerm.Term)
    - polynomialLemmas : List (Parser.SMTTerm.Term)
    - rewriteFacts : List (List (Parser.SMTTerm.Term)) -/
abbrev solverHints :=
  List (Parser.SMTTerm.Term) × List (Parser.SMTTerm.Term) × List (Parser.SMTTerm.Term) ×
  List (Parser.SMTTerm.Term) × List (Parser.SMTTerm.Term) × List (List (Parser.SMTTerm.Term))

/-- Behaves like `querySolver` but assumes that the output came from cvc5 with `--dump-hints` enabled. The
    additional output is used to return not just the unsatCore and proof, but also a list of theory lemmas. -/
def querySolverWithHints (query : Array IR.SMT.Command)
  : MetaM (Option (Parser.SMTTerm.Term × solverHints × String)) := do
  if !(auto.smt.get (← getOptions)) then
    throwError "querySolver :: Unexpected error"
  if (auto.smt.solver.name.get (← getOptions) == .none) then
    logInfo "querySolver :: Skipped"
    return .none
  let name := auto.smt.solver.name.get (← getOptions)
  let solver ← createSolver name
  emitCommand solver (.setOption (.produceProofs true))
  emitCommand solver (.setOption (.produceUnsatCores true))
  emitCommands solver query
  emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  trace[auto.smt.result] "checkSatResponse: {stdout}"
  -- **TODO** When checkSatResponse is sat, the below getTerm call can throw an error
  let (checkSatResponse, _) ← getTerm stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    solver.kill
    try
      let (model, _) ← getTerm stdout
      trace[auto.smt.result] "{name} says Sat"
      trace[auto.smt.model] "Model:\n{model}"
      trace[auto.smt.stderr] "stderr:\n{stderr}"
      return .none
    catch _ => -- Don't let a failure to parse the model prevent `querySolverWithHints` from returning `none`
      return .none
  | .atom (.symb "unsat") =>
    emitCommand solver (.echo "Unsat core:")
    emitCommand solver .getUnsatCore
    emitCommand solver .getProof
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[auto.smt.result] "Original unfiltered {name} output: {stdout}"
    let [_, stdout] := stdout.splitOn "Preprocess:"
      | throwError "Error finding preprocess facts in output"
    let [preprocessFacts, stdout] := stdout.splitOn "Theory lemmas:"
      | throwError "Error finding theory lemmas in output"
    let [theoryLemmas, stdout] := stdout.splitOn "Instantiations:"
      | throwError "Error finding instantiations in output"
    let [instantiations, stdout] := stdout.splitOn "Evaluation/computation:"
      | throwError "Error finding evaluation/computation section in output"
    let [computationLemmas, stdout] := stdout.splitOn "Polynomial normalization:"
      | throwError "Error finding polymolial normalization section in output"
    let firstRewritesLabel :=
      "Rewrites (rule defs (if any) and their usages in quantifier-free terms):"
    let (polynomialLemmas, stdout) :=
      match stdout.splitOn firstRewritesLabel with
      | [polynomialLemmas, stdout] => (polynomialLemmas, stdout)
      | _ => ("", stdout)
    let rewriteFacts := stdout.splitOn "Rewrites:"
    let some stdout := rewriteFacts.getLast?
      | throwError "Error finding rewrites"
    let rewriteFacts := rewriteFacts.take (rewriteFacts.length - 1)
    let [lastRewriteFact, stdout] := stdout.splitOn "\"Unsat core:\""
      | throwError "Error finding unsat core in output"
    let rewriteFacts := rewriteFacts.append [lastRewriteFact]
    let (unsatCore, stdout) ← getTerm stdout
    let preprocessFacts ← lexAllTerms preprocessFacts 0 []
    let theoryLemmas ← lexAllTerms theoryLemmas 0 []
    let instantiations ← lexAllTerms instantiations 0 []
    let computationLemmas ← lexAllTerms computationLemmas 0 []
    let polynomialLemmas ← lexAllTerms polynomialLemmas 0 []
    let rewriteFacts ← rewriteFacts.mapM (fun rwFact => lexAllTerms rwFact 0 [])
    trace[auto.smt.result] "{name} says Unsat, unsat core:\n{unsatCore}"
    trace[auto.smt.result] "{name} preprocess facts:\n{preprocessFacts}"
    trace[auto.smt.result] "{name} theory lemmas:\n{theoryLemmas}"
    trace[auto.smt.result] "{name} computation/evaluation lemmas:\n{computationLemmas}"
    trace[auto.smt.result] "{name} polynomial normalization lemmas:\n{polynomialLemmas}"
    trace[auto.smt.result] "{name} instantiations:\n{instantiations}"
    trace[auto.smt.result] "{name} rewriteFacts:\n{rewriteFacts}"
    trace[auto.smt.stderr] "stderr:\n{stderr}"
    solver.kill
    let solverHints := (preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts)
    return .some (unsatCore, solverHints, stdout)
  | _ =>
    trace[auto.smt.result] "{name} produces unexpected check-sat response\n {checkSatResponse}"
    return .none

def saveQuery (query : Array IR.SMT.Command) : MetaM Unit := do
  if !(auto.smt.save.get (← getOptions)) then
    throwError "{decl_name%} :: Unexpected error"
  let path := auto.smt.savepath.get (← getOptions)
  IO.FS.withFile path IO.FS.Mode.write fun fd =>
    for cmd in query do
      fd.putStrLn s!"{cmd}"

end Solver.SMT

end Auto
