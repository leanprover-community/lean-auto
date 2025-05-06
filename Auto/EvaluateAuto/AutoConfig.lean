import Lean
import Auto.Tactic

open Lean Auto

namespace EvalAuto

inductive SolverConfig where
  -- Use `duper` as the backend prover
  | native
  -- Use `duper` as the backend prover, without any preprocessing
  | rawNative
  -- Use `lean-smt`, currently not supported
  | leanSmt
  | smt (solverName : Solver.SMT.SolverName)
  | tptp (solverName : Solver.TPTP.SolverName) (path : String)
  deriving BEq, Hashable, Repr

instance : ToString SolverConfig where
  toString : SolverConfig → String
  | .native       => "native"
  | .rawNative    => "rawNative"
  | .leanSmt      => "leanSmt"
  | .smt sn       => s!"smt {sn}"
  | .tptp sn path => s!"tptp {sn} {path}"

def disableAllSolvers (o : Options) : Options :=
  let o := auto.native.set o false
  let o := auto.smt.set o false
  let o := auto.tptp.set o false
  o

def withAutoSolverConfigOptions
  {m : Type → Type} [Monad m] [MonadError m]
  [MonadWithOptions m] [MonadControlT CoreM m] [MonadWithReaderOf Core.Context m]
  (config : SolverConfig)
  (timeout : Nat) -- Timeout for external provers
  (k : m α) : m α :=
  match config with
  | .native       =>
    withOptions (fun o =>
      let o := disableAllSolvers o
      let o := auto.native.set o true
      let o := auto.mono.mode.set o MonoMode.hol
      o) <| k
  | .rawNative    => k
  | .leanSmt      =>
    throwError "Lean-SMT is currently not supported"
  | .smt sn       =>
    withOptions (fun o =>
      let o := disableAllSolvers o
      let o := auto.smt.set o true
      let o := auto.smt.solver.name.set o sn
      let o := auto.smt.timeout.set o timeout
      let o := auto.smt.trust.set o true
      let o := auto.mono.mode.set o MonoMode.fol
      o) <| k
  | .tptp sn path =>
    withOptions (fun o =>
      let o := disableAllSolvers o
      let o := auto.tptp.set o true
      let o := auto.tptp.solver.name.set o sn
      let o := auto.tptp.timeout.set o timeout
      let o := auto.tptp.trust.set o true
      let o := auto.mono.mode.set o MonoMode.hol
      match sn with
      | .zipperposition => auto.tptp.zipperposition.path.set o path
      | .zipperposition_exe => o -- `zipperposition_exe` is built in and does not need a path to be set
      | .zeport _       => auto.tptp.zeport.path.set o path
      | .eproverHo      => auto.tptp.eproverHo.path.set o path
      | .vampire        => auto.tptp.vampire.path.set o path) <|
        k

end EvalAuto
