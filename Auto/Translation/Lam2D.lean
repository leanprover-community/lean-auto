import Lean
import Duper.Tactic
import Auto.Util.ExprExtra
import Auto.Util.MetaExtra
import Auto.Embedding.LamBase
import Auto.Translation.LamReif
open Lean

-- Lam2D : Simply-typed lambda calculus to Lean
-- The reason we need this file is that, sometimes we want external
--   provers (e.g. duper) to help us complete proofs. Note that
--   external provers does not work with things like `GLift.up Prop`.
--   Therefore, we must have a function to translate expressions
--   into `un-lifted` (original) `Lean expressions`.
-- Also, an important part of translating to un-lifted Lean
--   expressions is to deal with `=, ∀` and `∃`, namely assigning
--   the appropriate valuation so that the type matches.

namespace Auto.Lam2D

open LamReif
open Embedding.Lam

-- All the type atoms and term atoms are interpreted as fvars, which
--   are let-declarations in the local context. We don't want the external
--   prover to unfold these let-declarations, so we add these atoms as
--   non-let free variables into the local context, run the external prover,
--   abstract these free variables after the external prover has
--   finished, and apply the abstracted expression to the value of
--   these atoms to restore the requires expression.
structure Context where
  -- Type atoms that are used in the expressions sent to external prover
  typeAtomFVars   : HashMap Nat FVarId := HashMap.empty
  -- Term atoms that are used in the expressions sent to external prover
  termAtomFVars   : HashMap Nat FVarId := HashMap.empty

abbrev ExternM := ReaderT Context ReifM

#genMonadContext ExternM

def withTypeAtomAsFVar (atom : Nat) (cont : ExternM Expr) : ExternM Expr := do
  if (← getTypeAtomFVars).contains atom then
    return ← cont
  let freshId := (← mkFreshId).toString
  let (_, orig, lvl) ← lookupTyVal! atom
  Meta.withLocalDeclD ("_exTypeAtom_" ++ freshId) (.sort lvl) (fun newFVar =>
    withReader (fun s => {s with typeAtomFVars := s.typeAtomFVars.insert atom newFVar.fvarId!}) (do
      let abst ← Meta.mkLambdaFVars #[newFVar] (← cont)
      -- We have to `headBeta` this `appExpr`, otherwise the term
      --   might not be type correct
      -- For example, suppose we have `x : α`, where `α` is type
      --   atom 0, and `x` is term atom 0. Now we call the external
      --   prover, which returns an expression `termAtom 0 = termAtom 0`.
      --   After going up `with<Type/Term>AtomAsFVar`, it will
      --   become `(fun (α' : Sort _) => (fun (x' : α') => x' = x') (x : α)) α`
      --   and the application `(fun (x' : α') => x' = x') (x : α)` is not
      --   type correct.
      -- However, the above term will be type correct if we `headBeta1`
      --   at each `withTypeAtomAsFVar
      match abst with
      | .lam _ _ body _ => return body.instantiate1 orig
      | _ => throwError "withTypeAtomAsFVar :: Unexpected expression {abst}"
      )
    )

def withTypeAtomsAsFVar (atoms : Array Nat) (cont : ExternM Expr) : ExternM Expr :=
  atoms.foldl (fun cont atom => withTypeAtomAsFVar atom cont) cont

-- Takes a `s : LamSort` and produces the `un-lifted` version of `s.interp`
--   (note that `s.interp` is lifted)
-- This function should be called after we've called
--   `withTypeAtomAsFVar` on all the type atoms occurring in `s`
def interpLamSortAsUnlifted : LamSort → ExternM Expr
| .atom n => do
  let .some fid := (← getTypeAtomFVars).find? n
    | throwError "interpLamSortAsUnlifted :: Cannot find fvarId assigned to type atom {n}"
  return .fvar fid
| .base b =>
  match b with
  | .prop => return .sort .zero
  | .int  => return .const ``Int []
  | .real => return .const ``Real []
  | .bv n => return .app (.const ``Bitvec []) (.lit (.natVal n))
| .func s₁ s₂ => do
  return .forallE `_ (← interpLamSortAsUnlifted s₁) (← interpLamSortAsUnlifted s₂) .default

def withTermAtomAsFVar (atom : Nat) (cont : ExternM Expr) : ExternM Expr := do
  if (← getTermAtomFVars).contains atom then
    return ← cont
  let freshId := (← mkFreshId).toString
  let (_, e, s) ← lookupVarVal! atom
  let sinterp ← interpLamSortAsUnlifted s
  Meta.withLocalDeclD ("_exTermAtom_" ++ freshId) sinterp (fun newFVar =>
    withReader (fun s => {s with termAtomFVars := s.termAtomFVars.insert atom newFVar.fvarId!}) (do
      let abst ← Meta.mkLambdaFVars #[newFVar] (← cont)
      return mkApp abst e)
    )

def withTermAtomsAsFVar (atoms : Array Nat) (cont : ExternM Expr) : ExternM Expr :=
  atoms.foldl (fun cont atom => withTermAtomAsFVar atom cont) cont

def interpCstrRealAsUnlifted (c : CstrReal) : Expr :=
  let lvl₁ := Level.succ .zero
  let real := Expr.const ``Real []
  match c with
  | .zero => .app (.app (.const ``Zero.zero [lvl₁]) real) real
  | .one => .app (.app (.const ``One.one [lvl₁]) real) real

open Embedding in
def interpLamBaseTermAsUnlifted : LamBaseTerm → ExternM Expr
| .trueE      => return .const ``True []
| .falseE     => return .const ``False []
| .not        => return .const ``Not []
| .and        => return .const ``And []
| .or         => return .const ``Or []
| .imp        => return .const ``ImpF [.zero, .zero]
| .iff        => return .const ``Iff []
| .intVal _   => throwError "Not implemented"
| .realVal c  => return interpCstrRealAsUnlifted c
| .bvVal _    => throwError "Not implemented"
| .eqI _      => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .forallEI _ => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .existEI _  => throwError ("interpLamTermAsUnlifted :: " ++ exportError.ImpPolyLog)
| .eq s       => do
  return ← Meta.mkAppOptM ``Eq #[← interpLamSortAsUnlifted s]
| .forallE s  => do
  let ty ← interpLamSortAsUnlifted s
  let sort ← Util.normalizeType (← Meta.inferType ty)
  let Expr.sort lvl := sort
    | throwError "interpLamBaseTermAsUnlifted :: Unexpected sort {sort}"
  return mkAppN (.const ``forallF [lvl, .zero]) #[← interpLamSortAsUnlifted s]
| .existE s  => do
  return ← Meta.mkAppOptM ``Exists #[← interpLamSortAsUnlifted s]

-- Takes a `t : LamTerm` and produces the `un-lifted` version of `t.interp`.
-- This function should be called after we've called
--   `withTermAtomAsFVar` on all the term atoms occurring in `t`
def interpLamTermAsUnlifted : LamTerm → ExternM Expr
| .atom n => do
  let .some fid := (← getTermAtomFVars).find? n
    | throwError "interpLamTermAsUnlifted :: Cannot find fvarId assigned to term atom {n}"
  return .fvar fid
| .base b => interpLamBaseTermAsUnlifted b
| .bvar n => return .bvar n
| .lam s t => do
  let sinterp ← interpLamSortAsUnlifted s
  let tinterp ← interpLamTermAsUnlifted t
  return .lam (← mkFreshId) sinterp tinterp .default
| .app _ fn arg => do
  return .app (← interpLamTermAsUnlifted fn) (← interpLamTermAsUnlifted arg)

-- The external prover should only see the local context
--   and an array of Lean expressions, and should not see
--   anything within `ExternM, LamReif.ReifM, ULiftM` or `Reif.ReifM`
def withTranslatedLamTerms (ts : Array LamTerm) (externCont : Array Expr → MetaM Expr) : ReifM Expr :=
  let extern : ExternM Expr := do
    let hss ← ts.mapM (fun t => liftM (collectAtoms t))
    let (typeHs, termHs) := hss.foldl
      (fun (typeHs, termHs) (typeHs', termHs') =>
        (mergeHashSet typeHs typeHs', mergeHashSet termHs termHs')) (HashSet.empty, HashSet.empty)
    withTypeAtomsAsFVar typeHs.toArray (
      withTermAtomsAsFVar termHs.toArray (do
        externCont (← ts.mapM interpLamTermAsUnlifted)
      )
    )
  extern.run {}

-- Override the one in duper so that it works for `MetaM`
def Duper.withoutModifyingCoreEnv (m : MetaM α) : MetaM α :=
  try
    let env := (← liftM (get : CoreM Core.State)).env
    let ret ← m
    liftM (modify fun s => {s with env := env} : CoreM Unit)
    return ret
  catch e =>
    throwError e.toMessageData

-- Override the one in duper so that it works for `MetaM`
def Duper.rconsProof (state : Duper.ProverM.State) : MetaM Expr := do
  let some emptyClause := state.emptyClause
    | throwError "rconsProof :: Can't find empty clause in ProverM's state"
  let l := (← Elab.Tactic.collectClauses state emptyClause (#[], Std.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[ProofReconstruction] "Collected clauses: {l}"
  -- First make proof for skolems, then make proof for clauses
  let proof ← Elab.Tactic.mkAllProof state l
  trace[ProofReconstruction] "rconsProof :: Reconstructed proof {proof}"
  return proof

-- Given `ts = #[t₀, t₁, ⋯, kₖ₋₁]`, invoke Duper to get a proof 
--   `t₀ → t₁ → ⋯ → tₖ₋1 → ⊥`
def callDuper (ts : Array LamTerm) : ReifM Expr :=
  withTranslatedLamTerms ts (fun exprs => do
    let startTime ← IO.monoMsNow
    for expr in exprs do
      if !(← Meta.isTypeCorrect expr) then
        throwError "callDuper :: Malformed hypothesis {expr}"
      if !(← Meta.isProp expr) then
        throwError "callDuper :: Hypothesis {expr} is not a proposition"
    -- Reduce `forallF` and `impF`
    let exprs ← Meta.withTransparency .reducible <| exprs.mapM (fun e => liftM <| Meta.reduceAll e)
    Util.Meta.withHyps exprs (fun fvars => do
      if exprs.size != fvars.size then
        throwError "callDuper :: Unexpected error"
      let lemmas : Array (Expr × Expr × Array Name) ←
        (exprs.zip fvars).mapM (fun (ty, proof) => do
          return (ty, ← Meta.mkAppM ``eq_true #[.fvar proof], #[]))
      let state ← Duper.withoutModifyingCoreEnv <| do
        let skSorryName ← Elab.Tactic.addSkolemSorry
        let (_, state) ←
          Duper.ProverM.ProverM.runWithExprs (ctx := {}) (s := {skolemSorryName := skSorryName})
            Duper.ProverM.saturateNoPreprocessingClausification
            lemmas.toList
        return state
      match state.result with
      | .contradiction =>
        IO.println s!"callDuper :: Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
        let expr ← Duper.rconsProof state
        Meta.mkLambdaFVars (fvars.map (.fvar ·)) expr
      | .saturated =>
        throwError "callDuper :: Duper saturated"
      | .unknown => throwError "callDuper :: Duper was terminated"
    )
  )

end Auto.Lam2D