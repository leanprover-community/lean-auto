import Lean
import Auto.Lib.ExprExtra
open Lean Meta Elab

initialize
  registerTraceClass `auto.metaExtra

namespace Auto

def Meta.isDefEqD (t s : Expr) : MetaM Bool := Meta.withDefault <| Meta.isDefEq t s

def Meta.whnfNondependentForall (e : Expr) : MetaM Expr := do
  let e' ← Meta.whnf e
  match e' with
  | .forallE _ _ body _ =>
    if body.hasLooseBVar 0 then
      return e
    else
      return e'
  | _ => return e

partial def Meta.normalizeNondependentForall (e : Expr) : MetaM Expr := do
  let e' ← whnfNondependentForall e
  match e' with
  | .forallE name ty body bi =>
    if body.hasLooseBVar 0 then
      return e
    let ty' ← normalizeNondependentForall ty
    let body' ← normalizeNondependentForall body
    return .forallE name ty' body' bi
  | _ => return e

def Meta.withoutMVarAssignments (m : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  Meta.withMCtx {mctx with eAssignment := {}, lAssignment := {}} m

initialize
  registerTraceClass `auto.inspectMVarAssignments

def Meta.inspectMVarAssignments : MetaM Unit := do
  let mctx ← getMCtx
  let eAssignmentList := mctx.eAssignment.toList
  let lAssignmentList := mctx.lAssignment.toList
  let composeAssignMessage (ms : List MessageData) : MetaM MessageData := do
    let mut rm := m!"["
    let mut fst := true
    for m in ms do
      if fst then
        fst := false
      else
        rm := .compose rm m!", "
      rm := .compose rm m
    return .compose rm "]"
  Meta.withMCtx {mctx with eAssignment := {}, lAssignment := {}} <| do
    let ems := eAssignmentList.map (fun (id, e) => MessageData.compose m!"{Expr.mvar id} := " m!"{e}")
    trace[auto.inspectMVarAssignments] .compose "ExprMVar Assignments: " (← composeAssignMessage ems)
    let lms := lAssignmentList.map (fun (id, l) => MessageData.compose m!"{Level.mvar id} := " m!"{l}")
    trace[auto.inspectMVarAssignments] .compose "LevelMVar Assignments: " (← composeAssignMessage lms)

/-- Synthesize inhabited instance for a given type -/
def Meta.trySynthInhabited (e : Expr) : MetaM (Option Expr) := do
  let eSort ← Expr.normalizeType (← instantiateMVars (← Meta.inferType e))
  let .sort lvl := eSort
    | throwError "{decl_name%} :: {e} is not a type"
  try
    if let .some inh ← Meta.synthInstance? e then
      return .some inh
    if let .some inh ← Meta.synthInstance? (Lean.mkApp (.const ``Inhabited [lvl]) e) then
      return .some (Lean.mkApp2 (.const ``Inhabited.default [lvl]) e inh)
    if let .some inh ← Meta.synthInstance? (Lean.mkApp (.const ``Nonempty [lvl]) e) then
      return .some (Lean.mkApp2 (.const ``Classical.choice [lvl]) e inh)
    return .none
  catch _ =>
    return .none

syntax (name := fromMetaTactic) "fromMetaTactic" "[" ident "]" : tactic

@[tactic fromMetaTactic]
unsafe def evalFromMetaTactic : Tactic.Tactic
| `(fromMetaTactic | fromMetaTactic [ $i ]) => do
  let some iexpr ← Term.resolveId? i
    | throwError "{decl_name%} :: Unknown identifier {i}"
  let mtname := iexpr.constName!
  let Except.ok mt := (← getEnv).evalConst (MVarId → MetaM (List MVarId)) (← getOptions) mtname
    | throwError "{decl_name%} :: Failed to evaluate {mtname} to a term of type (Expr → TermElabM Unit)"
  Tactic.liftMetaTactic mt
| _ => Elab.throwUnsupportedSyntax

-- **-TODO: Deal with mutual dependencies between mvar and fvar**
-- **-      Maybe inspect the LocalContext in the metavariable declaration**
def Meta.abstractAllMVarFVar (e : Expr) : MetaM Expr := do
  let mut curr := e
  -- **TODO: Fix**
  while true do
    let next ← instantiateMVars (← zetaReduce curr)
    if next == curr then
      break
    curr := next
  let e := curr
  -- Now `(e == (← instantiateMVars) e) && (e == (← zetaReduce e))`
  let res ← Meta.abstractMVars (levels := false) e
  -- Now expr mvars in `e` are abstracted
  let mut e := res.expr
  -- **TODO: Fix**
  while true do
    let (_, collectFVarsState) ← e.collectFVars.run {}
    -- Now free variables in `e` are abstracted
    e ← mkLambdaFVars (collectFVarsState.fvarIds.map Expr.fvar) e
    if !e.hasFVar then
      break
  let res ← Meta.abstractMVars (levels := true) e
  -- Now level mvars in `e` are abstracted
  -- Level mvars must be abstracted after fvars are abstracted,
  --   because they may occur in fvars
  return res.expr

def Meta.coreCheck (e : Expr) : MetaM (Option Expr) := do
  let e ← Meta.abstractAllMVarFVar e
  match Kernel.check (← getEnv) {} e with
  | Except.ok type => return .some type
  | Except.error _ => return .none

def Meta.isTypeCorrectCore (e : Expr) : MetaM Bool := do
  let type? ← Meta.coreCheck e
  return type?.isSome

def Meta.withMaxHeartbeats [Monad m] [MonadLiftT BaseIO m]
    [MonadWithReaderOf Core.Context m] (n : Nat) (x : m α) : m α := do
  let numHeartbeats ← IO.getNumHeartbeats
  let f s := {
    s with
    initHeartbeats := numHeartbeats
    maxHeartbeats := n * 1000
  }
  withReader f x

def Meta.exToExcept (x : MetaM α) : MetaM (Except Exception α) :=
  try
    let v ← x
    return .ok v
  catch e =>
    return .error e

def Meta.runtimeExToExcept (x : MetaM α) : MetaM (Except Exception α) :=
  tryCatchRuntimeEx (do let v ← x; return .ok v) (fun e => return .error e)

/--
  Workaround for modifying the `lctx` field of `Meta.Context`
-/
def Meta.Context.modifyLCtx (ctx : Context) (lctx : LocalContext) : CoreM Context :=
  MetaM.run' (withLCtx' lctx read) ctx

/--
  Workaround for modifying the `localInstances` field of `Meta.Context`
-/
def Meta.Context.modifyLocalInstances (ctx : Context) (localInsts : LocalInstances) : CoreM Context :=
  MetaM.run' (withLCtx ctx.lctx localInsts read) ctx

/--
Replace occurrences of `p` in non-dependent positions in `e` with `q`. The type
of the resulting expression should be identical to the type of `e`
· Both `e` and `q` are not supposed to contain loose bvars
· We detect subterms equivalent to `p` using key-matching.
  That is, only perform `isDefEq` tests when the head symbol of substerm is equivalent to head symbol of `p`.
· We only abstract non-dependent positions
  That is, if there is a function application `f a` and the argument of
  `f` is dependent, then occurrences of `p` in `a` will not be abstracted

By default, all occurrences are abstracted,
but this behavior can be controlled using the `occs` parameter.

All matches of `p` in `e` are considered for occurrences,
but for each match that is included by the `occs` parameter,
metavariables appearing in `p` (or `e`) may become instantiated,
affecting the possibility of subsequent matches.
For matches that are not included in the `occs` parameter, the metavariable context is rolled back
to prevent blocking subsequent matches which require different instantiations.
-/
partial def Meta.replaceNonDep (e : Expr) (p : Expr) (q : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a         => do
        let type ← Meta.whnf (← Meta.inferType f)
        let .forallE _ _ b _ := type
          | throwError "{decl_name%} :: {type} is not a `∀`"
        if b.hasLooseBVar 0 then
          return e.updateApp! (← visit f) a
        else
          return e.updateApp! (← visit f) (← visit a)
      | .mdata _ b       => return e.updateMData! (← visit b)
      | .proj _ _ b      => return e.updateProj! (← visit b)
      | .letE n t v b _ =>
        Meta.withLetDecl n t (← visit v) fun x =>
          return ← mkLetFVars #[x] (← visit (b.instantiate1 x))
      | .lam ..     =>
        Meta.lambdaTelescope e fun xs b => do
          return ← mkLambdaFVars xs (← visit b)
      | .forallE n d b bi => do
        let d' ← (if b.hasLooseBVar 0 then return d else visit d)
        Meta.withLocalDecl n bi d' fun x => do
          return ← mkForallFVars #[x] (← visit (b.instantiate1 x))
      | e                => return e
    if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let i ← get
        set (i+1)
        if occs.contains i then
          return q
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e |>.run' 1

end Auto
