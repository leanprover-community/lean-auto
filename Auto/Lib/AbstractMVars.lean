import Lean

open Lean Meta

namespace Auto
namespace AbstractMVars

/- **TODO:** Update according to the `AbstractMVars` implementation of Lean -/

structure AbstractMVarsResult where
  paramNames : Array Name
  numMVars   : Nat
  expr       : Expr
  deriving Inhabited, BEq

structure State where
  ngen         : NameGenerator
  lctx         : LocalContext
  mctx         : MetavarContext
  nextParamIdx : Nat := 0
  paramNames   : Array Name := #[]
  fvars        : Array Expr  := #[]
  lmap         : Std.HashMap LMVarId Level := {}
  emap         : Std.HashMap MVarId Expr  := {}

abbrev M := StateM State

@[always_inline]
instance : MonadMCtx M where
  getMCtx := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

def mkFreshId : M Name := do
  let s ← get
  let fresh := s.ngen.curr
  modify fun s => { s with ngen := s.ngen.next }
  pure fresh

def mkFreshFVarId : M FVarId :=
  return { name := (← mkFreshId) }

/-- Bug fix for ``abstractLevelMVars`` in Lean -/
private partial def abstractLevelMVars (u : Level) : M Level := do
  if !u.hasMVar then
    return u
  else
    match u with
    | Level.zero        => return u
    | Level.param _     => return u
    | Level.succ v      => return u.updateSucc! (← abstractLevelMVars v)
    | Level.max v w     => return u.updateMax! (← abstractLevelMVars v) (← abstractLevelMVars w)
    | Level.imax v w    => return u.updateIMax! (← abstractLevelMVars v) (← abstractLevelMVars w)
    | l@(Level.mvar mvarId) =>
      let s ← get
      let depth := s.mctx.getLevelDepth mvarId;
      if depth != s.mctx.depth then
        return u -- metavariables from lower depths are treated as constants
      else
        let lNew ← instantiateLevelMVars l
        if l != lNew then
          abstractLevelMVars lNew
        else
          match s.lmap.get? mvarId with
          | some u => pure u
          | none   =>
            let paramId := Name.mkNum `_abstMVar s.nextParamIdx
            let u := mkLevelParam paramId
            modify fun s => { s with nextParamIdx := s.nextParamIdx + 1, lmap := s.lmap.insert mvarId u, paramNames := s.paramNames.push paramId }
            return u

partial def abstractExprMVars (e : Expr) : M Expr := do
  if !e.hasMVar then
    return e
  else
    match e with
    | e@(Expr.lit _)           => return e
    | e@(Expr.bvar _)          => return e
    | e@(Expr.fvar _)          => return e
    | e@(Expr.sort u)          => return e.updateSort! (← abstractLevelMVars u)
    | e@(Expr.const _ us)      => return e.updateConst! (← us.mapM abstractLevelMVars)
    | e@(Expr.proj _ _ s)      => return e.updateProj! (← abstractExprMVars s)
    | e@(Expr.app f a)         => return e.updateApp! (← abstractExprMVars f) (← abstractExprMVars a)
    | e@(Expr.mdata _ b)       => return e.updateMData! (← abstractExprMVars b)
    | e@(Expr.lam _ d b _)     => return e.updateLambdaE! (← abstractExprMVars d) (← abstractExprMVars b)
    | e@(Expr.forallE _ d b _) => return e.updateForallE! (← abstractExprMVars d) (← abstractExprMVars b)
    | e@(Expr.letE _ t v b _)  => return e.updateLet! (← abstractExprMVars t) (← abstractExprMVars v) (← abstractExprMVars b)
    | e@(Expr.mvar mvarId)     =>
      let decl := (← getMCtx).getDecl mvarId
      if decl.depth != (← getMCtx).depth then
        return e
      else
        let eNew ← instantiateMVars e
        if e != eNew then
          abstractExprMVars eNew
        else
          match (← get).emap.get? mvarId with
          | some e =>
            return e
          | none   =>
            let type   ← abstractExprMVars decl.type
            let fvarId ← mkFreshFVarId
            let fvar := mkFVar fvarId;
            let userName ← if decl.userName.isAnonymous then pure <| (`x).appendIndexAfter (← get).fvars.size else pure decl.userName
            modify fun s => {
              s with
              emap  := s.emap.insert mvarId fvar,
              fvars := s.fvars.push fvar,
              lctx  := s.lctx.mkLocalDecl fvarId userName type }
            return fvar

end AbstractMVars

/--
  Abstract (current depth) metavariables occurring in `e`.
  The result contains
  - An array of universe level parameters that replaced universe metavariables occurring in `e`.
  - The number of (expr) metavariables abstracted.
  - And an expression of the form `fun (m_1 : A_1) ... (m_k : A_k) => e'`, where
    `k` equal to the number of (expr) metavariables abstracted, and `e'` is `e` after we
    replace the metavariables.

  Example: given `f.{?u} ?m1` where `?m1 : ?m2 Nat`, `?m2 : Type -> Type`. This function returns
  `{ levels := #[u], size := 2, expr := (fun (m2 : Type -> Type) (m1 : m2 Nat) => f.{u} m1) }`

  This API can be used to "transport" to a different metavariable context.
  Given a new metavariable context, we replace the `AbstractMVarsResult.levels` with
  new fresh universe metavariables, and instantiate the `(m_i : A_i)` in the lambda-expression
  with new fresh metavariables.

  Application: we use this method to cache the results of type class resolution. -/
def abstractMVars (e : Expr) : MetaM Auto.AbstractMVars.AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }

def openAbstractMVarsResult (a : Auto.AbstractMVars.AbstractMVarsResult) : MetaM (Array Expr × Array BinderInfo × Expr) := do
  let us ← a.paramNames.mapM fun _ => mkFreshLevelMVar
  let e := a.expr.instantiateLevelParamsArray a.paramNames us
  lambdaMetaTelescope e (some a.numMVars)

def abstractMVarsForall (e : Expr) : MetaM Auto.AbstractMVars.AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkForall s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }

def abstractMVarsLambdaWithIds (e : Expr) : MetaM (Expr × Array Expr × Array Name × Array Level) := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e
  -- Restore the corresponding expr mvarId
  let sfvars := s.fvars
  let mut fvarpos : Std.HashMap FVarId Nat := {}
  for i in [:sfvars.size] do
    fvarpos := fvarpos.insert sfvars[i]!.fvarId! i
  let mut mvars := sfvars
  for (mid, fvar) in s.emap.toList do
    mvars := mvars.set! (fvarpos.get! fvar.fvarId!) (mkMVar mid)
  -- Restore the corresponding level mvarId
  let sparams := s.paramNames
  let mut parampos : Std.HashMap Name Nat := {}
  for i in [:sparams.size] do
    parampos := parampos.insert sparams[i]! i
  let mut lmvars := sparams.map (Level.param)
  for (lmid, paramname) in s.lmap.toList do
    lmvars := lmvars.set! (parampos.get! (getParamLevelName! paramname)) (mkLevelMVar lmid)
  pure (e, mvars, sparams, lmvars)
where getParamLevelName! : Level → Name
| .param name => name
| e           => panic! s!"Lean.getLevelParamName! :: Level {e} is not a parameter level."

def abstractMVarsLambda (e : Expr) : MetaM Auto.AbstractMVars.AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }
