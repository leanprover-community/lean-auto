import Lean
import Auto.Lib.MonadUtils
import Auto.Lib.MetaExtra
open Lean

namespace Auto.MetaState

structure State extends Meta.State, Meta.Context

structure SavedState where
  core       : Core.State
  metaState  : State

abbrev MetaStateM := StateRefT State CoreM

@[always_inline]
instance : Monad MetaStateM := let i := inferInstanceAs (Monad MetaStateM); { pure := i.pure, bind := i.bind }

instance : MonadLCtx MetaStateM where
  getLCtx := return (← get).toContext.lctx

instance : MonadMCtx MetaStateM where
  getMCtx      := return (← get).toState.mctx
  modifyMCtx f := modify (fun s => {s with mctx := f s.mctx})

instance : MonadEnv MetaStateM where
  getEnv      := return (← getThe Core.State).env
  modifyEnv f := do modifyThe Core.State fun s => { s with env := f s.env, cache := {} }; modify fun s => { s with cache := {} }

instance : AddMessageContext MetaStateM where
  addMessageContext := addMessageContextFull

protected def saveState : MetaStateM SavedState :=
  return { core := (← getThe Core.State), metaState := (← get) }

def SavedState.restore (b : SavedState) : MetaStateM Unit := do
  -- **TODO: Is this safe?**
  liftM (m := CoreM) <| modify fun s => { s with env := b.core.env, messages := b.core.messages, infoState := b.core.infoState }
  modify fun s => { s with mctx := b.metaState.mctx, zetaDeltaFVarIds := b.metaState.zetaDeltaFVarIds, postponed := b.metaState.postponed }

instance : MonadBacktrack SavedState MetaStateM where
  saveState      := MetaState.saveState
  restoreState s := s.restore

#genMonadState MetaStateM

def runMetaM (n : MetaM α) : MetaStateM α := do
  let s ← get
  let (ret, s') ← n.run s.toContext s.toState
  setToState s'
  return ret

def runAtMetaM (n : MetaStateM α) : MetaM (α × Meta.Context) := do
  let s ← get
  let ctx ← read
  let (ret, sc) ← n.run ⟨s, ctx⟩
  set sc.toState
  return (ret, sc.toContext)

/-- Run `n`, set State and discard context -/
def runAtMetaM' (n : MetaStateM α) : MetaM α := do
  let s ← get
  let ctx ← read
  let (ret, sc) ← n.run ⟨s, ctx⟩
  set sc.toState
  return ret

private def runWithFVars (lctx : LocalContext) (fvarids : Array FVarId) (k : MetaM α) : MetaM α := do
  let mut newlctx := (← read).lctx
  for fid in fvarids do
    match lctx.findFVar? (.fvar fid) with
    | .some decl =>
      match decl with
      | .cdecl _ fvarId userName type bi kind =>
        newlctx := newlctx.mkLocalDecl fvarId userName type bi kind
      | .ldecl _ fvarId userName type value nonDep kind =>
        newlctx := newlctx.mkLetDecl fvarId userName type value nonDep kind
    | .none => throwError "{decl_name%} :: Unknown free variable {Expr.fvar fid}"
  Meta.withLCtx' newlctx k

private def runWithIntroducedFVarsImp (m : MetaStateM (Array FVarId × α)) (k : α → MetaM β) : MetaM β := do
  let s ← get
  let ctx ← read
  let ((fvars, a), sc') ← m.run ⟨s, ctx⟩
  runWithFVars sc'.lctx fvars (k a)

/-
  This function is the safe version of `runAtMetaM`
  Rationale:
  · Although we mainly use `MetaStateM` to build a context for another
    `MetaM` action `n`, we sometimes have to destruct `Expr.lam` and introduce
    bound variables as free variables during the process. However, in
    `MetaStateM`, these bound variables does not go away when we finish
    inspecting the `Expr.lam`.
  · To deal with this issue, we can record all the free variables that
    are meant to be in the context of `n`, and use the following function
-/
def runWithIntroducedFVars [MonadControlT MetaM n] [Monad n]
  (m : MetaStateM (Array FVarId × α)) (k : α → n β) : n β :=
  Meta.map1MetaM (fun k => runWithIntroducedFVarsImp m k) k

def inferType (e : Expr) : MetaStateM Expr := runMetaM (Meta.inferType e)

def isDefEq (t s : Expr) : MetaStateM Bool := runMetaM (Meta.isDefEq t s)

def isDefEqRigid (t s : Expr) : MetaStateM Bool := runMetaM (Meta.withNewMCtxDepth (Meta.isDefEq s t))

def isDefEqRigidWith (t s : Expr) (mode : Meta.TransparencyMode) : MetaStateM Bool :=
  runMetaM (Meta.withTransparency mode <| Meta.withNewMCtxDepth (Meta.isDefEq s t))

def isLevelDefEq (u v : Level) : MetaStateM Bool := runMetaM (Meta.isLevelDefEq u v)

def isLevelDefEqRigid (u v : Level) : MetaStateM Bool := runMetaM (Meta.withNewMCtxDepth (Meta.isLevelDefEq u v))

def mkLocalDecl (fvarId : FVarId) (userName : Name) (type : Expr)
  (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := LocalDeclKind.default) : MetaStateM Unit := do
  let ctx ← getToContext
  let lctx := ctx.lctx
  let newCtx ← Meta.Context.modifyLCtx ctx (lctx.mkLocalDecl fvarId userName type bi kind)
  setToContext newCtx

def mkLetDecl (fvarId : FVarId) (userName : Name) (type value : Expr)
  (nonDep : Bool := false) (kind : LocalDeclKind := default) : MetaStateM Unit := do
  let ctx ← getToContext
  let lctx := ctx.lctx
  let newCtx ← Meta.Context.modifyLCtx ctx (lctx.mkLetDecl fvarId userName type value nonDep kind)
  setToContext newCtx

private def withNewLocalInstance (className : Name) (fvar : Expr) : MetaStateM Unit := do
  let localDecl ← runMetaM <| Meta.getFVarLocalDecl fvar
  if !localDecl.isImplementationDetail then
    let ctx ← getToContext
    let newCtx ← Meta.Context.modifyLocalInstances ctx (ctx.localInstances.push { className := className, fvar := fvar })
    setToContext newCtx

private def withNewFVar (fvar fvarType : Expr) : MetaStateM Unit := do
  if let some c ← runMetaM <| Meta.isClass? fvarType then
    withNewLocalInstance c fvar

def withLocalDecl (n : Name) (bi : BinderInfo) (type : Expr) (kind : LocalDeclKind) : MetaStateM FVarId := do
  let fvarId ← mkFreshFVarId
  mkLocalDecl fvarId n type bi kind
  let fvar := mkFVar fvarId
  withNewFVar fvar type
  return fvarId

def withLetDecl (n : Name) (type : Expr) (val : Expr) (kind : LocalDeclKind) : MetaStateM FVarId := do
  let fvarId ← mkFreshFVarId
  mkLetDecl fvarId n type val (nonDep := false) kind
  let fvar := mkFVar fvarId
  withNewFVar fvar type
  return fvarId

def withTemporaryLCtx [MonadLiftT MetaStateM n] [Monad n] (lctx : LocalContext) (localInsts : LocalInstances) (k : n α) : n α := do
  let initCtx ← getToContext
  let newCtx ← (Meta.Context.modifyLCtx initCtx lctx : MetaStateM _)
  let newCtx ← (Meta.Context.modifyLocalInstances newCtx localInsts : MetaStateM _)
  MetaState.setToContext newCtx
  let ret ← k
  MetaState.setToContext initCtx
  return ret

end Auto.MetaState
