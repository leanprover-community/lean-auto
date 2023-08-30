import Lean
import Auto.Lib.MonadUtils
open Lean

namespace Auto.MetaState

structure State extends Meta.State, Meta.Context

structure SavedState where
  core       : Core.State
  meta       : State

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
  return { core := (← getThe Core.State), meta := (← get) }

def SavedState.restore (b : SavedState) : MetaStateM Unit := do
  Core.restore b.core
  modify fun s => { s with mctx := b.meta.mctx, zetaFVarIds := b.meta.zetaFVarIds, postponed := b.meta.postponed }

instance : MonadBacktrack SavedState MetaStateM where
  saveState      := MetaState.saveState
  restoreState s := s.restore

#genMonadState MetaStateM

def runMetaM (n : MetaM α) : MetaStateM α := do
  let s ← get
  let (ret, s') ← n.run s.toContext s.toState
  setToState s'
  return ret

def runMetaMWithFVarsImp (ms : State) (fvars : Array FVarId) (k : MetaM α) : MetaM α := do
  let mut lctx := (← read).lctx
  for fid in fvars do
    match ms.lctx.findFVar? (.fvar fid) with
    | .some decl =>
      match decl with
      | .cdecl _ fvarId userName type bi kind =>
        lctx := lctx.mkLocalDecl fvarId userName type bi kind
      | .ldecl _ fvarId userName type value nonDep kind =>
        lctx := lctx.mkLetDecl fvarId userName type value nonDep kind
    | .none => throwError "runMetaMWithFVars :: Unknown free variable {Expr.fvar fid}"
  withReader (fun ctx => {ctx with lctx := lctx}) k

def runMetaMWithFVars [MonadControlT MetaM n] [Monad n] (ms : State) (fvars : Array FVarId) (k : n α) : n α :=
  Meta.mapMetaM (fun k => runMetaMWithFVarsImp ms fvars k) k

def mkLocalDecl (fvarId : FVarId) (userName : Name) (type : Expr)
  (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := LocalDeclKind.default) : MetaStateM Unit := do
  let ctx ← getToContext
  let lctx := ctx.lctx
  setToContext ({ctx with lctx := lctx.mkLocalDecl fvarId userName type bi kind})

def mkLetDecl (fvarId : FVarId) (userName : Name) (type value : Expr)
  (nonDep : Bool := false) (kind : LocalDeclKind := default) : MetaStateM Unit := do
  let ctx ← getToContext
  let lctx := ctx.lctx
  setToContext ({ctx with lctx := lctx.mkLetDecl fvarId userName type value nonDep kind})

end Auto.MetaState