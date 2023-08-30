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

-- Not all `MetaM` operations will succeed
def runMetaM (n : MetaM α) : MetaStateM α := do
  let s ← get
  let (ret, s') ← n.run s.toContext s.toState
  setToState s'
  return ret

def runAtMetaM (n : MetaStateM α) : MetaM (α × Meta.Context) := do
  let s ← get
  let c ← read
  let (ret, sc') ← n.run ⟨s, c⟩
  set sc'.toState
  return (ret, sc'.toContext)

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