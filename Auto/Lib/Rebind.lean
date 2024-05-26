import Lean

open Lean

/-
  Usage
  · Declare rebindable constant: `declare_rebindable <rebindable_func_name>`
  · Using rebindable constant: `eval_rebind% <rebindable_func_name>`
  · Re-bind rebindable constant:
    · Method 1:
      ```lean
      def <implementation_name> := ...

      attribute [rebind <rebindable_func_name>] <implementation_name>
      ```
    · Method 2:
      ```lean
      @[rebind <rebindable_func_name>]
      def <implementation_name> := ...
      ```
-/

structure RebindDescr where
  fnName : Name
  type : Expr
  impl? : Option Name
  deriving Inhabited

abbrev RebindState := NameMap RebindDescr

abbrev RebindExtension := SimpleScopedEnvExtension RebindDescr RebindState

def RebindState.addEntry (s : NameMap RebindDescr) (r : RebindDescr) : NameMap RebindDescr :=
  s.insert r.fnName r

initialize rebindExtension : RebindExtension ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := RebindState.addEntry
  }

def getRebinds (env : Environment) : NameMap RebindDescr := rebindExtension.getState env

def getRebind? (env : Environment) (fnName : Name) : Option RebindDescr :=
  (getRebinds env).find? fnName

syntax (name := rebindAttr) "rebind " ident : attr

initialize
  registerBuiltinAttribute {
    name := `rebindAttr
    descr := "add a rebind"
    add   := fun decl stx kind => do
      match stx with
      | `(attr| rebind $fnName) => withRef stx[0] do
        let fnName := fnName.getId.eraseMacroScopes
        let some r := getRebind? (← getEnv) fnName
          | throwError "No such rebindable function {fnName}"
        let some info := (← getEnv).find? decl | unreachable!
        unless info.levelParams.isEmpty do
          throwError "Declaration has level parameters, which is not supported."
        unless ← Meta.MetaM.run' <| Meta.isDefEq info.type r.type do
          throwError "Type is{indentD info.type}\nbut it must be{indentD r.type}"
        let r' := {r with impl? := decl}
        rebindExtension.add r' kind
      | _  => throwError "invalid `[rebind]` attribute"
  }

unsafe def RebindExtension.evalUnsafe
    {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]
    (α : Type) [Inhabited (m α)] (n : Name) : m α := do
  let some c := getRebind? (← getEnv) n
    | throwError "No such rebindable function {n}"
  let some impl := c.impl?
    | throwError "No implementation exists for rebind {n}"
  evalConst α impl

@[implemented_by RebindExtension.evalUnsafe]
opaque RebindExtension.eval
    {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]
    (α : Type) [Inhabited (m α)] (n : Name) : m α

elab "declare_rebindable " fnName:ident " : " type:term : command => do
  Elab.Command.runTermElabM fun args => do
    let type ← Elab.Term.elabType type
    Elab.Term.synthesizeSyntheticMVarsUsingDefault
    let type ← Meta.mkForallFVars (usedOnly := true) args type
    let type ← instantiateMVars type
    if type.hasMVar then
      throwError "Type contains metavariables{indentD type}"
    if type.hasLevelParam then
      throwError "Type contains level parameters{indentD type}"
    let r : RebindDescr :=
      { fnName := fnName.getId
        type := type
        impl? := none }
    rebindExtension.add r .global

syntax (name := evalRebindStx) "eval_rebind% " ident : term

@[term_elab evalRebindStx]
def elabEvalRebindStx : Elab.Term.TermElab
  | `(eval_rebind% $fnName) => fun expectedType? => do
    let some c := getRebind? (← getEnv) fnName.getId
      | throwError "No such rebindable function {fnName}"
    let stx ← `(RebindExtension.eval $(← Elab.Term.exprToSyntax c.type) $(quote fnName.getId))
    Elab.Term.elabTerm stx expectedType?
  | _ => fun _ => Elab.throwUnsupportedSyntax
