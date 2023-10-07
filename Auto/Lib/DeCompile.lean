import Lean
import Auto.Lib.ExprExtra
open Lean

namespace Auto

namespace ExprDeCompile

-- **TODO**:
-- 1: Support metavariables
--
-- Note that in this implementation, we treat all arguments
--   as explicit

structure Context where
  usedNames : HashSet String

structure State where
  binderNames : Array String := #[]
  curIdx : Nat := 0

abbrev ExprDeCompM := ReaderT Context (StateRefT State MetaM)

partial def withNewBinder (m : ExprDeCompM α) : ExprDeCompM (α × String) := do
  let bn := (← get).binderNames
  let ns := (← read).usedNames
  let mut nbn := #[]
  let mut idx := (← get).curIdx
  let mut nn := ""
  while true do
    nn := "x" ++ toString idx
    idx := idx + 1
    if !ns.contains nn then
      nbn := bn.push nn
      break
  modify (fun s => {s with binderNames := nbn, curIdx := idx})
  let ret ← m
  -- Do not reuse binder name, so do not revert curIdx
  modify (fun s => {s with binderNames := bn})
  return (ret, nn)

/--
  Reverse process of compiling string to `Expr`, similar to `toString`
  The `Expr` already has a `toString`, but that `toString` is
    very different from "decompiling" the `expr`
-/
private partial def exprDeCompileAux (final : Bool) (e : Expr) : ExprDeCompM String := do
  match e with
  | Expr.forallE _ d b _ =>
    let ds ← exprDeCompileAux final d
    let (bs, name) ← withNewBinder (exprDeCompileAux final b)
    return s!"(∀ ({name} : {ds}), {bs})"
  | Expr.lam _ d b _ =>
    let ds ← exprDeCompileAux final d
    let (bs, name) ← withNewBinder (exprDeCompileAux final b)
    return s!"(fun ({name} : {ds}) => {bs})"
  | Expr.mdata _ b => exprDeCompileAux final b
  | Expr.letE _ t v b _ =>
    let ts ← exprDeCompileAux final t
    let vs ← exprDeCompileAux final v
    let (bs, name) ← withNewBinder (exprDeCompileAux final b)
    return s!"(let {name} : {ts} := {vs}, {bs})"
  | Expr.app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConst ∧ !final then
      let expanded ← etaExpandConst f args.size
      let ret ← exprDeCompileAux true expanded
      return ret
    let fs ← exprDeCompileAux final f
    let argss ← args.mapM (exprDeCompileAux final)
    let argssC := String.intercalate " " argss.data
    return s!"({fs} {argssC})"
  | Expr.proj _ idx b =>
    let bs ← exprDeCompileAux final b
    return s!"({bs}.{idx})"
  | Expr.const name us =>
    if final then
      return constFinalDeComp name us
    else
      let expanded ← etaExpandConst e 0
      let ret ← exprDeCompileAux true expanded
      return ret
  | Expr.lit l =>
    match l with
    | .natVal l => return toString l
    | .strVal s => return toString s
  | Expr.sort l => return s!"Sort ({l})"
  | Expr.mvar .. => throwError "exprDeCompile :: Metavariable is not supported"
  | Expr.fvar f =>
    let some decl := (← getLCtx).find? f
      | throwError "Unknown free variable {e}"
    return decl.userName.toString
  | Expr.bvar n =>
    let bn := (← get).binderNames
    return bn[bn.size - n - 1]!
where 
  constFinalDeComp (name : Name) (us : List Level) :=
    if List.length us == 0 then
      "@" ++ name.toString
    else
      "@" ++ name.toString ++ ".{" ++
        String.intercalate ", " (us.map toString) ++ "}"
  etaExpandConst (cst : Expr) (appliedArgs : Nat) := do
    if !cst.isConst then
      throwError s!"exprDeCompile :: etaExpandConst received non-const {cst}"
    let some val := (← getEnv).find? cst.constName!
      | throwError s!"exprDeCompile :: Unknown identifier {cst.constName!}"
    let ty := val.type
    let lparams := val.levelParams
    let bs := Expr.forallBinders ty
    let extra := bs.size - appliedArgs
    let mut e := e
    for i in [0:extra] do
      e := .app e (.bvar (extra - i - 1))
    let bsU := bs[appliedArgs:bs.size].toArray.reverse
    for (_, ty, _) in bsU do
      e := .lam `_ (ty.instantiateLevelParams lparams cst.constLevels!) e .default
    return e

def levelCollectNames (l : Level) : StateT (HashSet String) MetaM Unit := do
  match l with
  | .zero => return
  | .succ l => levelCollectNames l
  | .mvar .. => return
  | .param n => modify (fun s => s.insert n.toString)
  | .max l1 l2 => levelCollectNames l1; levelCollectNames l2
  | .imax l1 l2 => levelCollectNames l1; levelCollectNames l2

def exprCollectNames (e : Expr) : StateT (HashSet String) MetaM Unit := do
  match e with
  | Expr.forallE _ d b _ => exprCollectNames d; exprCollectNames b
  | Expr.lam _ d b _ => exprCollectNames d; exprCollectNames b
  | Expr.mdata _ b => exprCollectNames b
  | Expr.letE _ t v b _ => exprCollectNames t; exprCollectNames v; exprCollectNames b
  | Expr.app f a => exprCollectNames f; exprCollectNames a
  | Expr.proj n _ b => do
      exprCollectNames b
      modify (fun s => s.insert n.toString)
  | Expr.const n us => do
      modify (fun s => s.insert n.toString)
      let _ ← us.mapM levelCollectNames
  | Expr.lit _ => return
  | Expr.sort l => levelCollectNames l
  | Expr.mvar .. => return
  | Expr.fvar f => 
    let some decl := (← getLCtx).find? f
      | throwError "Unknown free variable {e}"
    let name := decl.userName.toString
    modify (fun s => s.insert name)
  | Expr.bvar .. => return

end ExprDeCompile

def exprDeCompile (e : Expr) : MetaM String := do
  let names := (← (ExprDeCompile.exprCollectNames e).run {}).snd
  let res ← ((ExprDeCompile.exprDeCompileAux false e).run ⟨names⟩).run {}
  return res.fst

/- --Test

syntax (name := testDeComp) "#testDeComp" term : command

@[command_elab Auto.testDeComp]
def elabTestDeComp : Elab.Command.CommandElab := fun stx => do
  match stx with
  | `(command | #testDeComp $x:term) => Elab.Command.runTermElabM (fun _ => do
      let x ← Elab.Term.elabTerm x none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
      let e ← instantiateMVars x
      IO.println (← exprDeCompile e))
  | _ => Elab.throwUnsupportedSyntax

#testDeComp (fun (x y : Nat) => Nat.add x y)
#check (fun (x0 : @Nat) => (fun (x1 : @Nat) => (@Nat.add x0 x1)))
#testDeComp (fun (x : ∀ (α β : Type) (f : α → β) (x : α), β) (α β : Type) (f : α → β) (u : α) => x α β f u)
#check (fun (x5 : (∀ (x0 : Sort (1)), (∀ (x1 : Sort (1)), (∀ (x3 : (∀ (x2 : x0), x1)), (∀ (x4 : x0), x1))))) => (fun (x6 : Sort (1)) => (fun (x7 : Sort (1)) => (fun (x9 : (∀ (x8 : x6), x7)) => (fun (x10 : x6) => (x5 x6 x7 x9 x10))))))
#testDeComp 2
#check ((fun (x0 : Sort (1)) => (fun (x1 : @Nat) => (fun (x2 : (@OfNat.{0} x0 x1)) => (@OfNat.ofNat.{0} x0 x1 x2)))) @Nat 2 ((fun (x3 : @Nat) => (@instOfNatNat x3)) 2))
universe u
#testDeComp @OfNat.ofNat.{u}
#check (fun (x0 : Sort (u+1)) => (fun (x1 : @Nat) => (fun (x2 : (@OfNat.{u} x0 x1)) => (@OfNat.ofNat.{u} x0 x1 x2))))
#testDeComp @Nat.rec.{u}
#check (rfl : @Nat.rec.{u} = fun (x1 : (∀ (x0 : @Nat), Sort (u))) => (fun (x2 : (x1 @Nat.zero)) => (fun (x5 : (∀ (x3 : @Nat), (∀ (x4 : (x1 x3)), (x1 (@Nat.succ x3))))) => (fun (x6 : @Nat) => (@Nat.rec.{u} x1 x2 x5 x6)))))
#testDeComp fun {motive : Nat → Sort u} (t : Nat) (F_1 : (t : Nat) → @Nat.below.{u} motive t → motive t) =>
  (@Nat.rec.{max 1 u} (fun (t : Nat) => PProd.{u, max 1 u} (motive t) (@Nat.below.{u} motive t))
      (@PProd.mk.{u, max 1 u} (motive Nat.zero) PUnit.{max 1 u} (F_1 Nat.zero PUnit.unit.{max 1 u})
        PUnit.unit.{max 1 u})
      (fun (n : Nat) (n_ih : PProd.{u, max 1 u} (motive n) (@Nat.below.{u} motive n)) =>
        @PProd.mk.{u, max 1 u} (motive (Nat.succ n))
          (PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive n) (@Nat.below.{u} motive n)) PUnit.{max 1 u})
          (F_1 (Nat.succ n)
            (@PProd.mk.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive n) (@Nat.below.{u} motive n)) PUnit.{max 1 u} n_ih
              PUnit.unit.{max 1 u}))
          (@PProd.mk.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive n) (@Nat.below.{u} motive n)) PUnit.{max 1 u} n_ih
            PUnit.unit.{max 1 u}))
      t).1
#check (fun (x1 : (∀ (x0 : @Nat), Sort (u))) => (fun (x2 : @Nat) =>
  (fun (x5 : (∀ (x3 : @Nat), (∀ (x4 : (@Nat.below.{u} x1 x3)), (x1 x3))))
  => (@PProd.fst.{u, max 1 u} (x1 x2) (@Nat.below.{u} x1 x2)
  (@Nat.rec.{max 1 u} (fun (x6 : @Nat) => (@PProd.{u, max 1 u} (x1 x6)
  (@Nat.below.{u} x1 x6))) (@PProd.mk.{u, max 1 u} (x1 @Nat.zero)
  @PUnit.{max 1 u} (x5 @Nat.zero @PUnit.unit.{max 1 u})
  @PUnit.unit.{max 1 u}) (fun (x7 : @Nat) => (fun (x8 : (@PProd.{u, max 1 u}
  (x1 x7) (@Nat.below.{u} x1 x7))) => (@PProd.mk.{u, max 1 u} (x1
  (@Nat.succ x7)) (@PProd.{max 1 u, max 1 u} (@PProd.{u, max 1 u} (x1 x7)
  (@Nat.below.{u} x1 x7)) @PUnit.{max 1 u}) (x5 (@Nat.succ x7)
  (@PProd.mk.{max 1 u, max 1 u} (@PProd.{u, max 1 u} (x1 x7) (@Nat.below.{u}
  x1 x7)) @PUnit.{max 1 u} x8 @PUnit.unit.{max 1 u})) (@PProd.mk.{max 1 u,
  max 1 u} (@PProd.{u, max 1 u} (x1 x7) (@Nat.below.{u} x1 x7)) @PUnit.{max
  1 u} x8 @PUnit.unit.{max 1 u})))) x2)))))

--/

end Auto