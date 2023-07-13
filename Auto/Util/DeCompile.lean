import Lean
import Auto.Util.ExprExtra
open Lean

namespace Auto.Util

namespace ExprDeCompile

-- **TODO**: Support metavariables, Retain implicit binder information

structure Context where
  usedNames : HashSet String

structure State where
  binderNames : Array String := #[]
  curIdx : Nat := 0

abbrev ExprDeCompM := ReaderT Context (StateRefT State CoreM)

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

-- Reverse process of compiling string to `Expr`, similar to `toString`
-- The `Expr` already has a `toString`, but that `toString` is
--   very different from "decompiling" the `expr`
partial def exprDeCompileAux (final : Bool) (e : Expr) : ExprDeCompM String := do
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
    let fs ← exprDeCompileAux final f
    let argss ← args.mapM (exprDeCompileAux final)
    let argssC := String.intercalate " " argss.data
    return s!"({fs} {argssC})"
  | Expr.proj _ idx b =>
    let bs ← exprDeCompileAux final b
    return s!"({bs}.{idx})"
  | Expr.const name us =>
    if final then
      if List.length us == 0 then
        return "@" ++ name.toString
      else
        return "@" ++ name.toString ++ ".{" ++
          String.intercalate ", " (us.map toString) ++ "}"
    else
      let some val := (← getEnv).find? name
        | throwError "exprDeCompile : Unknown identifier {name}"
      let ty := val.type
      let lparams := val.levelParams
      let bs := Expr.binders ty
      let extra := bs.size
      let mut e := e
      for i in [0:extra] do
        e := .app e (.bvar (extra - i - 1))
      for (_, ty, _) in bs.reverse do
        e := .lam `_ (ty.instantiateLevelParams lparams us) e .default
      let ret ← exprDeCompileAux true e
      return ret
  | Expr.lit l =>
    match l with
    | .natVal l => return toString l
    | .strVal s => return toString s
  | Expr.sort l => return s!"Sort ({l})"
  | Expr.mvar .. => throwError "exprDeCompile : Metavariable is not supported"
  | Expr.fvar .. => throwError "exprDeCompile : Free variable is not supported"
  | Expr.bvar n =>
    let bn := (← get).binderNames
    return bn[bn.size - n - 1]!

def levelCollectNames (l : Level) : StateM (HashSet String) Unit := do
  match l with
  | .zero => return
  | .succ l => levelCollectNames l
  | .mvar .. => return
  | .param n => modify (fun s => s.insert n.toString)
  | .max l1 l2 => levelCollectNames l1; levelCollectNames l2
  | .imax l1 l2 => levelCollectNames l1; levelCollectNames l2

def exprCollectNames (e : Expr) : StateM (HashSet String) Unit := do
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
  | Expr.fvar .. => return
  | Expr.bvar .. => return

end ExprDeCompile

def exprDeCompile (e : Expr) : CoreM String := do
  let names := ((ExprDeCompile.exprCollectNames e).run {}).snd
  let res ← ((ExprDeCompile.exprDeCompileAux false e).run ⟨names⟩).run {}
  return res.fst

/- --Test

syntax (name := testDeComp) "#testDeComp" term : command

@[command_elab Auto.Util.testDeComp]
def elabTestDeComp : Elab.Command.CommandElab := fun stx => do
  match stx with
  | `(command | #testDeComp $x:term) => do
    let e ← Elab.Command.liftTermElabM (do
      let x ← Elab.Term.elabTerm x none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars x)
    IO.println (← Elab.Command.liftCoreM (exprDeCompile e))
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
 (fun (x8 : (∀ (x3 : @Nat), (∀ (x7 : ((fun (x5 : (∀ (x4 : @Nat), Sort (u)))
  => (fun (x6 : @Nat) => (@Nat.below.{u} x5 x6))) x1 x3)), (x1 x3)))) => 
  ((fun (x9 : Sort (u)) => (fun (x10 : Sort (max 1 u)) => (fun (x11 : 
  (@PProd.{u, max 1 u} x9 x10)) => (@PProd.fst.{u, max 1 u} x9 x10 x11))))
  (x1 x2) ((fun (x13 : (∀ (x12 : @Nat), Sort (u))) => (fun (x14 : @Nat) =>
  (@Nat.below.{u} x13 x14))) x1 x2) ((fun (x16 : (∀ (x15 : @Nat), 
  Sort (max 1 u))) => (fun (x17 : (x16 @Nat.zero)) => (fun (x20 : (∀
  (x18 : @Nat), (∀ (x19 : (x16 x18)), (x16 (@Nat.succ x18))))) => (fun (x21
  : @Nat) => (@Nat.rec.{max 1 u} x16 x17 x20 x21))))) (fun (x22 : @Nat) =>
  ((fun (x23 : Sort (u)) => (fun (x24 : Sort (max 1 u)) => (@PProd.{u, max 1
  u} x23 x24))) (x1 x22) ((fun (x26 : (∀ (x25 : @Nat), Sort (u))) => (fun
  (x27 : @Nat) => (@Nat.below.{u} x26 x27))) x1 x22))) ((fun (x28 : Sort (u))
  => (fun (x29 : Sort (max 1 u)) => (fun (x30 : x28) => (fun (x31 : x29) =>
  (@PProd.mk.{u, max 1 u} x28 x29 x30 x31))))) (x1 @Nat.zero) @PUnit.{max 1
  u} (x8 @Nat.zero @PUnit.unit.{max 1 u}) @PUnit.unit.{max 1 u}) (fun (x32 :
  @Nat) => (fun (x38 : ((fun (x33 : Sort (u)) => (fun (x34 : Sort (max 1 u))
  => (@PProd.{u, max 1 u} x33 x34))) (x1 x32) ((fun (x36 : (∀ (x35 : @Nat),
  Sort (u))) => (fun (x37 : @Nat) => (@Nat.below.{u} x36 x37))) x1 x32))) =>
  ((fun (x39 : Sort (u)) => (fun (x40 : Sort (max 1 u)) => (fun (x41 : x39) 
  => (fun (x42 : x40) => (@PProd.mk.{u, max 1 u} x39 x40 x41 x42))))) 
  (x1 ((fun (x43 : @Nat) => (@Nat.succ x43)) x32)) ((fun (x44 : Sort 
  (max 1 u)) => (fun (x45 : Sort (max 1 u)) => (@PProd.{max 1 u, max 1 u} 
  x44 x45))) ((fun (x46 : Sort (u)) => (fun (x47 : Sort (max 1 u)) => 
  (@PProd.{u, max 1 u} x46 x47))) (x1 x32) ((fun (x49 : (∀ (x48 : @Nat), 
  Sort (u))) => (fun (x50 : @Nat) => (@Nat.below.{u} x49 x50))) x1 x32)) 
  @PUnit.{max 1 u}) (x8 ((fun (x51 : @Nat) => (@Nat.succ x51)) x32) ((fun 
  (x52 : Sort (max 1 u)) => (fun (x53 : Sort (max 1 u)) => (fun (x54 : x52) 
  => (fun (x55 : x53) => (@PProd.mk.{max 1 u, max 1 u} x52 x53 x54 x55))))) 
  ((fun (x56 : Sort (u)) => (fun (x57 : Sort (max 1 u)) => (@PProd.{u, max 
  1 u} x56 x57))) (x1 x32) ((fun (x59 : (∀ (x58 : @Nat), Sort (u))) => (fun 
  (x60 : @Nat) => (@Nat.below.{u} x59 x60))) x1 x32)) @PUnit.{max 1 u} x38 
  @PUnit.unit.{max 1 u})) ((fun (x61 : Sort (max 1 u)) => (fun (x62 : Sort 
  (max 1 u)) => (fun (x63 : x61) => (fun (x64 : x62) => (@PProd.mk.{max 1 u, 
  max 1 u} x61 x62 x63 x64))))) ((fun (x65 : Sort (u)) => (fun (x66 : Sort 
  (max 1 u)) => (@PProd.{u, max 1 u} x65 x66))) (x1 x32) ((fun (x68 : (∀ 
  (x67 : @Nat), Sort (u))) => (fun (x69 : @Nat) => (@Nat.below.{u} x68 x69)))
  x1 x32)) @PUnit.{max 1 u} x38 @PUnit.unit.{max 1 u})))) x2)))))

--/

end Auto.Util