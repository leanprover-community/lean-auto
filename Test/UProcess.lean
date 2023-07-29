import Auto.Translation.Lift

set_option pp.universes true
namespace Auto

axiom f : ∀ (α : Type) (β : α → Type) (x : α), β x

noncomputable def f.Lift.{u} := fun
  (α : GLift.{2, u + 1} Type) (β : GLift (α.down) → Type) (x : GLift (α.down)) =>
  f α.down (fun x => β (GLift.up x)) x.down

noncomputable def f.Lift.check.{u} := fun (α : Type) (β : α → Type) (x : α) =>
  f.Lift.{u} (GLift.up α) (fun x => GLift (β x.down)) (GLift.up x)

#reduce f.Lift.check

set_option pp.all true in
#reduce (fun x : Nat × Nat => x.fst)

#check @Nat.rec

/-
@Nat.rec : {motive : Nat → Sort u_1} →
  motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
-/

def Nat.succ.Lift.{u} := fun (n : GLift.{1, u} Nat) => GLift.up.{1, u} (Nat.succ n.down)

noncomputable def Nat.rec.Lift.{u, v} := fun
  (motive' : GLift.{1, max u v + 1} Nat → GLift.{u + 1, max u v + 1} (Sort u))
  (H₀' : GLift (motive' (GLift.up Nat.zero)).down)
  (Hsucc' : ∀ (n : GLift Nat), GLift (motive' n).down → GLift (motive' (Nat.succ.Lift n)).down)
  (t' : GLift.{1, max u v + 1} Nat) =>
  @Nat.rec.{u}
    (motive:=fun n => (motive' (GLift.up n)).down)
    H₀'.down
    (fun n ih => (Hsucc' (GLift.up n) (GLift.up ih)).down)
    t'.down

axiom g : ∀ (u : (Nat → Nat) → Nat), Nat

noncomputable def g.Lift.{u} := fun (u : (GLift.{1, u} Nat → GLift Nat) → GLift Nat) =>
  GLift.up.{1, u} (g (fun f => GLift.down (u (fun x => GLift.up (f x.down)))))

end Auto