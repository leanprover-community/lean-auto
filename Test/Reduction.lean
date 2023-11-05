import Auto.Lib.ExprExtra
import Auto.Lib.BinTree

set_option lazyReduce.printTime true
set_option maxRecDepth 50000 in
#lazyReduce List.map (fun n => (List.range (1000 + n)).length) (List.range 10)

set_option maxRecDepth 50000 in
#lazyReduce (List.range 10000).length

#check 2

#check Classical.propDecidable
#check fun (α : Type) (i : LE α) (x y : α) => x <= y
#check trans
#check LE.le

def casting (f g : Nat → Type) (x : ∀ n, f n) (H : ∀ n, f n = g n) : (∀ n, g n) :=
  let heq : f = g := funext (fun n => H n);
  heq ▸ x

#eval casting (fun n => Nat) (fun n => match n with | 0 => Nat | _ => Nat) (fun n => n)
  (fun n => by cases n <;> rfl) 21

def tst1₁ (x : α) : True :=
  let a := inferInstanceAs (Inhabited Nat);
  let b := a.default
  True.intro

open Auto

def simplebt (x : Nat) (n : Nat) : BinTree Nat :=
  match n with
  | 0 => .leaf
  | n' + 1 => .node (simplebt (2 * x) n') (.some x) (simplebt (2 * x + 1) n')

def foldl' (f : α → β → α) (init : α) : BinTree β → α
| .leaf => init
| .node l x r =>
  let lf := foldl' f init l
  let mf :=
    match x with
    | .some x => f lf x
    | .none => lf
  match mf with
  | mf => foldl' f mf r

def foldAgain (bt : BinTree Nat) := foldl' (fun bt entry => bt.insert entry entry) BinTree.leaf bt

/-
def sdk : (foldAgain (simplebt 1 12)).get? 100 = Option.some 100 := Eq.refl (Option.some 100)

#check (simplebt 2 10)

#eval (foldAgain (simplebt 1 12)).get? 100
-/

#check 2
