import Auto.Lib.ExprExtra
import Auto.Lib.BinTree
import Auto.Lib.TreeList

set_option lazyReduce.printTime true
set_option maxRecDepth 10000 in
#lazyReduce List.map (fun n => (List.range (3000 + n)).length) (List.range 10)

/-
set_option maxRecDepth 20000 in
#lazyReduce (List.range 5000).length
-/

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
  let a : Inhabited Nat := inferInstance;
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
def sdk : (foldAgain (simplebt 1 12))[100]? = Option.some 100 := Eq.refl (Option.some 100)

#check (simplebt 2 10)

#eval (foldAgain (simplebt 1 12))[100]?
-/

def l₁ : CBTreeList Nat 1 .f := .f 1
def l₂ : CBTreeList Nat 2 .f := (l₁.append l₁).snd
def l₃ : CBTreeList Nat 5 .f := ((l₂.append l₂).snd.append l₁).snd
def l₄ : CBTreeList Nat 10 .f := (l₃.append l₃).snd
def l₅ : CBTreeList Nat 20 .f := (l₄.append l₄).snd
def l₆ : CBTreeList Nat 40 .f := (l₅.append l₅).snd
def l₇ : CBTreeList Nat 80 .f := (l₆.append l₆).snd
def l₈ : CBTreeList Nat 160 .f := (l₇.append l₇).snd
set_option maxRecDepth 4000
def l₉ : CBTreeList Nat 320 .f := (l₈.append l₈).snd
def l₁₀ : CBTreeList Nat 640 .f := (l₉.append l₉).snd
def l₁₁ : CBTreeList Nat 1280 .f := (l₁₀.append l₁₀).snd

-- set_option maxRecDepth 10000
-- set_option maxHeartbeats 2000000
-- def cbt500 : CBTreeList Nat 2000 .p :=
--   (List.foldl TreeList.push TreeList.empty (List.range 2000)).data

#check 2
