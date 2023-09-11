import Auto.Lib.ExprExtra

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