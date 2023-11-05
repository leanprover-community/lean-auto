import Auto.Tactic

set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

set_option auto.smt true

section Enum

  example (x y : Unit) : x = y ∧ x = () := by auto

  example (x y : Empty) : x = y := by auto

  example (_ : ¬ (∀ x y : Empty, False)) : False := by auto

  private inductive Color where
    | red
    | green
    | ultraviolet

  example (x y z t : Color) : x = y ∨ x = z ∨ x = t ∨ y = z ∨ y = t ∨ z = t := by auto

end Enum

section NonRecursive

  example (x y : α) (_ : Option.some x = Option.some y) : x = y := by auto

  -- **TODO**:
  -- Requires higher-order to first-order translation
  set_option trace.auto.printLemmas true in
  example (x : Option α) : Option.orElse x (fun _ => Option.none) = x := by auto

  set_option trace.auto.lamReif.printResult true
  example (x : α × β) : x = (Prod.fst x, Prod.snd x) := by
    auto

  example (f : α × β → α) (h : f = Prod.fst) : f (a, b) = a := by
    auto

end NonRecursive

section Recursive

  -- SMT solver is now able to recognize inductive types
  set_option auto.lamReif.prep.def false
  set_option trace.auto.lamReif.printResult true
  example (x y : α) : [x] ++ [y] = [x, y] := by
    -- Invoke definition unfolding
    have h : ∀ (x y : List α), x ++ y = x.append y := fun _ _ => rfl
    auto [h] d[List.append]

  -- SMT solver times out on the following problem:
  -- set_option auto.redMode "all" in
  -- example (x y z : List Nat) : (x ++ y) ++ z = x ++ (y ++ z) := by
  --   auto d[List.append]

  mutual

    private inductive tree where
      | leaf : Nat → tree
      | node : treelist → tree

    private inductive treelist where
      | nil : treelist
      | cons : tree → treelist → treelist

  end

  set_option trace.auto.lamReif.printResult true
  example (x : tree) : (∃ (y : treelist), x = .node y) ∨ (∃ y, x = .leaf y) := by
    auto

end Recursive

section Mixed

  example (x y : α) : List.get? [x, y] 1 = .some y := by
    auto d[List.get?]

  example (x : α) : List.head? [x] = .some x := by
    have h₁ : List.head? (α := α) [] = .none := rfl
    have h₂ : ∀ (x : α) (ys : _), List.head? (x :: ys) = .some x := fun _ _ => rfl
    auto

  example (x : α) (y : List α) : List.head? (x :: y) = .some x := by
    have h₁ : List.head? (α := α) [] = .none := rfl
    have h₂ : ∀ (x : α) (ys : _), List.head? (x :: ys) = .some x := fun _ _ => rfl
    auto

  -- **TODO**: Did not get desired definitional equation
  example (x : α) : List.head? [x] = .some x := by
    auto d[List.head?]

  inductive IndCtor₁ where
    | ctor : Nat → Bool → IndCtor₁

  example
    (f : Nat → Nat → Bool → IndCtor₁)
    (h₁ : IndCtor₁.ctor = f 1) (h₂ : IndCtor₁.ctor = f 2) : f 1 = f 2 := by
    auto

end Mixed

section Empty

  def Empty' := Empty

  example : (∃ (x : Empty), True) := by
    auto

  -- The translation to smt solver is unsound.
  -- SMT-LIB assume that all types are inhabited, while in DTT it's not.
  example : (∃ (x : Empty'), True) := by
    auto

end Empty

/- Issues to be solved:
  1. Unable to deal with inductive families, like `Vector`
  2. Fails if constructor is dependent/polymorphic after monomorphization,
     for example `Fin`
-/
