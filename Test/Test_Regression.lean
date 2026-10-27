import Auto.Tactic

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"
-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport-lams"
set_option auto.tptp.zeport.path "/home/indprinciples/Programs/zipperposition/portfolio"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"

set_option auto.tptp true
set_option trace.auto.tptp.printProof true

-- emulate native solver
set_option auto.native true
attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

-- Manual Check

section ManualCheck

  example : True := by (fail_if_success auto 👍); auto
  private def sorryChk : False := by auto 👎
  #print axioms sorryChk

  set_option auto.lamReif.prep.def false

  -- In `Checker Statistics`, check that the `assertions` field is `1`
  set_option auto.optimizeCheckerProof true in
  set_option trace.auto.buildChecker true in
  example (h₁ : False) (h₂ : a = b) : False := by auto [h₁, h₂]

  -- In `Checker Statistics`, check that the `assertions` field is `4`
  set_option auto.optimizeCheckerProof false in
  set_option trace.auto.buildChecker true in
  example (h₁ : False) (h₂ : a = b) : False := by auto [h₁, h₂]

  -- In `Checker Statistics`, check that the `assertions` field is `4`
  set_option auto.optimizeCheckerProof true in
  set_option trace.auto.buildChecker true in
  example (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a = c := by
    auto [h₁, h₂, h₃]

  -- In `Checker Statistics`, check that the `assertions` field is `5`
  set_option auto.optimizeCheckerProof false in
  set_option trace.auto.buildChecker true in
  example (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a = c := by
    auto [h₁, h₂, h₃]

end ManualCheck

-- Inhabitation Reasoning

section Inhabitation

  set_option trace.auto.lamReif.printProofs true
  set_option trace.auto.lamReif.printResult true

  example [Inhabited α] (h : ∀ (x : α), True) : ∃ (x : α), True := by
    auto

  example [Nonempty α] (h : ∀ (x : α), True) : ∃ (x : α), True := by
    auto

  example (h : ∀ (x : Nat), x = x) : ∃ (x : Nat), x = x := by
    auto

  example (x : α) (y : β) (h : ∀ (x : α) (y : β), x = x ∧ y = y) :
     ∃ (x : α) (y : β), x = x ∧ y = y := by
    auto

  example (a : α) (p : α → Prop) : (∃ x, p x → r) ↔ ((∀ x, p x) → r) := by
    auto

  example (a : α) (p : α → Prop) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
    auto

  -- `OK Nat → OK Nat` should be blocked for being trivial
  example (OK : Type → Type)
    (inh : ∀ (α : Type), OK α → OK α)
    (h : ∀ (x : OK Nat), x = x) : 1 = 1 := by
    auto

  -- Either `inh₁` or `inh₂` should be blocked for being redundant
  example (OK₁ OK₂ : Type → Type)
    (inh₁ : ∀ (α : Type), OK₁ α → OK₂ α)
    (inh₂ : ∀ (α : Type), OK₁ α → OK₁ α → OK₂ α)
    (h : OK₁ Nat → ∀ (x : OK₂ Nat), x = x) : 1 = 1 := by
    auto

end Inhabitation

-- Monomorphization

set_option auto.redMode "instances" in
example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  mono [List.append_assoc, List.map_append];
  intros; sorry

example
  (h : ∀ (α : Type u) (as bs cs : List α), (as ++ bs) ++ cs ≠ as ++ (bs ++ cs) → False)
  {α : Type u} (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  auto

section MonomorphizationWierdExample

  def List.directZip : {α : Type u} → List α → {β : Type v} → List β → List (α × β)
    | _, [], _, []   => []
    | _, [], _, _::_ => []
    | _, _::_, _, [] => []
    | _, x::xs, _, y::ys => (x,y) :: directZip xs ys

  def prod_eq₁' : ∀ (x : α) (y : β), Prod.fst (x, y) = x := by auto
  def prod_eq₂' : ∀ (x : α) (y : β), Prod.snd (x, y) = y := by auto

  set_option auto.mono.saturationThreshold 800 in
  example
    (α : Type u)
    (as bs cs ds : List α)
    (hab : as.length = bs.length) (hbc : bs.length = cs.length) (hcd : cs.length = ds.length)
    (h : ∀ (δ : Type u) (f₁ f₂ f₃ f₄ : δ → α) (xs : List δ),
      xs.map f₁ = as ∧ xs.map f₂ = bs ∧ xs.map f₃ = cs ∧ xs.map f₄ = ds → False) : False := by
    mono [h, hab, prod_eq₁', prod_eq₂'] d[List.length, List.directZip, List.map]
    intros; sorry

end MonomorphizationWierdExample

-- Data Structure Robustness

section DSRobust

  -- Duplicated reified fact
  example (h₁ : False) (h₂ : False) : False := by auto [h₁, h₂]
  example (α : Prop) (h₁ : α) (h₂ : α) (h₃ : α) : α := by auto
  example (h₁ : ¬ True) : True := by auto [h₁]

  -- Result of ChkStep coincides with input term
  example (h₁ : False → False) (h₂ : False) : True := by auto [h₁, h₂]

end DSRobust

-- Tactic elaboration

example : True := by auto []
example : True := by auto d[]
example : True := by auto u[]
example : True := by auto [] d[] u[]
example : True := by auto [] u[] d[]
example : True := by first | auto 👍| exact True.intro
example : True := by auto 👎

-- Defeq Lemma collection

section CollectLemma

  set_option trace.auto.printLemmas true
  set_option auto.redMode "instances"
  example : (∀ (xs ys zs : List α), xs ++ ys ++ zs = xs ++ (ys ++ zs)) := by
    intro xs; induction xs <;> auto [*] d[List.append]

  set_option auto.redMode "instances" in
  example : (∀ (m n k : Nat), m + n + k = m + (n + k)) := by
    intros m n k; revert m n; induction k <;> auto [*] d[Nat.add]

end CollectLemma

-- Skolemization

section Skolemization

  set_option trace.auto.lamReif.printProofs true

  example (p : α → Prop) (h₁ : ∃ x, p x) : ∃ x, p x :=
    by auto

  example (p q : (α → β) → Prop) (h₁ : ∃ (f : _) (g : α), p f) (h₂ : ∀ f, p f → q f) : ∃ f, q f :=
    by auto

  example (p : α → Prop) (q : (β → γ) → Prop) (h₁ : ∃ f, p f) (h₂ : ∃ f, q f) : ∃ f g, p f ∧ q g :=
    by auto

  example (p : α → β → Prop) (h : ∀ (x : α), ∃ y, p x y) : ∃ (f : α → β), ∀ x, p x (f x) :=
    by auto

  example (p : α → β → γ → Prop) (h : ∀ (x : α) (y : β), ∃ z, p x y z) :
    ∃ (f : α → β → γ), ∀ x y, p x y (f x y) :=
    by auto

  example (p : α → β → γ → δ → Prop) (h : ∀ (x : α), ∃ (y : β), ∀ (z : γ), ∃ (t : δ), p x y z t) :
    ∃ (f : α → β) (g : α → γ → δ), ∀ x z, p x (f x) z (g x z) :=
    by auto

  example (p : α → (β → γ) → Prop) (h : ∀ x, ∃ y, p x y) : ∃ (f : _ → _), ∀ x, p x (f x) :=
    by auto

  example (p : α → Prop) (h₁ : ∃ (_ : α), p x) (h₂ : p x) : p x :=
    by auto

  example (p : α → Prop)
    (h₁ : ∃ (_ _ : β) (_ _ : γ), p x) (h₂ : ∃ (_ _ : β), p x) : p x :=
    by auto

end Skolemization

-- Abstract complicated dependent types to free variables

section DepAbst

  example (f : ∀ (α : Type), α → α) : f = f :=
    by auto

  example (f₁ f₂ : ∀ (α : Type), α → α) : f₁ = f₂ → f₂ = f₁ :=
    by auto

  set_option auto.mono.ignoreNonQuasiHigherOrder true in
  example (g : Type → Type) (f : ∀ (α : Type), g α) : f = f :=
    by auto

  example : @HAdd.hAdd = @HAdd.hAdd :=
    by auto

end DepAbst

-- Extensionalization

section Extensionalization

  set_option trace.auto.lamReif.printProofs true

  example (f g : Nat → Nat) (H : ∀ x, f x = g x) : f = g := by
    auto

  example (f g : (α → α) → β → α) (H : ∀ x, f x = g x) : f = g := by
    auto

end Extensionalization

-- Constant unfolding

section UnfoldConst

  def c₁ := 2
  def c₂ := c₁

  example : c₁ = 2 := by auto
  example : c₂ = 2 := by auto
  example : c₂ = 2 := by auto
  example : c₂ = 2 := by auto
  example : c₂ = 2 := by auto
  example (h : c₃ = c₁) : c₃ = 2 := by auto
  example : let c := 2; c = 2 := by auto

  example : True := by auto d[Nat.rec]

  def not' (b : Bool) :=
    match b with
    | true => false
    | false => true

  example : ∀ b, (not' b) = true ↔ b = false := by
    auto u[not', not'.match_1] d[Bool.rec]

  example (x : α) : List.head? [x] = .some x := by
    have list_head_unfold : @List.head? α = (fun x =>
      @List.casesOn α (fun x => (fun x => Option α) x) x ((fun _ => @none α) Unit.unit) fun head tail =>
        (fun a tail => @some α a) head tail) := by sorry
    auto [list_head_unfold] d[List.rec]

end UnfoldConst

-- Definitional Equality from Constant Instances

section ConstInstDefEq

  -- Effectively disable `termLikeDefEq`
  set_option auto.mono.termLikeDefEq.mode "reducible"

  def Nat.add₁ := Nat.add

  example : Nat.add₁ = Nat.add := by
    auto

  def Nat.add₂ {α β γ} (_ : α) (_ : β) (_ : γ) (u v : Nat) (_ : δ) := Nat.add u v

  example (x : α) (y : β) (z : γ) (t : δ) : Nat.add₂ x y z n m t = Nat.add n m := by
    auto

  example (x y : Int) (xs ys : List α) : x + y = Int.add x y ∧ xs ++ ys = List.append xs ys := by
    auto

  opaque mpop₁ {α} [Mul α] : α → α → α := fun _ => id
  def mpop₂ := @mpop₁

  /-
    To solve this problem, Lean-auto must succeed in doing all of
      the following steps consecutively
    · Instantiate `α` in `h` by unifying the `@op α` in `h`
      with the `@op α` in the goal.
    · The `[inst : Mul α]` in `h` is instantiated by `Lemma.monomorphic?`
    · The constant instance `@mpop₁ α inst` is collected and processed
    · During constant instance definitional equality production
      `@mpop₁ α inst` is matched with `@mpop₂ α inst` by `Expr.instanceOf?`
  -/
  example
    (α : Type)
    (op : ∀ {α}, α → α → α)
    (h : ∀ α [inst : Mul α] (x y : α), op x y = mpop₁ x y) :
    ∀ α [inst : Mul α] (x y : α), op x y = mpop₂ x y := by
    auto

end ConstInstDefEq

-- Definitional Equality from Term-like expressions

section TermLikeDefEq

  set_option auto.tptp false
  example (h : List.append [1, 2] [3, 4] = [2, 3]) : [1, 2, 3, 4] = [2, 3] := by
    auto

end TermLikeDefEq

-- First Order

example : True := by
  auto [True.intro]

example (a b : Prop) : a ∨ b ∨ ¬ a := by
  auto

example (a b : Nat) (f : Nat → Nat)
 (eqNat : Nat → Nat → Prop) (H : eqNat (f a) (f b)) : True := by
  auto [H]

example {α β : Type} (a : α) (b : β) (H : b = b) : a = a := by
  auto [H]

example (a : Nat) (f : Nat → Nat) (H : ∀ x, f x = x) :
  f x = f (f (f (f (f (f (f (f (f x)))))))) := by
  auto [H]

example (x y : Nat) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ f₁₄ : Nat → Nat → Nat)
  (H : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈,
    f₁ (f₂ (f₃ x₁ x₂) (f₄ x₃ x₄)) (f₅ (f₆ x₅ x₆) (f₇ x₇ x₈)) =
    f₈ (f₉ (f₁₀ x₈ x₇) (f₁₁ x₆ x₅)) (f₁₂ (f₁₃ x₄ x₃) (f₁₄ x₂ x₁))) :
  True := by
  auto [H]

-- Basic examples

example (a b c d : Nat) :
  a + b + d + c = (d + a) + (c + b) := by
  auto [Nat.add_comm, Nat.add_assoc]

example (a b c : Nat) :
  a * (b + c) = b * a + a * c := by
  auto [Nat.add_comm, Nat.mul_comm, Nat.add_mul]

set_option auto.tptp true in
set_option auto.native false in
example (f : (Nat → Nat → Prop) → Prop)
  (h : ∀ (p : Nat → Nat → Prop), (∀ x, p x x) → f p) : f (fun x y => x = y) := by
  try auto [h]
  apply h; intro; rfl

-- Binders in the goal

example : 2 = 3 → 2 = 3 := by auto

-- Higher Order

example (H : (fun x : Nat => x) = (fun x => x)) : True := by
  auto [H]

example (H : (fun (x y z t : Nat) => x) = (fun x y z t => x)) : True := by
  auto [H]

example
  {α : Sort u}
  (add : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (hadd : ∀ x y f n, add x y f n = (x f) ((y f) n))
  (mul : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (hmul : ∀ x y f, mul x y f = x (y f))
  (w₁ w₂ : ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (Hw₁₂ : (w₁ = w₂) = (w₂ = w₁)) : True := by
  auto [hadd, hmul, Hw₁₂]

example
  (P : (α → γ) → Prop) (f : α → β) (g : β → γ) (h : β → β)
  : P ((g ∘ h) ∘ f) = P (fun x => g (h (f x))) := by
  auto [Function.comp_def]

example
  (A : Sort u)
  (add : ∀ {α}, ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (hadd : ∀ {α} x y f n, @add α x y f n = (x f) ((y f) n))
  (mul : ∀ {α}, ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
  (hmul : ∀ {α} x y f, @mul α x y f = x (y f))
  (two : (A → A) → (A → A))
  (htwo : ∀ f x, two f x = f (f x))
  (three : (A → A) → (A → A))
  (hthree : ∀ f x, three f x = f (f (f x))) :
  mul three (add two (add three three)) =
  mul three (mul two (add two two)) := by
  auto [hadd, hmul, htwo, hthree]

-- Polymorphic Constant

set_option auto.redMode "instances" in
example (as bs cs ds : List β) : (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  auto [List.append_assoc]

set_option auto.redMode "instances" in
example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  auto [List.append_assoc, List.map_append]

example (as bs cs ds : List β) :
  (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  auto [List.append_assoc]

example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  auto [List.append_assoc, List.map_append]

-- Polymorphic free variable

example
  (ap : ∀ {α : Type v}, List α → List α → List α)
  (ap_assoc : ∀ (α : Type v) (as bs cs : List α), ap (ap as bs) cs = ap as (ap bs cs)) :
  ap (ap as bs) (ap cs ds) = ap as (ap bs (ap cs ds)) := by
  auto [ap_assoc]

example
  (instHAppend : ∀ {α}, HAppend (List α) (List α) (List α))
  (hap : ∀ {α β γ : Type u} [HAppend α β γ], α → β → γ)
  (ap_assoc : ∀ (α : Type u) (as bs cs : List α),
    @hap (List α) (List α) (List α) instHAppend (@hap (List α) (List α) (List α) instHAppend as bs) cs =
    @hap (List α) (List α) (List α) instHAppend as (@hap (List α) (List α) (List α) instHAppend bs cs)) :
  @hap (List α) (List α) (List α) instHAppend (@hap (List α) (List α) (List α) instHAppend as bs) (@hap (List α) (List α) (List α) instHAppend cs ds) =
  @hap (List α) (List α) (List α) instHAppend as (@hap (List α) (List α) (List α) instHAppend bs (@hap (List α) (List α) (List α) instHAppend cs ds)) := by
  auto [ap_assoc]

-- Matching with leading propositional ∀ quantifiers

example
  (p : ∀ (α : Type), List α → Prop)
  (h1 : ∀ α x, p α x → q)
  (h2 : p A x) : q := by
  auto

example
  (p q : ∀ (α : Type), List α → Prop)
  (h1 : ∀ α β x y, p α x → q β y → r)
  (h2 : p A x)
  (h3 : q B y) : r := by
  auto

-- One LemmaInst match multiple ConstInst

example
  (p1 p2 : ∀ (α : Type), List α → Prop)
  (h1 : ∀ α β x y, p1 α x → p2 β y)
  (h2 : p1 A x) : p2 B y := by
  auto

example
  (p1 p2 p3 : ∀ (α β : Type), List α → List β → Prop)
  (h1 : ∀ α β γ δ ε π x y z t u v, p1 α β x y → p2 γ δ z t → p3 ε π u v)
  (h2 : p1 A B x y)
  (h3 : p2 C D z t) : p3 E F u v := by
  auto

-- Metavariable

example (u : α) (h : ∀ (z : α), x = z ∧ z = y) : x = y := by
  have g : ∀ z, x = z ∧ z = y → x = y := by
    intros z hlr; have ⟨hl, hr⟩ := hlr; exact Eq.trans hl hr
  -- Notably, this example fails if we use "duper"
  apply g; auto [h]; exact x

example (α : Type u) : True := by
  have g : (∀ (ap : ∀ {α : Type u}, List α → List α → List α)
    (ap_assoc_imp : (∀ (as bs cs : List α), ap (ap as bs) cs = ap as (ap bs cs)) →
      (∀ (as bs cs ds : List α), ap (ap as bs) (ap cs ds) = ap as (ap bs (ap cs ds)))), True) := by
    intros; exact True.intro
  apply g;
  case ap_assoc_imp => intro hassoc; auto [hassoc]
  case ap => exact List.append

-- A head expression may have different dependent arguments under
--   different circumstances. This is first observed in `FunLike.coe`

section FluidDep

  variable (fundep : ∀ {α : Type u} (β : α → Type) (a : α), β a)

  example (h : @fundep α (fun _ => Nat) = fun (_ : α) => x) :
    @fundep α (fun _ => Nat) y = x := by
    auto [h]

end FluidDep

-- Defeq Problem in Types

section TypeDefeq

  class Foo where
    foo : Nat

  def inst₁ : Foo := ⟨2⟩

  def inst₂ : Foo := ⟨2⟩

  variable (fun₁ : [Foo] → Type)

  example (f : @fun₁ inst₁ → Nat) (g : @fun₁ inst₂ → Nat) (H : f = g) : g = f := by
    auto [H]

end TypeDefeq

-- Definition Recognization

section DefinitionRecognization

  set_option trace.auto.lamReif.prep.def true

  example (a b : α) (f : α → α) (H : f b = a) : True := by
    auto

  example (f g : α → β) (h : α → α) (H : ∀ x, f x = g (h x)) : True := by
    auto

  example (f : α → α → α) (g : α → α → α → α → α) (H : ∀ x y z, f x y = g x y z z) : True := by
    auto

  example (f : α → α → α) (g : α → α → α) (H : ∀ x y, f y x = g x x) : True := by
    auto

  example (f : α → α → α) (g : α → α → α) (H : (fun x y => f y x) = (fun x y => f x y)) : True := by
    auto

  example (f : α → α → α) (g : α → α → α) (H : (fun x y => f y x) = (fun x y => g x x)) : True := by
    auto

  example (f : α → α → α) (g : α → α → α) (H : (fun x y => g x x) = (fun x y => f y x)) : True := by
    auto

  example (f : α → β → γ → δ → ε) (g : α → α → ε) (H : ∀ x t z y, f x y z t = g x x) : True := by
    auto

  set_option trace.auto.lamReif.printProofs true

  example (a b : α) (f : α → α) (H : f b = a) : f (f b) = f a := by
    auto

  example (a : α) (f : α → α) (H : f a = a) : f (f a) = a := by
    auto

  example (f : α → α → α) (g : α → α → α) (H : (fun x y => f y x) = (fun x y => g x x)) :
    f b a = f c a := by
    auto

  example (H : α ↔ β) : α = β := by
    auto

  example {α : Type} (f : α → Nat → Nat → α → Nat) :
    ∀ a b c, f a 1 b c = f a 1 b c := by auto

end DefinitionRecognization

-- Complex

section Complex

  set_option auto.mono.ignoreNonQuasiHigherOrder true in
  example (h1 : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0) (h2 : 3 > 0) : ∃ z : Fin 3, z.1 = 0 := by
    auto

end Complex

-- SMT support

section SMT

  set_option auto.tptp false
  set_option auto.native false
  set_option auto.smt true
  set_option auto.smt.trust true

  set_option auto.mono.ciInstDefEq false
  set_option auto.mono.termLikeDefEq false

  -- If-then-else
  example (h₁ : if 2 < 3 then False else True) (h₂ : 2 < 3) : False := by
    auto

  example (h₁ : if 2 > 3 then True else False) (h₂ : ¬ 2 > 3) : False := by
    auto

  example {α : Sort u} {β : Sort v} (x y : α) (z t : β) :
    (if True then x else y) = x ∧ (if False then z else t) = t := by
    auto

  -- Nested `ite`

  set_option auto.smt true in
  set_option auto.tptp false in
  example
    (h : if (if 2 = 3 then 1 else 2) = (if 3 = 2 then 0 else 1) then True else False)
    : False := by
    auto

  set_option trace.auto.mono.printInputLemmas true
  open Classical
  example
    (node : Type) [node_dec : DecidableEq node] (ring_bottom : node)
    (st0_x st0_up st1_x st1_up : node → Prop) (s x x_1 : node)
    (bad_motive :
      ¬if s = ring_bottom then True
        else if st0_x s = st0_x x then True
        else if ((¬st0_x s) = if x_1 = s then ¬st0_x s else st0_x x_1) ∧ ¬x_1 = s ∧ ¬st0_up x_1 then
          (∀ (a_1 : node), (if a_1 = s then ¬st0_x s else st0_x a_1) = st1_x a_1) → ∃ x, ¬(¬x = s ∧ (¬x = s → st0_up x)) = st1_up x
        else True) :
    True := by
    auto

  -- Boolean
  example : true ≠ false := by
    auto

  example : (!a && !b) = !(a || b) := by
    auto

  example
    (a b : α) [inst : Decidable (a = b)]
    (h : if (a = b) then True else a = b) : a = b := by
    auto

  -- Cond
  example : cond true a b = a ∧ cond false a b = b := by
    auto

  example (h : p = true) : cond p a b = a := by
    auto

  example (h : p = false) : cond p a b = b := by
    auto

  -- Decide
  example : ∀ b, !(b = true) ↔ b = false := by auto

  example : ∀ b, !(b = false) ↔ b = true := by auto

  example (h : ¬ (∀ b, !(b = true) ↔ b = false)) : False := by
    auto

  -- Nat
  example (_ : ∃ b, !(!b) ≠ b) : False := by auto

  example (a b : Nat) : max a b = max a b ∧ min a b = min a b := by auto

  example (a b c : Nat) : Nat.zero = 0 ∧ 3 = nat_lit 3 ∧ (a = b ↔ b = a) ∧ Nat.succ c = c + 1 := by auto

  example : Nat.succ x = x + 1 := by auto

  example (a b : Nat) : a % b + a - b + (a / b) * b = a % b + a - b + (a / b) * b := by auto

  example (a b c d : Nat) (h₁ : a < b) (h₂ : c > d) : b > a ∧ d < c := by auto

  example (a b c d : Nat) (h₁ : a ≤ b) (h₂ : c ≥ d) : b ≥ a ∧ d ≤ c := by auto

  example : 10 % 0 = 10 := by
    auto

  example : 10 / 0 = 0 := by
    auto

  -- Integer
  example
    (a b : Int)
    (mul_comm : ∀ (a b : Int), a * b = b * a) : a * b + 1 = b * a + 1 := by auto

  example
    (a b : Int)
    : a * b - a % (Int.tmod b a) = a * b - a % (Int.tmod b a) := by auto

  example (a : Int)
    (h₁ : a ≥ 0) (h₂ : -a ≤ 0) (h₃ : 0 < 1) (h₄ : 2 > 0)
    : (a ≥ 0) ∧ (-a ≤ 0) ∧ (0 < 1) ∧ (2 > 0) := by auto

  example (a b : Int) : max a b = max a b ∧ min a b = min a b := by auto

  example : (3 : Int) = ((nat_lit 3) : Int) := by auto

  example : (-3 : Int) = (-(nat_lit 3) : Int) := by auto

  example : (10 : Int) % (0 : Int) = 10 := by
    auto

  example : (10 : Int) / (0 : Int) = 0 := by
    auto

  -- String
  example (a b : String)
    : "asdf" = "asdf" ∧ a ++ b = a ++ b ∧ (a < b) = (a < b) ∧
      (a > b) = (a > b) ∧ a.length = a.length := by auto

  example (a b : String)
    : String.isPrefixOf a b = String.isPrefixOf a b ∧
      String.replace a b a = String.replace a b a := by auto

  -- BitVec
  example (a : BitVec k) (b : BitVec 2) : a = a ∧ b = b := by auto

  example (a : BitVec u) (b : BitVec v) (c : BitVec 2) :
    a ++ b = a ++ b ∧ b ++ c = b ++ c := by auto

  example :
    0b10#3 + 0b101#3 = 0b10#3 + 0b101#3 ∧
    0b10#(3+0) * 0b101#(1+2) = 0b10#3 * 0b101#3 := by auto

  example (a b : Nat) :
    let f := BitVec.ofNat 16; f (a + b) = f a + f b ∧ f (a * b) = f a * f b := by auto

  example (a b : BitVec 3) :
    (a < b) = (b > a) ∧ (a ≤ b) = (b ≥ a) := by auto

  example (a : BitVec 5) (b : BitVec k) :
    a.msb = a.msb ∧ b.msb = b.msb ∧
    a.rotateLeft w = a.rotateLeft w ∧
    a.rotateRight w = a.rotateRight w := by auto

  -- SMT attributes
  open Auto.SMT.Attribute in
  example (f : Int → Int) (H : forall x, trigger (f x) (f x > x)) :
    (forall x, (f x) + 1 > x) := by
    auto [H]

end SMT

-- TPTP Support

section TPTP

  -- TPTP/SMT support for `Empty`
  example (f : ((Empty → Prop) → Prop) → Prop) :
    f Auto.Embedding.forallF = f Auto.Embedding.forallF := by auto

  example (f : ((Empty → Prop) → Prop) → Prop) :
    f Exists = f Exists := by auto

  -- Regression tests for #72: expanding a non-lambda quantifier body must not
  -- capture bound variables from the surrounding context.
  #guard (Auto.Lam2TH0.transLamTerm
      (.app (.func (.atom 0) (.base .prop)) (.base (.existE (.atom 0))) (.bvar 0)) 1).toOption ==
    .some "(? [X1 : s_a0] : (X0 @ X1))"

  #guard (Auto.Lam2TH0.transLamTerm
      (.app (.func (.atom 0) (.base .prop)) (.base (.forallE (.atom 0))) (.bvar 0)) 1).toOption ==
    .some "(! [X1 : s_a0] : (X0 @ X1))"

  #guard (Auto.Lam2TH0.transLamTerm
      (.app (.func (.atom 0) (.base .prop)) (.base (.forallE (.atom 0)))
        (.lam (.atom 0)
          (.app (.func (.atom 0) (.base .prop)) (.base (.existE (.atom 0)))
            (.app (.atom 0) (.bvar 1) (.bvar 0))))) 1).toOption ==
    .some "(! [X1 : s_a0] : (? [X2 : s_a0] : ((X0 @ X1) @ X2)))"

  -- An explicit lambda body is stripped directly and must not be lifted again.
  #guard (Auto.Lam2TH0.transLamTerm
      (.app (.func (.atom 0) (.base .prop)) (.base (.existE (.atom 0)))
        (.lam (.atom 0) (.app (.atom 0) (.bvar 1) (.bvar 0)))) 1).toOption ==
    .some "(? [X1 : s_a0] : (X0 @ X1))"

end TPTP


-- Native prover's handling of `Real` (a `LaterType`)
section NativeReal

  /-
    `lean-auto` cannot import Mathlib, so this section uses a stand-in `Real`.
    When `Real` and its operations are treated like builtin types (e.g. `Nat`, `Int`),
    the hypotheses sent to the native prover (see `trace.auto.lam2D.printHyps`)
    should mention `Real`'s `+, -, *, /, -·, ·⁻¹` as-is, instead of free variables
    for uninterpreted atoms.
  -/

  -- Use smt solver to test correctness of translation
  set_option auto.smt true
  set_option auto.smt.trust true
  set_option auto.tptp false
  set_option auto.native false

  -- Stand-ins for Mathlib's `FloorRing`, `Int.floor`, `Int.ceil` and `abs`,
  --   and Batteries' `RatCast` and `Rat.cast`, with the same shape of arguments
  class _root_.FloorRing (α : Type) where
    floor : α → Int
    ceil : α → Int

  def _root_.Int.floor {α : Type} [FloorRing α] : α → Int := FloorRing.floor
  def _root_.Int.ceil {α : Type} [FloorRing α] : α → Int := FloorRing.ceil
  def _root_.abs {α : Type} [Max α] [Neg α] (a : α) : α := max a (-a)

  class _root_.RatCast (K : Type) where
    ratCast : Rat → K

  @[reducible] def _root_.Rat.cast {K : Type} [RatCast K] : Rat → K := RatCast.ratCast

  structure _root_.Real where
    val : Rat
  deriving Inhabited

  namespace Real

  @[irreducible] private def zero : Real := ⟨0⟩
  @[irreducible] private def one : Real := ⟨1⟩
  @[irreducible] private def add (x y : Real) : Real := ⟨x.val + y.val⟩
  @[irreducible] private def neg (x : Real) : Real := ⟨-x.val⟩
  @[irreducible] private def mul (x y : Real) : Real := ⟨x.val * y.val⟩
  @[irreducible] private def inv' (x : Real) : Real := ⟨x.val⁻¹⟩
  @[irreducible] private def lt (x y : Real) : Prop := x.val < y.val
  @[irreducible] private def le (x y : Real) : Prop := x.val ≤ y.val
  @[irreducible] private def sup (x y : Real) : Real := ⟨max x.val y.val⟩
  @[irreducible] private def inf (x y : Real) : Real := ⟨min x.val y.val⟩

  -- Mathlib's `Real.sqrt` is irreducible
  opaque sqrt : Real → Real

  instance : Zero Real := ⟨zero⟩
  instance : One Real := ⟨one⟩
  instance : Add Real := ⟨add⟩
  instance : Neg Real := ⟨neg⟩
  instance : Mul Real := ⟨mul⟩

  -- Constants are recognized individually: here `0`, `+` and `*` are recognized, while
  --   `Real.inv'` is an uninterpreted atom because `Inv Real` is not declared yet. The SMT
  --   translation still treats `Real` as an uninterpreted sort, because its core constants are
  --   not characterized (see the stand-ins for theorems of Mathlib below)
  example (x y : Real) (h : False) : x + y * 0 = x := by
    fail_if_success auto []
    contradiction

  example (h : False) : Real.inv' 1 = 1 := by
    fail_if_success auto []
    contradiction

  instance : Inv Real := ⟨inv'⟩
  instance : Sub Real := ⟨fun a b => a + -b⟩
  instance : Div Real := ⟨fun a b => a * b⁻¹⟩
  instance : NatCast Real := ⟨fun n => ⟨n⟩⟩
  instance : IntCast Real := ⟨fun z => ⟨z⟩⟩
  instance (priority := 100) (n : Nat) : OfNat Real n := ⟨Nat.cast (OfNat.ofNat n)⟩
  instance : LT Real := ⟨lt⟩
  instance : LE Real := ⟨le⟩
  instance : Max Real := ⟨sup⟩
  instance : Min Real := ⟨inf⟩
  instance : OfScientific Real := ⟨fun m s e => ⟨OfScientific.ofScientific m s e⟩⟩
  instance : FloorRing Real := ⟨fun x => x.val.floor, fun x => x.val.ceil⟩
  instance : Pow Real Nat := ⟨fun x n => ⟨x.val ^ n⟩⟩
  instance : RatCast Real := ⟨fun q => ⟨q⟩⟩

  end Real

  /-
    Stand-ins for theorems of Mathlib, which prove the characterizations of the constants of
      `Real` (see `RealInterpUnlifted.CoreSpec` and `RealInterpUnlifted.ExtSpec`). The SMT
      translation only interprets `Real` and its constants if they are characterized.
    They are proved from the corresponding facts about `Rat`, except for the ones that
      the stand-in does not satisfy (completeness) or that are about the opaque `Real.sqrt`
  -/
  theorem Real.ext {a b : Real} (h : a.val = b.val) : a = b := by cases a; cases b; cases h; rfl

  @[simp] theorem Real.zero_val : (0 : Real).val = 0 := by show Real.zero.val = 0; unfold Real.zero; rfl
  @[simp] theorem Real.one_val : (1 : Real).val = 1 := by show Real.one.val = 1; unfold Real.one; rfl
  @[simp] theorem Real.add_val (a b : Real) : (a + b).val = a.val + b.val := by
    show (Real.add a b).val = _; unfold Real.add; rfl
  @[simp] theorem Real.neg_val (a : Real) : (-a).val = -a.val := by
    show (Real.neg a).val = _; unfold Real.neg; rfl
  @[simp] theorem Real.mul_val (a b : Real) : (a * b).val = a.val * b.val := by
    show (Real.mul a b).val = _; unfold Real.mul; rfl
  @[simp] theorem Real.inv_val (a : Real) : a⁻¹.val = a.val⁻¹ := by
    show (Real.inv' a).val = _; unfold Real.inv'; rfl
  @[simp] theorem Real.le_iff (a b : Real) : a ≤ b ↔ a.val ≤ b.val := by
    show Real.le a b ↔ _; unfold Real.le; rfl
  @[simp] theorem Real.lt_iff (a b : Real) : a < b ↔ a.val < b.val := by
    show Real.lt a b ↔ _; unfold Real.lt; rfl
  @[simp] theorem Real.max_val (a b : Real) : (max a b).val = max a.val b.val := by
    show (Real.sup a b).val = _; unfold Real.sup; rfl
  @[simp] theorem Real.min_val (a b : Real) : (min a b).val = min a.val b.val := by
    show (Real.inf a b).val = _; unfold Real.inf; rfl

  -- Core constants
  theorem _root_.add_assoc (a b c : Real) : a + b + c = a + (b + c) := Real.ext (by simp; grind)
  theorem _root_.add_comm (a b : Real) : a + b = b + a := Real.ext (by simp; grind)
  theorem _root_.zero_add (a : Real) : 0 + a = a := Real.ext (by simp; exact Rat.zero_add _)
  theorem _root_.add_neg_cancel (a : Real) : a + -a = 0 := Real.ext (by simp; grind)
  theorem _root_.mul_assoc (a b c : Real) : a * b * c = a * (b * c) := Real.ext (by simp; grind)
  theorem _root_.mul_comm (a b : Real) : a * b = b * a := Real.ext (by simp; grind)
  theorem _root_.one_mul (a : Real) : 1 * a = a := Real.ext (by simp)
  theorem _root_.mul_add (a b c : Real) : a * (b + c) = a * b + a * c := Real.ext (by simp; grind)
  theorem _root_.zero_ne_one : (0 : Real) ≠ 1 := fun h => by simpa using congrArg Real.val h
  theorem _root_.mul_inv_cancel₀ {a : Real} (h : a ≠ 0) : a * a⁻¹ = 1 :=
    Real.ext (by simp; exact Rat.mul_inv_cancel _ fun h' => h (Real.ext (by simpa using h')))
  theorem _root_.inv_zero : (0 : Real)⁻¹ = 0 := Real.ext (by simp)
  theorem _root_.le_refl (a : Real) : a ≤ a := by simp
  theorem _root_.le_trans {a b c : Real} : a ≤ b → b ≤ c → a ≤ c := by simp; grind
  theorem _root_.le_antisymm {a b : Real} : a ≤ b → b ≤ a → a = b := by
    simp; intro h₁ h₂; exact Real.ext (by grind)
  theorem _root_.le_total (a b : Real) : a ≤ b ∨ b ≤ a := by simp; grind
  theorem _root_.add_le_add {a b c d : Real} : a ≤ b → c ≤ d → a + c ≤ b + d := by simp; grind
  theorem _root_.mul_nonneg {a b : Real} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by simp; exact Rat.mul_nonneg
  -- Does not hold for the stand-in
  theorem _root_.Real.exists_isLUB {S : Real → Prop} : (∃ x, S x) → (∃ b, ∀ x, S x → x ≤ b) →
    ∃ s, (∀ x, S x → x ≤ s) ∧ ∀ b, (∀ x, S x → x ≤ b) → s ≤ b := sorry

  -- Other constants. `div_eq_mul_inv`, `pow_zero` and `pow_succ` are polymorphic in Mathlib
  class _root_.DivInvLaws (α : Type) [Mul α] [Inv α] [Div α] : Prop where
    div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹

  class _root_.PowLaws (α : Type) [Mul α] [One α] [Pow α Nat] : Prop where
    pow_zero : ∀ a : α, a ^ 0 = 1
    pow_succ : ∀ (a : α) (n : Nat), a ^ (n + 1) = a ^ n * a

  theorem _root_.div_eq_mul_inv {α : Type} [Mul α] [Inv α] [Div α] [DivInvLaws α] (a b : α) :
    a / b = a * b⁻¹ := DivInvLaws.div_eq_mul_inv a b
  theorem _root_.pow_zero {α : Type} [Mul α] [One α] [Pow α Nat] [PowLaws α] (a : α) :
    a ^ 0 = 1 := PowLaws.pow_zero a
  theorem _root_.pow_succ {α : Type} [Mul α] [One α] [Pow α Nat] [PowLaws α] (a : α) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := PowLaws.pow_succ a n

  instance : DivInvLaws Real := ⟨fun _ _ => rfl⟩
  instance : PowLaws Real := ⟨fun a => Real.ext (by show a.val ^ 0 = _; simp),
    fun a n => Real.ext (by simp; show a.val ^ (n + 1) = a.val ^ n * a.val; exact Rat.pow_succ _ _)⟩

  theorem _root_.sub_eq_add_neg (a b : Real) : a - b = a + -b := rfl
  theorem _root_.Nat.cast_zero : ((0 : Nat) : Real) = 0 := Real.ext (by simp; rfl)
  theorem _root_.Nat.cast_succ (n : Nat) : ((n + 1 : Nat) : Real) = n + 1 :=
    Real.ext (by simp; show ((n + 1 : Nat) : Rat) = (n : Rat) + 1; simp)
  theorem _root_.Int.cast_one : ((1 : Int) : Real) = 1 := Real.ext (by simp; rfl)
  theorem _root_.Int.cast_add (m n : Int) : ((m + n : Int) : Real) = m + n :=
    Real.ext (by simp; show ((m + n : Int) : Rat) = (m : Rat) + (n : Rat); simp)
  theorem _root_.lt_iff_le_not_ge {a b : Real} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by simp; grind
  theorem _root_.max_eq_left {a b : Real} (h : b ≤ a) : max a b = a := Real.ext (by simp at h ⊢; grind)
  theorem _root_.max_eq_right {a b : Real} (h : a ≤ b) : max a b = b := Real.ext (by simp at h ⊢; grind)
  theorem _root_.min_eq_left {a b : Real} (h : a ≤ b) : min a b = a := Real.ext (by simp at h ⊢; grind)
  theorem _root_.min_eq_right {a b : Real} (h : b ≤ a) : min a b = b := Real.ext (by simp at h ⊢; grind)
  theorem _root_.abs_of_nonneg {a : Real} (h : 0 ≤ a) : abs a = a := Real.ext (by simp [abs] at h ⊢; grind)
  theorem _root_.abs_of_nonpos {a : Real} (h : a ≤ 0) : abs a = -a := Real.ext (by simp [abs] at h ⊢; grind)
  theorem _root_.Rat.cast_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    (Rat.cast (OfScientific.ofScientific m s e : Rat) : Real) = OfScientific.ofScientific m s e := rfl
  theorem _root_.Rat.cast_one : (Rat.cast (1 : Rat) : Real) = 1 := Real.ext (by simp; rfl)
  theorem _root_.Rat.cast_add (p q : Rat) : (Rat.cast (p + q) : Real) = Rat.cast p + Rat.cast q :=
    Real.ext (by simp; rfl)
  theorem _root_.Rat.cast_mul (p q : Rat) : (Rat.cast (p * q) : Real) = Rat.cast p * Rat.cast q :=
    Real.ext (by simp; rfl)
  -- About the opaque `Real.sqrt`
  theorem _root_.Real.sqrt_nonneg (x : Real) : 0 ≤ Real.sqrt x := sorry
  theorem _root_.Real.mul_self_sqrt {x : Real} (h : 0 ≤ x) : Real.sqrt x * Real.sqrt x = x := sorry
  theorem _root_.Real.sqrt_eq_zero_of_nonpos {x : Real} (h : x ≤ 0) : Real.sqrt x = 0 := sorry

  -- The core constants are characterized, so `Real` is interpreted. Each of the other constants
  --   is interpreted only if it is characterized, and here `Int.floor` is not
  example (x y : Real) : x + y * 0 = x := by auto

  example (h : False) : Int.floor (2.5 : Real) = 2 := by
    fail_if_success auto []
    contradiction

  theorem _root_.Int.floor_le (a : Real) : ((Int.floor a : Int) : Real) ≤ a := by
    show ((a.val.floor : Int) : Real) ≤ a; simp
    show ((a.val.floor : Int) : Rat) ≤ a.val; exact Rat.floor_le _
  theorem _root_.Int.lt_floor_add_one (a : Real) : a < ((Int.floor a : Int) : Real) + 1 := by
    show a < ((a.val.floor : Int) : Real) + 1; simp
    show a.val < ((a.val.floor : Int) : Rat) + 1; simpa using Rat.lt_floor_add_one a.val
  theorem _root_.Int.le_ceil (a : Real) : a ≤ ((Int.ceil a : Int) : Real) := by
    show a ≤ ((a.val.ceil : Int) : Real); simp
    show a.val ≤ ((a.val.ceil : Int) : Rat); exact Rat.le_ceil
  theorem _root_.Int.ceil_lt_add_one (a : Real) : ((Int.ceil a : Int) : Real) < a + 1 := by
    show ((a.val.ceil : Int) : Real) < a + 1; simp
    show ((a.val.ceil : Int) : Rat) < a.val + 1; exact Rat.ceil_lt

  example (x y : Real) (h : x = 1 * y) : x = 1 * y := by
    fail_if_success auto []
    exact h

  -- Lean's `x / 0 = 0` and `0⁻¹ = 0`, which do not hold for SMT-LIB's `/`
  example (x : Real) : x / 0 = 0 ∧ (0 : Real)⁻¹ = 0 := by auto

  example (x y : Real) : y + x = Real.add x y := by auto

  example (x y : Real) (h : -x = y⁻¹) : y⁻¹ = -x := by auto [h]

  example (x y : Real) : x * y = y * x := by auto

  example (f : Real → Real) (y z : Real) (h : ∀ x, f x = x + x) : f (y * z) = y * z + y * z := by auto [h]

  example : ∀ x : Real, ∃ y : Real, y = x - x := by auto

  -- Mixing with builtin types
  example (n : Nat) (x : Real) (h₁ : n * n = n + n) (h₂ : x * x = x + x) :
    n + n = n * n ∧ x + x = x * x := by auto [h₁, h₂]

  -- Order
  example (x y z : Real) (h₁ : x ≤ y) (h₂ : y < z) : x < z ∧ ¬ z ≤ x := by auto [h₁, h₂]

  example (x y : Real) (h₁ : x ≤ y) (h₂ : x ≠ y) : x < y := by
    fail_if_success auto [h₁]
    auto [h₁, h₂]

  example (x y : Real) (h : Real.lt x y) : x ≤ y := by auto [h]

  example (x : Real) (h : False) : x < x := by
    fail_if_success auto []
    contradiction

  -- `≥` and `>` are recognized as flipped `≤` and `<`
  example (x y : Real) : (x ≥ y ↔ y ≤ x) ∧ (x > y ↔ y < x) := by auto

  example (x y : Real) (h : False) : (x ≥ y ↔ x ≤ y) := by
    fail_if_success auto []
    contradiction

  example (x y : Real) : max x y ≥ x ∧ min x y ≤ y ∧ abs x ≥ 0 ∧ abs (-x) = abs x := by auto

  example (x y : Real) (h : False) : max x y ≤ x := by
    fail_if_success auto []
    contradiction

  example (h : False) : abs (-1 : Real) = -1 := by
    fail_if_success auto []
    contradiction

  -- Mathlib's `abs` on `Int` (a function with two instance arguments, not `Abs.abs`)
  example (x : Int) : abs x ≥ 0 ∧ abs (-x) = abs x ∧ abs (-3 : Int) = 3 := by auto

  example (h : False) : abs (-1 : Int) = -1 := by
    fail_if_success auto []
    contradiction

  -- The kernel checks that `abs` on `Int` is definitionally equal to `Int.abs`
  set_option auto.smt false in
  set_option auto.native true in
  example (x : Int) (h : abs x ≥ 0) : abs x ≥ 0 := by auto [h]

  -- Decimal literals
  example : (1.5 : Real) + 0.5 = 2 ∧ (0.25 : Real) * 4 = 1 ∧ (2.5e2 : Real) = 250 := by auto

  example (h : False) : (2.5 : Real) = 1.5 + 1.5 := by
    fail_if_success auto []
    contradiction

  example (x : Real) :
    Int.floor x ≤ Int.floor (x + 1) ∧ ((Int.floor x : Int) : Real) ≤ x ∧ x ≤ ((Int.ceil x : Int) : Real) := by auto

  example : Int.floor (2.5 : Real) = 2 ∧ Int.ceil (2.5 : Real) = 3 ∧ Int.floor (-2.5 : Real) = -3 := by auto

  example (h : False) : Int.floor (-2.5 : Real) = -2 := by
    fail_if_success auto []
    contradiction

  -- Powers, expanded into multiplications for literal exponents
  example (x y : Real) : x ^ 2 ≥ 0 ∧ (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 ∧ x ^ 0 = 1 ∧ x ^ 1 = x := by auto

  example (x : Real) (n : Nat) (h : x ^ n = 0) : x ^ (n + 1) = 0 := by auto [h]

  example (x : Real) (h : False) : x ^ 2 = x := by
    fail_if_success auto []
    contradiction

  -- `Real.sqrt`, with `Real.sqrt x = 0` for `x < 0`
  example (x : Real) (h : x ≥ 0) : Real.sqrt x * Real.sqrt x = x ∧ Real.sqrt x ≥ 0 := by auto [h]

  example : Real.sqrt 4 = 2 ∧ Real.sqrt (-1) = 0 := by auto

  example (x : Real) (h : False) : Real.sqrt x * Real.sqrt x = x := by
    fail_if_success auto []
    contradiction

  -- `Rat.cast`
  example (q : Rat) :
    (Rat.cast q : Real) + 1 = Rat.cast (q + 1) ∧ (Rat.cast (1.5 : Rat) : Real) = 1.5 ∧
    (Rat.cast q : Real) ≤ Rat.cast (q + 1) := by auto

  example (q : Rat) (h : False) : (Rat.cast q : Real) = Rat.cast (q + 1) := by
    fail_if_success auto []
    contradiction

  -- The characterizations are part of the valuation of the verified checker, which the
  --   kernel checks together with the proof produced by the (emulated) native prover
  set_option auto.smt false in
  set_option auto.native true in
  set_option auto.checker.buildMode "directReduce" in
  example (x y : Real) (h : x - y ≤ max x y) : x - y ≤ max x y := by auto [h]

  set_option auto.smt false in
  set_option auto.native true in
  set_option auto.checker.buildMode "indirectReduce" in
  example (x y : Real) (h : x - y ≤ max x y) : x - y ≤ max x y := by auto [h]

  set_option auto.smt false in
  set_option auto.native true in
  set_option auto.checker.buildMode "indirectReduce_reflection" in
  example (x y : Real) (h : x - y ≤ max x y) : x - y ≤ max x y := by auto [h]

  open Lean Auto Embedding.Lam in
  /--
    Run the checker step `.f fs`, which should produce the valid fact `t`, with the valuation
      built from the environment (with no atoms), and let the kernel check the result
  -/
  def checkSpecFactStep (fs : FactStep) (t : LamTerm) (name : Name) : MetaM Unit := do
    let li ← Auto.LamLater.LaterInfo.init
    let u := Level.zero
    let tyVal := mkApp2 (.const ``TyVal.mk [u]) (.lam `_ (.const ``Nat []) (.const ``PUnit [.succ .zero]) .default)
      (li.laterTyValExpr u)
    let mk := mkApp2 (.const ``CPVal.mk [u]) tyVal (li.laterValExpr u)
    let .forallE _ varTy (.forallE _ ilTy _ _) _ ← Meta.inferType mk
      | throwError "Unexpected type of `CPVal.mk`"
    let cpv := mkApp2 mk (← Meta.mkAppOptM ``BinTree.leaf #[varTy.appArg!]) (← Meta.mkAppOptM ``BinTree.leaf #[ilTy.appArg!])
    let it := Expr.app (.const ``BinTree.leaf [.zero]) (mkApp2 (.const ``PSigma [.succ .zero, .zero])
      (.const ``ImportEntry []) (.app (.const ``importTablePSigmaβ [u]) cpv))
    let cs := toExpr (BinTree.leaf.insert 0 (ChkStep.f fs, 0) : ChkSteps)
    let heq ← Meta.mkEqRefl (toExpr (Option.some (([] : List LamSort), t)))
    let proof := mkAppN (.const ``Checker.getValidExport_directReduce [u])
      #[toExpr ([] : List LamSort), toExpr t, cpv, it, cs, toExpr (0 : Nat), heq]
    addDecl (.thmDecl { name, levelParams := [], type := ← Meta.inferType proof, value := proof })

  -- The checker step `FactStep.realExtSpec .max` produces the characterization of `max`,
  --   which is available in the valuation
  run_meta checkSpecFactStep (.realExtSpec .max) (.realExtSpec .max) `Real.maxSpecTest

end NativeReal


-- Handling of `Complex` (a `LaterType` that depends on `Real`)
section NativeComplex

  /-
    Uses the stand-in `Real` of section `NativeReal`, and a stand-in `Complex`
    mirroring `Mathlib/Basic/Complex/Basic.lean`
  -/

  -- Use smt solver to test correctness of translation
  set_option auto.smt true
  set_option auto.smt.trust true
  set_option auto.tptp false
  set_option auto.native false

  -- Stand-ins for Mathlib's `DFunLike`, bundled homomorphisms, `Star`, `starRingEnd` and `Norm`,
  --   with the same shape of arguments
  class _root_.DFunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam (α → Sort _)) where
    coe : F → ∀ a : α, β a

  instance (priority := 100) {F α β} [DFunLike F α fun _ => β] : CoeFun F (fun _ => α → β) where
    coe := @DFunLike.coe _ _ _ _

  structure _root_.MonoidWithZeroHom (M N : Type) where
    toFun : M → N

  instance {M N : Type} : DFunLike (MonoidWithZeroHom M N) M (fun _ => N) := ⟨MonoidWithZeroHom.toFun⟩

  structure _root_.RingHom (M N : Type) where
    toFun : M → N

  instance {M N : Type} : DFunLike (RingHom M N) M (fun _ => N) := ⟨RingHom.toFun⟩

  class _root_.Star (R : Type) where
    star : R → R

  def _root_.starRingEnd (R : Type) [Star R] : RingHom R R := ⟨Star.star⟩

  class _root_.Norm (E : Type) where
    norm : E → Real

  structure _root_.Complex where
    re : Real
    im : Real

  namespace Complex

  def ofReal (r : Real) : Complex := ⟨r, 0⟩

  instance : Coe Real Complex := ⟨ofReal⟩
  instance : Zero Complex := ⟨ofReal 0⟩
  instance : One Complex := ⟨ofReal 1⟩
  instance : Add Complex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
  instance : Neg Complex := ⟨fun z => ⟨-z.re, -z.im⟩⟩
  instance : Sub Complex := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
  instance : Mul Complex := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

  -- Constants are recognized individually: here `Complex.I`, `Complex.normSq`, `⁻¹`, `/` etc.
  --   are not declared yet, while `*`, `Complex.re` and `Complex.im` are recognized
  example (z w : Complex) : (z * w).re = z.re * w.re - z.im * w.im := by auto

  -- Mathlib's `normSq` is a bundled homomorphism
  def normSq : MonoidWithZeroHom Complex Real := ⟨fun z => z.re * z.re + z.im * z.im⟩

  instance : Inv Complex := ⟨fun z => ⟨z.re / normSq z, -z.im / normSq z⟩⟩
  instance : Div Complex := ⟨fun z w => z * w⁻¹⟩
  instance : NatCast Complex := ⟨fun n => ofReal n⟩
  instance : IntCast Complex := ⟨fun n => ofReal n⟩
  instance (priority := 100) (n : Nat) : OfNat Complex n := ⟨Nat.cast (OfNat.ofNat n)⟩
  instance : Star Complex := ⟨fun z => ⟨z.re, -z.im⟩⟩
  instance : Norm Complex := ⟨fun z => Real.sqrt (normSq z)⟩
  instance : Pow Complex Nat := ⟨fun z n => Nat.rec 1 (fun _ w => w * z) n⟩
  instance : RatCast Complex := ⟨fun q => ofReal (Rat.cast q)⟩

  def I : Complex := ⟨0, 1⟩

  end Complex

  /-
    Stand-ins for theorems of Mathlib, which prove the characterizations of the constants of
      `Complex` (see `ComplexInterpUnlifted.CoreSpec` and `ComplexInterpUnlifted.ExtSpec`).
      The core constants `re, im, mk` are characterized by definition
  -/
  theorem Complex.zero_re : (0 : Complex).re = 0 := rfl
  theorem Complex.zero_im : (0 : Complex).im = 0 := rfl
  theorem Complex.one_re : (1 : Complex).re = 1 := rfl
  theorem Complex.one_im : (1 : Complex).im = 0 := rfl
  theorem Complex.I_re : Complex.I.re = 0 := rfl
  theorem Complex.I_im : Complex.I.im = 1 := rfl
  theorem Complex.add_re (z w : Complex) : (z + w).re = z.re + w.re := rfl
  theorem Complex.add_im (z w : Complex) : (z + w).im = z.im + w.im := rfl
  theorem Complex.sub_re (z w : Complex) : (z - w).re = z.re - w.re := rfl
  theorem Complex.sub_im (z w : Complex) : (z - w).im = z.im - w.im := rfl
  theorem Complex.mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im * w.im := rfl
  theorem Complex.mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
  theorem Complex.neg_re (z : Complex) : (-z).re = -z.re := rfl
  theorem Complex.neg_im (z : Complex) : (-z).im = -z.im := rfl
  theorem Complex.inv_re (z : Complex) : z⁻¹.re = z.re / Complex.normSq z := rfl
  theorem Complex.inv_im (z : Complex) : z⁻¹.im = -z.im / Complex.normSq z := rfl
  theorem Complex.natCast_re (n : Nat) : (n : Complex).re = (n : Real) := rfl
  theorem Complex.natCast_im (n : Nat) : (n : Complex).im = 0 := rfl
  theorem Complex.intCast_re (n : Int) : (n : Complex).re = (n : Real) := rfl
  theorem Complex.intCast_im (n : Int) : (n : Complex).im = 0 := rfl
  theorem Complex.ratCast_re (q : Rat) : (Rat.cast q : Complex).re = (Rat.cast q : Real) := rfl
  theorem Complex.ratCast_im (q : Rat) : (Rat.cast q : Complex).im = 0 := rfl
  theorem Complex.ofReal_re (x : Real) : (Complex.ofReal x).re = x := rfl
  theorem Complex.ofReal_im (x : Real) : (Complex.ofReal x).im = 0 := rfl
  theorem Complex.conj_re (z : Complex) : (starRingEnd Complex z).re = z.re := rfl
  theorem Complex.conj_im (z : Complex) : (starRingEnd Complex z).im = -z.im := rfl
  theorem Complex.norm_def (z : Complex) : Norm.norm z = Real.sqrt (Complex.normSq z) := rfl
  instance : DivInvLaws Complex := ⟨fun _ _ => rfl⟩
  instance : PowLaws Complex := ⟨fun _ => rfl, fun _ _ => rfl⟩

  -- Each constant is interpreted only if it is characterized, and here `Complex.normSq` is not
  example (h : False) : Complex.normSq Complex.I = 1 := by
    fail_if_success auto []
    contradiction

  theorem Complex.normSq_apply (z : Complex) : Complex.normSq z = z.re * z.re + z.im * z.im := rfl

  example : Complex.normSq Complex.I = 1 := by auto

  example (z : Complex) : (starRingEnd Complex z).im = -z.im ∧ Norm.norm Complex.I = 1 ∧ Complex.I ^ 2 = -1 := by
    auto

  example (z w : Complex) (h : z = 1 * w) : z = 1 * w := by
    fail_if_success auto []
    exact h

  -- Lean's `z / 0 = 0` and `0⁻¹ = 0`
  example (z : Complex) : z / 0 = 0 ∧ (0 : Complex)⁻¹ = 0 := by auto

  example (z w : Complex) : z + w = w + z ∧ z * w = w * z ∧ z - w = z + -w := by auto

  example : Complex.I * Complex.I = -1 := by auto

  example (z : Complex) (h : z ≠ 0) : z * z⁻¹ = 1 := by auto [h]

  example (n : Nat) (k : Int) : (2 : Complex) = 1 + 1 ∧ (n : Complex) = ((n : Real) : Complex) ∧
    (k : Complex) = ((k : Real) : Complex) := by auto

  -- Conversions between `Real` and `Complex`
  example (x y : Real) (z w : Complex) :
    (x : Complex).re = x ∧ (x : Complex).im = 0 ∧ (z * w).re = z.re * w.re - z.im * w.im ∧
    ((x * y : Real) : Complex) = (x : Complex) * (y : Complex) := by auto

  example (z : Complex) : Complex.mk z.re z.im = z := by auto

  -- The kernel checks the valuation with the characterizations, together with
  --   the proof produced by the (emulated) native prover
  set_option auto.smt false in
  set_option auto.native true in
  example (z w : Complex) (h : (z + w).re = z.re + w.re) : (z + w).re = z.re + w.re := by auto [h]

  -- The checker steps `FactStep.complexCoreSpec` and `FactStep.complexExtSpec .add` produce
  --   the characterizations, which are available in the valuation
  run_meta checkSpecFactStep .complexCoreSpec .complexCoreSpec `Complex.coreSpecTest

  run_meta checkSpecFactStep (.complexExtSpec .add) (.complexExtSpec .add) `Complex.addSpecTest

  open Lean Meta in
  /--
    Proofs of the fields of `proof`, recursively, if its type is a structure, e.g.
      `And` or `RealInterpUnlifted.CoreSpec`
  -/
  partial def fieldProofs (proof : Expr) : MetaM (Array Expr) := do
    let .const n _ := (← whnf (← inferType proof)).getAppFn
      | return #[proof]
    if !isStructure (← getEnv) n then
      return #[proof]
    (getStructureFields (← getEnv) n).foldlM (fun acc f => do
      return acc ++ (← fieldProofs (← mkProjection proof f))) #[]

  open Lean Meta Auto in
  /--
    A native prover that closes a negated goal `¬ P` among the regular facts with a
      field `∀ xs, P'` of a characterization of later-declared types
  -/
  def specProver (ni : NativeInterface Lemma) : MetaM Expr := do
    for neg in ni.valids do
      let .forallE _ p (.const ``False []) _ ← whnfD neg.type
        | continue
      for spec in ni.laterSpecs.toArray do
        for specProof in ← fieldProofs spec.proof do
          let (xs, _, body) ← forallMetaTelescope (← inferType specProof)
          if ← isDefEq body p then
            let proof ← instantiateMVars (.app neg.proof (mkAppN specProof xs))
            if !proof.hasMVar then
              return proof
    throwError "specProver :: No characterization closes the goal"

  open Lean Auto in
  /-- Behaves like `emulateNative` if the characterizations offered satisfy `p` -/
  def checkSpecsProver (p : LaterSpecInterface Lemma → Bool) (ni : NativeInterface Lemma) : MetaM Expr := do
    if !p ni.laterSpecs then
      throwError "checkSpecsProver :: Unexpected characterizations {ni.laterSpecs.toArray}"
    Solver.Native.emulateNative ni

  def noSpecsProver := checkSpecsProver (·.toArray.isEmpty)

  def realCoreProver := checkSpecsProver (·.realCore.isSome)

  -- The kernel checks the characterizations used by the native prover
  section
    set_option auto.smt false
    set_option auto.native true
    attribute [local rebind Auto.Native.solverFunc] specProver

    example (x y : Real) : x + y = y + x := by auto
    example (x y : Real) : x - y = x + -y := by auto
    example (z w : Complex) : (z + w).re = z.re + w.re := by auto
    example (z : Complex) : Complex.mk z.re z.im = z := by auto
    set_option auto.checker.buildMode "indirectReduce" in
    example (x y : Real) : x + y = y + x := by auto
    set_option auto.checker.buildMode "indirectReduce_reflection" in
    example (z w : Complex) : (z + w).re = z.re + w.re := by auto
    -- Without the verified checker, the characterizations are proved by the proofs
    --   `lean-auto` finds for them
    example (x y : Real) : x + y = y + x := by mononative
    example (x y : Real) : x - y = x + -y := by mononative
    example (z w : Complex) : (z + w).re = z.re + w.re := by mononative
    example (z : Complex) : Complex.mk z.re z.im = z := by mononative
  end

  -- Characterizations are offered for the later-declared types occurring in
  --   the facts, and for the later-declared types they depend on
  section
    set_option auto.smt false
    set_option auto.native true

    section
      attribute [local rebind Auto.Native.solverFunc] noSpecsProver
      example (n m : Nat) (h : n + m = m + n) : n + m = m + n := by auto [h]
      example (x y : Real) (h : x + y = y + x) : x + y = y + x := by
        fail_if_success auto [h]
        exact h
    end

    section
      attribute [local rebind Auto.Native.solverFunc] realCoreProver
      example (z w : Complex) (h : z + w = w + z) : z + w = w + z := by auto [h]
      example (n m : Nat) (h : n + m = m + n) : n + m = m + n := by
        fail_if_success auto [h]
        exact h
    end
  end

end NativeComplex


-- `Rat` (a builtin type, like `Nat` and `Int`)
section Rat

  /-
    SMT solvers do not have rationals, so `Rat` is translated to `Real`
    with the well-formed constraint `∃ n d : Int, d ≥ 1 ∧ x * d = n`
  -/

  -- Use smt solver to test correctness of translation
  set_option auto.smt true
  set_option auto.smt.trust true
  set_option auto.tptp false
  set_option auto.native false

  example (x y : Rat) : x + y = y + x ∧ x * y = y * x ∧ x - y = x + -y := by auto

  -- `x / 0 = 0` and `0⁻¹ = 0`
  example (x : Rat) : x / 0 = 0 ∧ (0 : Rat)⁻¹ = 0 := by auto

  example (x : Rat) (h : x ≠ 0) : x * x⁻¹ = 1 := by auto [h]

  -- Numerals and decimal literals
  example : (3 : Rat) = 1 + 2 ∧ (1.5 : Rat) + 0.5 = 2 ∧ (0.25 : Rat) * 4 = 1 := by auto

  example (h : False) : (2.5 : Rat) = 250 := by
    fail_if_success auto []
    contradiction

  -- Casts
  example (n : Nat) (k : Int) : (n : Rat) ≥ 0 ∧ ((k + 1 : Int) : Rat) = (k : Rat) + 1 := by auto

  example (k : Int) (h : False) : (k : Rat) ≥ 0 := by
    fail_if_success auto []
    contradiction

  -- Order
  example (x y : Rat) : (x ≥ y ↔ y ≤ x) ∧ max x y ≥ x ∧ min x y ≤ y ∧ Rat.abs x ≥ 0 := by auto

  example (x : Rat) (h : False) : x < x := by
    fail_if_success auto []
    contradiction

  example (x : Rat) :
    Rat.floor x ≤ Rat.floor (x + 1) ∧ Rat.floor (2.5 : Rat) = 2 ∧ Rat.ceil (2.5 : Rat) = 3 := by auto

  example (h : False) : Rat.ceil (2.5 : Rat) = 2 := by
    fail_if_success auto []
    contradiction

  example (h : False) : Rat.floor (-2.5 : Rat) = -2 := by
    fail_if_success auto []
    contradiction

  -- Rationality is respected, although both hold for `Real`
  example (h : False) : ∃ x : Rat, x * x = 2 := by
    fail_if_success auto []
    contradiction

  example (h : False) (h₁ : ∀ x : Rat, x * x ≠ 2) : False := by
    fail_if_success auto [h₁]
    contradiction

end Rat


-- Characterizations of inductive types sent to native provers
section NativeInductive

  set_option auto.smt false
  set_option auto.tptp false
  set_option auto.native true

  inductive IColor where | red | green | blue

  inductive INTree where
    | leaf : Nat → INTree
    | node : List INTree → INTree

  mutual
    inductive IA where | a0 | a1 : IB → IA
    inductive IB where | b0 : IA → IB | b1 : IA → IB → IB
  end

  structure IS where
    x : Nat
    y : Bool

  inductive IRose (α : Type) where
    | mk : α → List (IRose α) → IRose α

  -- The (emulated) native prover uses all the characterizations, so the kernel checks
  --   the proofs of the characterizations of all the mutual blocks
  example (c : IColor) (h : c = .red) : c = .red := by auto [h]
  example (t : INTree) (h : t = .node []) : t = .node [] := by auto [h]
  example (a : IA) (h : a = .a1 (.b0 .a0)) : a = .a1 (.b0 .a0) := by auto [h]
  example (s : IS) (h : s = ⟨1, true⟩) : s = ⟨1, true⟩ := by auto [h]
  example (r : IRose Nat) (h : r = .mk 0 []) : r = .mk 0 [] := by auto [h]
  set_option auto.checker.buildMode "indirectReduce" in
  example (t : INTree) (h : t = .node []) : t = .node [] := by auto [h]
  set_option auto.checker.buildMode "indirectReduce_reflection" in
  example (t : INTree) (h : t = .node []) : t = .node [] := by auto [h]
  example (t : INTree) (h : t = .node []) : t = .node [] := by mononative [h]

  -- `IPF.mk.inj` omits the proof field, whose equation is proved by proof irrelevance
  structure IPF where
    x : Nat
    h : True

  example (s : IPF) (h : s.x = 1) : s.x = 1 := by auto [h]

  open Lean Meta Auto in
  /--
    A native prover that closes a negated goal `¬ P` among the regular facts with a
      conjunct `∀ xs, H₁ → ⋯ → Hₙ → P'` of a characterization of inductive types,
      where `H₁ ⋯ Hₙ` are regular facts
  -/
  def indSpecProver (ni : NativeInterface Lemma) : MetaM Expr := do
    for neg in ni.valids do
      let .forallE _ p (.const ``False []) _ ← whnfD neg.type
        | continue
      for spec in ni.indSpecs.flatMap IndBlockSpec.toArray do
        let (xs, _, body) ← forallMetaTelescope spec.type
        if !(← isDefEq body p) then
          continue
        for x in xs do
          if ← x.mvarId!.isAssigned then
            continue
          for v in ni.valids do
            if ← isDefEq (← inferType x) v.type then
              x.mvarId!.assign v.proof
              break
        let proof ← instantiateMVars (.app neg.proof (mkAppN spec.proof xs))
        if !proof.hasMVar then
          return proof
    throwError "indSpecProver :: No characterization closes the goal"

  -- The kernel checks the characterizations used by the native prover
  section
    attribute [local rebind Auto.Native.solverFunc] indSpecProver

    example (x : Nat) (xs : List Nat) : [] ≠ x :: xs := by auto
    example (x : Nat) (xs : List Nat) : [] ≠ x :: xs := by mononative
    example (a b : Nat) (as bs : List Nat) (h : a :: as = b :: bs) : a = b ∧ as = bs := by auto
    example (a b : Nat) (as bs : List Nat) (h : a :: as = b :: bs) : a = b ∧ as = bs := by mononative
    example : IA.a0 ≠ IA.a1 (IB.b0 IA.a0) := by auto
    -- Preprocessing in the verified checker rewrites `s` by `h`, so the native prover gets
    --   `¬ IS.x (IS.mk n b) = n`, which is closed by the characterization of `IS.x`
    example (s : IS) (n : Nat) (b : Bool) (h : s = ⟨n, b⟩) : s.x = n := by auto
    example : IA.a0 ≠ IA.a1 (IB.b0 IA.a0) := by mononative
    example (P : IColor → Prop) (h₀ : P .red) (h₁ : P .green) (h₂ : P .blue) : ∀ c, P c := by auto
    example (P : IColor → Prop) (h₀ : P .red) (h₁ : P .green) (h₂ : P .blue) : ∀ c, P c := by mononative
    -- Induction over `INTree` and the type `List INTree` nested in it
    example (P : INTree → Prop) (Q : List INTree → Prop) (hl : ∀ n, P (.leaf n))
      (hn : ∀ ts, Q ts → P (.node ts)) (hnil : Q []) (hcons : ∀ t ts, P t → Q ts → Q (t :: ts)) :
      (∀ t, P t) ∧ (∀ ts, Q ts) := by auto
    set_option auto.checker.buildMode "indirectReduce_reflection" in
    example (P : INTree → Prop) (Q : List INTree → Prop) (hl : ∀ n, P (.leaf n))
      (hn : ∀ ts, Q ts → P (.node ts)) (hnil : Q []) (hcons : ∀ t ts, P t → Q ts → Q (t :: ts)) :
      (∀ t, P t) ∧ (∀ ts, Q ts) := by auto
    example (P : INTree → Prop) (Q : List INTree → Prop) (hl : ∀ n, P (.leaf n))
      (hn : ∀ ts, Q ts → P (.node ts)) (hnil : Q []) (hcons : ∀ t ts, P t → Q ts → Q (t :: ts)) :
      (∀ t, P t) ∧ (∀ ts, Q ts) := by mononative

    -- No characterization is offered if `auto.indSpec` is disabled
    set_option auto.indSpec false in
    example (x : Nat) (xs : List Nat) : [] ≠ x :: xs := by
      fail_if_success auto
      simp
  end

end NativeInductive


-- Issues
section Issues

  set_option trace.auto.mono true
  set_option trace.auto.mono.printConstInst true
  set_option trace.auto.lamReif.printResult true

  -- Can succeed if auto ignores the un-monomorphizable formulas
  example (h1 : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0) (h2 : 3 > 0) : ∃ z : Fin 3, z.1 = 0 := by
    auto

  -- Do not know how to deal with expression ∃ i_1, dvd i x
  -- Non-dependent ∃, but whose domain type is a `Prop`
  example (x : Nat) (primeset : Nat → Prop) (dvd : Nat → Nat → Prop) :
    ((∃ (i : _) (i_1 : primeset i), dvd i x) ↔ (∃ p, primeset p ∧ dvd p x)) := by
    auto

  -- Brute force example
  -- This must be fixed
  set_option auto.redMode "instances" in
  example : (∀ (m n k : Nat), m + n + k = m + (n + k)) := by
    intros m n k; revert m n; induction k
    case zero => auto u[Nat.add] d[Nat.rec]

end Issues
