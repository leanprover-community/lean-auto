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

end TPTP

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
