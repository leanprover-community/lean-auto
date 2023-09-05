import Auto.Tactic

axiom Real : Type
axiom dist : Real → Real → Real 
axiom add : Real → Real → Real 
axiom lt : Real → Real → Prop 
axiom zero : Real
axiom one : Real
axiom dist_self (a : Real) : dist a a = zero
axiom zero_lt_one (a : Real) : lt zero one

def continuous_at (f : Real → Real) (x₀ : Real) :=
  ∀ ε : Real, lt zero ε → ∃ δ : Real, lt zero δ ∧
    ∀ x, lt (dist x x₀) δ → lt (dist (f x) (f x₀)) ε

def continuous (f : Real → Real) := ∀ x, continuous_at f x

def uniformly_continuous (f : Real → Real) :=
  ∀ ε : Real, lt zero ε → ∃ δ : Real, lt zero δ ∧
    ∀ x y, lt (dist x y) δ → lt (dist (f x) (f y)) ε

example (a : Real) : continuous (λ _ => a) :=
  by auto [dist_self] u[continuous, continuous_at]

example (a : Real) : uniformly_continuous (λ _ => a) :=
  by auto [dist_self, zero_lt_one] u[uniformly_continuous]

example : continuous (λ x => x) :=
  by auto [dist_self] u[continuous, continuous_at]

example : uniformly_continuous (λ x => x) :=
  by auto [dist_self, zero_lt_one] u[uniformly_continuous]

example (f : Real → Real) : uniformly_continuous f → continuous f :=
  by auto u[continuous, continuous_at, uniformly_continuous]