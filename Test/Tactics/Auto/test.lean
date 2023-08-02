import Auto.Tactic

-- Collecting `logical constructors`

set_option trace.auto.printLemmas true
set_option trace.auto.lamULift true

set_option pp.universes true in
example : True := by
  auto [True.intro];

example : True := by
  try auto p [Or.inl, Or.inr];
  sorry

example : True := by
  try auto p [And.intro];
  sorry