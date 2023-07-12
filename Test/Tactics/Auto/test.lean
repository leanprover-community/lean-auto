import Auto.Tactic

-- Collecting `logical constructors`

set_option trace.auto.printLemmas true

example : True := by
  try auto [True.intro];
  sorry

example : True := by
  try auto [Or.inl, Or.inr];
  sorry

example : True := by
  try auto [And.intro];
  sorry