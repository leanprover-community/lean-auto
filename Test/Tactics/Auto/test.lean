import Auto.Tactic

-- Collecting `logical constructors`

set_option trace.auto.printLemmas true

example : True := by
  try auto p [True.intro];
  sorry

example : True := by
  try auto p [Or.inl, Or.inr];
  sorry

example : True := by
  try auto p [And.intro];
  sorry