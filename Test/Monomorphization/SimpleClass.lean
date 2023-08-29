import Auto.Tactic

set_option auto.prep.redMode "reducible"
set_option trace.auto.tactic true
set_option trace.auto.mono true

set_option trace.auto.printLemmas true in
set_option trace.auto.mono.printConstInst true in
set_option trace.auto.mono.printLemmaInst true in
example (as bs cs ds : List β) : (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cd ++ ds)) := by
  try auto [List.append_assoc]
  sorry

set_option trace.auto.printLemmas true in
set_option trace.auto.mono.printLemmaInst true in
example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  try auto [List.append_assoc, List.map_append]
  sorry