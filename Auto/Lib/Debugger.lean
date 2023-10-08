import Lean
open Lean


namespace Auto.RTrace

/--
  If we're debugging a program, but there are so many trace messages
    that Lean crashes, we will want to choose the range of trace
    messages that we see (e.g. we want to see the 200th-300th trace
    messages and the 500th-550th trace messages). We might also want
    to see trace messages that contain specific substrings.
  
  `Range` represents an array of left-closed, right-open non-empty
    intervals on natural numbers, such that they're disjoint and are
    ordered with respect to the ordering of natural numbers.
-/
abbrev Range := Array (Nat × Nat)

def Range.wf (r : Range) : Bool :=
  r.size == 0 || (r.all (fun (a, b) => a < b) &&
    (r.pop.zip (r.eraseIdx 0)).all (fun ((_, a), (b, _)) => a ≤ b))

def Range.contains (r : Range) (n : Nat) : Bool := r.any (fun (l, r) => l ≤ n ∧ n < r)

def Range.add (r : Range) (interval : Nat × Nat) : Range := Id.run <| do
  let (a, b) := interval
  if a ≥ b then return r
  let mut ret := #[]
  let mut curl := a
  let mut curr := b
  let mut done := false
  for (li, ri) in r do
    if done || ri < curl then
      ret := ret.push (li, ri)
      continue
    if li > curr then
      ret := ret.push (curl, curr)
      ret := ret.push (li, ri)
      done := true; continue
    -- Now `ri ≥ curl` and `li ≤ curr`
    curl := Nat.min li curl
    curr := Nat.max ri curr
  if !done then ret := ret.push (curl, curr)
  return ret

def Range.adds (r : Range) (intervals : Range) : Range :=
  intervals.foldl (fun cur i => cur.add i) r

initialize rtraceExt : IO.Ref (HashMap String Range) ← IO.mkRef {}

def declareRTraceClass (clsName : String) : IO Unit := do
  rtraceExt.set ((← rtraceExt.get).insert clsName #[])

private def throwUnregisteredRTraceClass (clsName action : String) : IO Unit :=
  let cmdstr := "?? " ++ clsName
  throw (IO.userError <| "Please declare rtrace class using " ++
    s!"command {repr cmdstr} before {action}")

def addToRTraceClass (clsName : String) (intervals : Range) : IO Unit := do
  let .some range := (← rtraceExt.get).find? clsName
    | throwUnregisteredRTraceClass clsName "adding interval to it"
  rtraceExt.set ((← rtraceExt.get).insert clsName (range.adds intervals))

end RTrace

end Auto