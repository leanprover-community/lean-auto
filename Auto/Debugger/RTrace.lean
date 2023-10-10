import Lean
open Lean

namespace Auto.Debugger

initialize
  registerTraceClass `auto.debugger.rtrace

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

initialize RTrace.rtraceState : IO.Ref (HashMap String (Range × Nat)) ← IO.mkRef {}

def RTrace.printRTraceClass (clsName : String) : IO Unit := do
  if let .some range := (← rtraceState.get).find? clsName then
    IO.println s!"Class range: {range.fst.data}, Current index: {range.snd}"
  else
    throw (IO.userError s!"Unknown RTrace Class {clsName}")

def RTrace.setRTraceClass (clsName : String) (intervals : Range) : IO Unit := do
  let range := (@id Range #[]).adds intervals
  rtraceState.set ((← rtraceState.get).insert clsName (range, 0))

def RTrace.addToRTraceClass (clsName : String) (intervals : Range) : IO Unit := do
  let range := ((← rtraceState.get).find? clsName).getD (#[], 0)
  rtraceState.set ((← rtraceState.get).insert clsName (range.fst.adds intervals, 0))

def RTrace.clearRTraceClass (clsName : String) : IO Unit := do
  rtraceState.set ((← rtraceState.get).insert clsName (#[], 0))

def RTrace.resetRTrace : IO Unit := do
  let state := ← rtraceState.get
  rtraceState.set (HashMap.ofList (state.toList.map (fun (name, (r, _)) => (name, (r, 0)))))

syntax (name := printRTraceClass) "#printRTraceClass" str : command
syntax (name := setRTraceClass) "#setRTraceClass" str "[" ( "(" num "," num ")" ) ,* "]" : command
syntax (name := addToRTraceClass) "#addToRTraceClass" str "[" ( "(" num "," num ")" ) ,* "]" : command
syntax (name := clearRTraceClass) "#clearRTraceClass" str : command
syntax (name := resetRTrace) "#resetRTrace": command

open Elab Command

@[command_elab printRTraceClass]
def elabPrintRTraceClass : CommandElab := fun stx => do
  match stx with
  | `(printRTraceClass | #printRTraceClass $clsName) =>
    let clsName := clsName.getString
    RTrace.printRTraceClass clsName
  | _ => throwUnsupportedSyntax

@[command_elab setRTraceClass]
def elabSetRTraceClass : CommandElab := fun stx => do
  match stx with
  | `(setRTraceClass | #setRTraceClass $clsName [$[($a, $b)],*]) =>
    let clsName := clsName.getString
    let lbs := a.map (fun stx => stx.getNat)
    let ubs := b.map (fun stx => stx.getNat)
    RTrace.setRTraceClass clsName (lbs.zip ubs)
  | _ => throwUnsupportedSyntax

@[command_elab addToRTraceClass]
def elabAddToRTraceClass : CommandElab := fun stx => do
  match stx with
  | `(addToRTraceClass | #addToRTraceClass $clsName [$[($a, $b)],*]) =>
    let clsName := clsName.getString
    let lbs := a.map (fun stx => stx.getNat)
    let ubs := b.map (fun stx => stx.getNat)
    RTrace.addToRTraceClass clsName (lbs.zip ubs)
  | _ => throwUnsupportedSyntax

@[command_elab clearRTraceClass]
def elabClearRTraceClass : CommandElab := fun stx => do
  match stx with
  | `(clearRTraceClass | #clearRTraceClass $clsName) =>
    let clsName := clsName.getString
    RTrace.clearRTraceClass clsName
  | _ => throwUnsupportedSyntax

@[command_elab resetRTrace]
def elabResetRTrace : CommandElab := fun stx => do
  match stx with
  | `(resetRTrace | #resetRTrace) =>
    RTrace.resetRTrace
  | _ => throwUnsupportedSyntax

def rguard [Monad m] [MonadLiftT IO m] (clsName : String) (action : m Unit) : m Unit := do
  let state ← @id (IO _) <| RTrace.rtraceState.get
  match state.find? clsName with
  | .some (range, idx) =>
    if range.contains idx then action
    @id (IO _ ) <| RTrace.rtraceState.set (state.insert clsName (range, idx + 1))
  | .none => pure ()

def rtrace [Monad m] [MonadLiftT IO m] [MonadTrace m] [MonadRef m] [AddMessageContext m]
  (clsName : String) (msg : MessageData) : m Unit := do
  let state ← @id (IO _) <| RTrace.rtraceState.get
  match state.find? clsName with
  | .some (range, idx) =>
    if range.contains idx then (addTrace `auto.debugger.rtrace (m!"{clsName} {idx} : " ++ msg))
    @id (IO _ ) <| RTrace.rtraceState.set (state.insert clsName (range, idx + 1))
  | .none => pure ()

end Auto.Debugger