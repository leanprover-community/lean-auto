import Lean
open Lean

def spawnSleep (n : Nat) : IO UInt32 := do
  let proc ← IO.Process.spawn
    {stdin := .piped, stdout := .piped, stderr := .piped, cmd := "sleep", args := #[s!"{n}"]}
  proc.wait

-- Type something here --> <-- multiple times to interrupt the normal execution of the following command
#eval spawnSleep 10
