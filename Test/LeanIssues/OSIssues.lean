import Lean
open Lean

def spawnSleep₁ (n : Nat) : IO Nat := do
  let proc ← IO.Process.spawn
    {stdin := .piped, stdout := .piped, stderr := .piped, cmd := "sleep", args := #[s!"{n}"]}
  let n ← proc.wait
  return n.toNat

def spawnSleep₂ (n : Nat) : IO Nat := do
  let proc ← IO.Process.spawn
    {stdin := .piped, stdout := .piped, cmd := "sleep", args := #[s!"{n}"]}
  let tsk ← IO.asTask proc.wait
  while true do
    IO.sleep 100
    if ← IO.checkCanceled then
      IO.cancel tsk
      break
    if ← IO.hasFinished tsk then
      break
  return 0

def spawnSleep₃ (n : Nat) : IO Nat := do
  IO.sleep (.ofNat (n * 1000))
  spawnSleep₁ n

def spin₁ : IO Unit := do
  let mut i := 0
  while true do
    i := i + 1
    if i % 10000000 == 0 then
      IO.println "Oh"

def spin₂ : IO Unit := do
  let mut i := 0
  while true do
    i := i + 1
    if i % 10000000 == 0 then
      IO.println "Oh"
    if ← IO.checkCanceled then
      break

-- Type something here --> <-- multiple times to interrupt the normal execution of the following command
-- #eval spawnSleep₃ 10
