import Lean

open Lean

namespace EvalAuto

def mathlibModules : CoreM (Array Name) := do
  let u := (← getEnv).header.moduleNames
  return u.filter (fun name => name.components[0]? == .some `Mathlib)

/-- Pick `n` elements from array `xs`. Elements may duplicate -/
def Array.randPick {α} (xs : Array α) (n : Nat) : IO (Array α) := do
  let mut ret := #[]
  for _ in [0:n] do
    let rd ← IO.rand 0 (xs.size - 1)
    if h : rd < xs.size then
      ret := ret.push (xs[rd]'h)
  return ret

end EvalAuto
