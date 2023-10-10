import Lean
open Lean

namespace Auto.Debugger

initialize Idbg.stack : IO.Ref (Array String) ← IO.mkRef #[]

def Idbg.clearStack : IO Unit := Idbg.stack.set #[]

end Auto.Debugger