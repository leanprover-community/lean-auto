import Lean
open Lean

/-
  This file is here so that code in `Auto/Solver` can find
  the path to the source code folder of `lean-auto` by
  ``Lean.findOLean `Auto.Lib.PathHook``
-/

namespace Auto

namespace PathHook

def hookName : Name := `Auto.Lib.PathHook

end PathHook

end Auto
