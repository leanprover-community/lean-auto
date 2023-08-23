import Lake
open Lake DSL

package «auto» {
  precompileModules := true
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require duper from git
  "https://github.com/leanprover-community/duper.git"

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
