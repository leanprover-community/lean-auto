import Lake
open Lake DSL

package «auto» {
  precompileModules := true
}

require std from git
  "https://github.com/leanprover/std4.git"@"nightly-testing-2024-02-20"

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
