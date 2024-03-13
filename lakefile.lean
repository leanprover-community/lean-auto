import Lake
open Lake DSL

package «auto» {
  precompileModules := true
  preferReleaseBuild := true
}

require std from git
  "https://github.com/leanprover/std4.git"@"nightly-testing-2024-02-18"

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
