import Lake
open Lake DSL

package «auto» {
  -- add any package configuration options here
}

require std from git
  "https://github.com/leanprover/std4.git"@"main"

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
