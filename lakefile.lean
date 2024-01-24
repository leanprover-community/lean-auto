import Lake
open Lake DSL

package «auto» {
  precompileModules := true
  preferReleaseBuild := true
}

require std from git
  "https://github.com/leanprover/std4.git"@"3959bc5de5142d06d7673ec091d406e5abe45bf0"

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
