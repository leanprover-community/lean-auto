import Lake
open Lake DSL

package «auto» {
  -- add any package configuration options here
}

require std from git
  "https://github.com/leanprover/std4.git"@"9e37a01f8590f81ace095b56710db694b5bf8ca0"

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
