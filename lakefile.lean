import Lake
open Lake DSL

package «auto» {
  precompileModules := true
}

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}
