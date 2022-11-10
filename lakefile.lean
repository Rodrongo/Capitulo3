import Lake
open Lake DSL

package scripts {
  -- add package configuration options here
}

lean_lib Scripts {
  -- add library configuration options here
}

@[default_target]
lean_exe scripts {
  root := `Main
}
