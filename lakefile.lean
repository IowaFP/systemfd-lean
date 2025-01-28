import Lake
open Lake DSL

package SystemFD where
  -- add package configuration options here

lean_lib SystemFD where
  -- add library configuration options here

@[default_target]
lean_exe systemfd where
  root := `Main
