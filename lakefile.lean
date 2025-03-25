import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.18.0-rc1"

package SystemFD
  -- add package configuration options here

lean_lib SystemFD
  -- add library configuration options here
lean_lib Hs


@[default_target]
lean_exe systemfd where
  root := `Main
