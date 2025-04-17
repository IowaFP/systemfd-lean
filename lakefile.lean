import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.19.0-rc3"

package SystemFD
  -- add package configuration options here

lean_lib SystemFD
  -- add library configuration options here
lean_lib Hs


@[default_target]
lean_exe systemfd where
  root := `Main

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
