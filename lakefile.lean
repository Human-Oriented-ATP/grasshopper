import Lake
open Lake DSL

package «Grasshopper» where
  -- add package configuration options here

lean_lib «Grasshopper» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

@[default_target]
lean_exe «grasshopper» where
  root := `Main
