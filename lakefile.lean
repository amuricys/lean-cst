import Lake
open Lake DSL

package «lean-cst» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"

lean_lib «LeanCst» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-cst» where
  root := `Main
