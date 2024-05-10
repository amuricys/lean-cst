import Lake
open Lake DSL

package «lean-cst» where
  -- add package configuration options here

lean_lib «LeanCst» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-cst» where
  root := `Main
