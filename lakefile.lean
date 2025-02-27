import Lake
open Lake DSL

package "lean-lake" where
  version := v!"0.1.0"

lean_lib «LeanLake» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-lake" where
  root := `Main
