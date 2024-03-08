import Lake
open Lake DSL

package «event-systems» where
  -- add package configuration options here

lean_lib «EventSystems» where
  -- add library configuration options here

@[default_target]
lean_exe «event-systems» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
