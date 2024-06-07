import Lake
open Lake DSL

package «lean-machines» where
  -- add package configuration options here

lean_lib «LeanMachines» where
  -- add library configuration options here

lean_lib «Examples» where

@[default_target]
lean_exe «lean-machines» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
