import Lake
open Lake DSL

package "partial_order_tactic" where
  -- add package configuration options here

lean_lib «PartialOrderTactic» where
  -- add library configuration options here

@[default_target]
lean_exe "partial_order_tactic" where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"
