import Lake
open Lake DSL

package workspace

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

@[default_target]
lean_lib WorkspaceTheorems

lean_lib MiniF2F
