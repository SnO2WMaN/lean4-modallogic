import Lake
open Lake DSL

package «modallogic» {
  -- add package configuration options here
}

lean_lib «Modallogic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «modallogic» {
  root := `Main
}
