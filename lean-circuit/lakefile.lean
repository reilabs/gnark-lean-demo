import Lake
open Lake DSL

package «lean-circuit» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"ea67efc21e4e1496f0a1d954cd0c0a952523133a"

require ProvenZK from git
  "https://github.com/reilabs/proven-zk.git"@"fa2a6b0dda0f94554fc511181a711415c2eb58fe"

lean_lib LeanCircuit {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean-circuit» {
  moreLeanArgs := #["--tstack=1000000"]
  root := `Main
}
