import Lake
open Lake DSL

package «lean-circuit» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"ea67efc21e4e1496f0a1d954cd0c0a952523133a"

lean_lib LeanCircuit {
  -- add library configuration options here
}

-- require mathlib from git
--   "https://github.com/reilabs/proven-zk.git"

require ProvenZK from ".."/".."/"proven-zk"

@[default_target]
lean_exe «lean-circuit» {
  moreLeanArgs := #["--tstack=1000000"]
  root := `Main
}
