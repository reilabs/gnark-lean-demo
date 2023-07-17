import Lake
open Lake DSL

package «lean-circuit» {
  -- add package configuration options here
}

-- require ProvenZk from git
--   "https://github.com/reilabs/proven-zk.git"

require ProvenZk from ".."/".."/"proven-zk"

@[default_target]
lean_exe «lean-circuit» {
  moreLeanArgs := #["--tstack=1000000"]
  -- add any library configuration options here
}
