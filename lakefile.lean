import Lake
open Lake DSL

package «ELFSage» where
  -- add package configuration options here

require Cli from git
  "https://github.com/leanprover/lean4-cli.git"@"28e0856d4424863a85b18f38868c5420c55f9bae"

lean_lib «ELFSage» where
  -- add library configuration options here

@[default_target]
lean_exe «elfsage» where
  root := `Main

lean_exe test where
  root := `Test
