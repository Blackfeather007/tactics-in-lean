import Lake
open Lake DSL

package «TacticsInLean» where
    leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «TacticsInLean» where
  -- add library configuration options here
  globs := #[.submodules `TacticsInLean]

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.14.0"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.14.0"
