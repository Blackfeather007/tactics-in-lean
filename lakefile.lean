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
