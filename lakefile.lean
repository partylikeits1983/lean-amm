import Lake
open Lake DSL

package «Amm» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Amm» where
  srcDir := "."

lean_lib «AmmTest» where
  srcDir := "."
  globs := #[.submodules `AmmTest]
