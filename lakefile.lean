import Lake
open Lake DSL

package «leanInRome» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «LeanInRome» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"e659b1b3c9ad1535ef5f4ec13280a382fe457aee"
