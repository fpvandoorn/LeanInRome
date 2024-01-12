import Lake
open Lake DSL

def serverOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

package «leanInRome» where
  moreServerOptions := serverOptions

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"e659b1b3c9ad1535ef5f4ec13280a382fe457aee"

@[default_target]
lean_lib «LeanInRome» where
