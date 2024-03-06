import Lake
open Lake DSL

package Ssreflect where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib Ssreflect where
  -- add any library configuration options here

@[default_target]
lean_lib Examples {
  globs := #[.submodules "Examples"]
}

@[default_target]
lean_lib Tests {
  globs := #[.submodules "Tests"]
  leanOptions := #[⟨`linter.unusedVariables, false⟩]
}
