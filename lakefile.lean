import Lake
open Lake DSL

package ssreflect where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "v4.20.0-rc2"

abbrev defaultOptions : Array LeanOption := #[⟨`Elab.async, false⟩]

@[default_target]
lean_lib Ssreflect where
  -- add any library configuration options here

@[default_target]
lean_lib Examples {
  globs := #[.submodules `Examples]
  leanOptions := defaultOptions
}

@[default_target]
lean_lib Talk {
  globs := #[.submodules `Talk]
  leanOptions := defaultOptions ++ #[⟨`linter.unusedVariables, false⟩]
}

@[default_target]
lean_lib Tests {
  globs := #[.submodules `Tests]
  leanOptions := defaultOptions ++ #[⟨`linter.unusedVariables, false⟩]
}
