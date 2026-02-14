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
    git "https://github.com/leanprover-community/batteries" @ "v4.26.0"

@[default_target]
lean_lib Ssreflect {
  globs := #[.submodules `Ssreflect]
}
  -- add any library configuration options here

lean_lib Examples {
  globs := #[.submodules `Examples]
}

lean_lib Talk {
  globs := #[.submodules `Talk]
}

lean_lib Tests {
  globs := #[.submodules `Tests]
  leanOptions := #[⟨`linter.unusedVariables, false⟩]
}
