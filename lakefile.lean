/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
import Lake

open Lake DSL

package "restricted-product-duality" where
  version := v!"0.1.0"
  lintDriver := "batteries/runLinter"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "83abb3e776bdefcbc447a1e44d0debe4010039e5"

require «fundamental-groupoids» from git
  "https://github.com/FormalFrontier/fundamental-groupoids.git" @
    "2d276f19865bb972d0b07221e0979083fff06c4c"

@[default_target]
lean_lib RestrictedProductDuality

@[default_target]
lean_lib RestrictedProductDualityTest where
  leanOptions := #[⟨`weak.linter.privateModule, false⟩]
