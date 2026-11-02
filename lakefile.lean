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
    "ce98f182cebbd2ae549dc9e7de6882a6f860cc7b"

require groupTheory from git
  "https://github.com/FormalFrontier/group-theory.git" @
    "aad807ee05018f3a7b45cea81aeed190112a7b75"

require complexAnalysis from git
  "https://github.com/FormalFrontier/complex-analysis.git" @
    "ec0323f84c5bf2e6639f4a4a02955264baa94e6a"

@[default_target]
lean_lib RestrictedProductDuality

@[default_target]
lean_lib RestrictedProductDualityTest where
  leanOptions := #[⟨`weak.linter.privateModule, false⟩]
