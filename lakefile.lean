/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
import Lake

open Lake DSL

package "restricted-product-duality" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "e37d88a26f3791ed5a93daa1f949af1021b8d103"

@[default_target]
lean_lib RestrictedProductDuality

@[default_target]
lean_lib RestrictedProductDualityTest
