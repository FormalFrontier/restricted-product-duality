/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Circle-valued characters with small image

This file packages the centered-small-arc argument which forces a subgroup of
the circle to be trivial.
-/

public section

set_option warningAsError true

open Set
open Real

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup whose image under a circle-valued homomorphism lies in the centered `π / 2` arc
is contained in the homomorphism's kernel. -/
theorem le_ker_of_mapsTo_centeredArc (S : Subgroup G) (f : G →* Circle)
    (hf : MapsTo f S (Circle.centeredArc (π / 2))) : S ≤ f.ker := by
  intro x hx
  refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
  simpa only [map_pow] using hf (S.pow_mem hx n)

end Subgroup
