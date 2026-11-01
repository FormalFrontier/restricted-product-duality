/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuity of characters from continuous weights

A nonzero continuous complex-valued right weight makes its Circle-valued character
continuous. Only a multiplication and an identity on the domain are needed; no
compatibility between that multiplication and the topology is required.
-/

public section

universe u

namespace MonoidHom

/-- A Circle-valued character with a nonzero continuous complex-valued right weight
is continuous. The weight identity at the identity element expresses the character
as the weight divided by its nonzero value there. -/
theorem continuous_of_continuous_weight
    {G : Type u} [MulOneClass G] [TopologicalSpace G]
    (χ : G →* Circle) (w : C(G, ℂ)) (hw : w ≠ 0)
    (hweight : ∀ s g : G, w (s * g) = (χ g : ℂ) * w s) :
    Continuous χ := by
  have hw_one : w 1 ≠ 0 := by
    intro h
    apply hw
    apply ContinuousMap.ext
    intro g
    simpa [h] using hweight 1 g
  have hcoe : Continuous (fun g : G => (χ g : ℂ)) := by
    have heq : (fun g : G => (χ g : ℂ)) = fun g => w g / w 1 := by
      funext g
      apply (eq_div_iff hw_one).2
      simpa only [one_mul] using (hweight 1 g).symm
    rw [heq]
    exact w.continuous.div_const (w 1)
  exact continuous_induced_rng.2 hcoe

end MonoidHom
