/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.MeasureTheory.Integral.Kernel
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.UrysohnsLemma

/-!
# A specified evaluation defect for compact-group convolution

For any nonidentity point of a compact Hausdorff topological group, some continuous
convolution kernel sends a continuous input to a function with different values at
that point and at the identity. The measure need only be finite and positive on
nonempty open sets; translation invariance is not required.

Urysohn separation supplies the kernel, and injectivity of the continuous-function
embedding into L² turns its conjugate slice difference into a nonzero test input.
This result does not assert character separation or spectral invariance.
-/

public section

universe u

open MeasureTheory

namespace ContinuousMap

/-- Every specified nonidentity point is detected by an output of a genuine convolution
kernel. This holds for arbitrary compact Hausdorff topological groups and finite Borel
measures positive on nonempty opens, without commutativity or translation invariance. -/
theorem exists_kernelOperator_comp_mul_inv_ne
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {x : K} (hx : x ≠ 1) :
    ∃ f h : C(K, ℂ),
      let κ : C(K × K, ℂ) :=
        f.comp ⟨fun p : K × K => p.1 * p.2⁻¹,
          continuous_fst.mul continuous_snd.inv⟩
      kernelOperator μ κ (toLp (E := ℂ) (2 : ENNReal) μ ℂ h) x ≠
        kernelOperator μ κ (toLp (E := ℂ) (2 : ENNReal) μ ℂ h) 1 := by
  obtain ⟨r, hrx, hr1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({x} : Set K))
    (isClosed_singleton : IsClosed ({(1 : K)} : Set K))
    (by simpa using hx : Disjoint ({x} : Set K) ({(1 : K)} : Set K))
  have hrx' : r x = 0 := hrx (by simp)
  have hr1' : r (1 : K) = 1 := hr1 (by simp)
  let f : C(K, ℂ) := ⟨fun y => (r y : ℂ), Complex.continuous_ofReal.comp r.continuous⟩
  have hfx : f x = 0 := by simp [f, hrx']
  have hf1 : f (1 : K) = 1 := by simp [f, hr1']
  let κ : C(K × K, ℂ) :=
    f.comp ⟨fun p : K × K => p.1 * p.2⁻¹,
      continuous_fst.mul continuous_snd.inv⟩
  let h : C(K, ℂ) := star (κ.curry x - κ.curry 1)
  have hh1 : h 1 = -1 := by simp [h, κ, hfx, hf1]
  have hh : h ≠ 0 := by
    intro hz
    have hz1 : h 1 = 0 := congrArg (fun g : C(K, ℂ) => g 1) hz
    rw [hh1] at hz1
    exact (neg_ne_zero.mpr one_ne_zero) hz1
  let J := toLp (E := ℂ) (2 : ENNReal) μ ℂ
  have hJinj : Function.Injective J :=
    toLp_injective (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ)
  have hJh : J h ≠ 0 := by
    intro hz
    exact hh (hJinj (by simpa using hz))
  have hJ : J h = J (star (κ.curry x)) - J (star (κ.curry 1)) := by
    dsimp [h]
    rw [star_sub, map_sub]
  refine ⟨f, h, ?_⟩
  change kernelOperator μ κ (J h) x ≠ kernelOperator μ κ (J h) 1
  intro heq
  have hz : inner ℂ (J h) (J h) = 0 := by
    calc
      inner ℂ (J h) (J h) =
          inner ℂ (J (star (κ.curry x)) - J (star (κ.curry 1))) (J h) :=
        congrArg (fun v => inner ℂ v (J h)) hJ
      _ = kernelOperator μ κ (J h) x - kernelOperator μ κ (J h) 1 := by
        rw [inner_sub_left, kernelOperator_apply_eq_inner, kernelOperator_apply_eq_inner]
      _ = 0 := sub_eq_zero.mpr heq
  exact hJh (inner_self_eq_zero.mp hz)

end ContinuousMap
