/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import RestrictedProductDuality.FiniteStageColimit
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite products and the empty-index boundary

For two real coordinates with given zero points, the terminal finite stage is the
ordinary plane. A proper stage inserts zero in its missing coordinate. Coordinate
zero evaluation defines a cocone whose categorical descendant distinguishes
`(1, 0)` from `(0, 0)`.

For an empty index type there is one finite subset, not an empty diagram. Its ordinary
Pi stage and the original restricted product are singletons. The descendant of any
compatible family takes the value supplied by the empty stage, without requiring a
chosen point in the observer.
-/

noncomputable section

open CategoryTheory RestrictedProduct RestrictedProduct.SingletonPathComponents

universe w

namespace RestrictedProductTest.FiniteStageColimit

private def realZero : Fin 2 → ℝ := fun _ ↦ 0

/-- The full ordinary finite Pi stage, identified with the real plane. -/
private def realPlaneStage : (∀ _j : (Finset.univ : Finset (Fin 2)), ℝ) ≃ₜ ℝ × ℝ where
  toFun xs := (xs ⟨0, Finset.mem_univ 0⟩, xs ⟨1, Finset.mem_univ 1⟩)
  invFun z j := if (j : Fin 2) = 0 then z.1 else z.2
  left_inv := by
    intro xs
    have h : ∀ i : Fin 2,
        (if i = 0 then xs ⟨0, Finset.mem_univ 0⟩ else xs ⟨1, Finset.mem_univ 1⟩) =
          xs ⟨i, Finset.mem_univ i⟩ :=
      Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
    funext j
    exact h j
  right_inv := by
    intro z
    apply Prod.ext <;> simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_apply (⟨0, Finset.mem_univ 0⟩ :
        (Finset.univ : Finset (Fin 2)))
    · exact continuous_apply (⟨1, Finset.mem_univ 1⟩ :
        (Finset.univ : Finset (Fin 2)))
  continuous_invFun := by
    apply continuous_pi
    intro j
    by_cases hj : (j : Fin 2) = 0
    · simpa only [ite_eq_left hj] using
        (continuous_fst : Continuous (fun z : ℝ × ℝ ↦ z.1))
    · simpa only [ite_eq_right hj] using
        (continuous_snd : Continuous (fun z : ℝ × ℝ ↦ z.2))

private def realCoordinateZeroFamily (s : Finset (Fin 2)) :
    C((∀ _j : s, ℝ), ℝ) where
  toFun xs := singletonFinsetInsert realZero s xs 0
  continuous_toFun :=
    (RestrictedProduct.continuous_eval (0 : Fin 2)).comp
      (continuous_singletonFinsetInsert realZero s)

private theorem realCoordinateZeroFamily_compatible :
    ∀ {s t : Finset (Fin 2)}, s ⊆ t →
      (realCoordinateZeroFamily t).comp (singletonFinsetMap realZero s t) =
        realCoordinateZeroFamily s := by
  intro s t hst
  apply ContinuousMap.ext
  intro xs
  exact congrArg (fun x : PointProduct realZero ↦ x 0)
    (singletonFinsetInsert_map realZero hst xs)

/-- Coordinate-zero evaluation as a cocone with point the real line. -/
private def realCoordinateZeroCocone :
    CategoryTheory.Limits.Cocone (singletonFinsetDiagram realZero) where
  pt := TopCat.of ℝ
  ι :=
    { app := fun s ↦ TopCat.ofHom (realCoordinateZeroFamily s)
      naturality := by
        -- Apply `realCoordinateZeroFamily_compatible (leOfHom h)` to an arrow `h`.
        -- Its continuous-map equality gives naturality after applying `TopCat.ofHom`.
        intro s t h
        change TopCat.ofHom ((realCoordinateZeroFamily t).comp
          (singletonFinsetMap realZero s t)) = TopCat.ofHom (realCoordinateZeroFamily s)
        exact congrArg TopCat.ofHom
          (realCoordinateZeroFamily_compatible (leOfHom h)) }

/-- The top-stage leg is an isomorphism; the proper stage really inserts zero.
Categorical descent of coordinate evaluation is nonconstant on the original product. -/
private theorem real_plane_desc :
    IsIso ((singletonFinsetCocone realZero).ι.app Finset.univ) ∧
      singletonFinsetInsert realZero {0} (fun _ ↦ (1 : ℝ)) 0 = 1 ∧
      singletonFinsetInsert realZero {0} (fun _ ↦ (1 : ℝ)) 1 = 0 ∧
      (singletonFinsetCoconeIsColimit realZero).desc realCoordinateZeroCocone
        (singletonFinsetInsert realZero Finset.univ (realPlaneStage.symm (1, 0))) = (1 : ℝ) ∧
      (singletonFinsetCoconeIsColimit realZero).desc realCoordinateZeroCocone
        (singletonFinsetInsert realZero Finset.univ (realPlaneStage.symm (0, 0))) = (0 : ℝ) := by
  refine ⟨by
    have hsurj : Function.Surjective (singletonFinsetInsert realZero Finset.univ) := by
      intro x
      refine ⟨Finset.univ.restrict (fun i ↦ x i), ?_⟩
      exact singletonFinsetInsert_restrict realZero Finset.univ x (by
        intro i hi
        exact False.elim (hi (Finset.mem_univ i)))
    exact TopCat.isIso_of_bijective_of_isOpenMap _
      ⟨(isEmbedding_singletonFinsetInsert realZero Finset.univ).injective, hsurj⟩
      ((isEmbedding_singletonFinsetInsert realZero Finset.univ).isOpenEmbedding_of_surjective
        hsurj).isOpenMap
  , by
    exact singletonFinsetInsert_apply_of_mem realZero {0} (fun _ ↦ (1 : ℝ)) 0 (by simp)
  , by
    exact singletonFinsetInsert_apply_of_notMem realZero {0} (fun _ ↦ (1 : ℝ)) 1 (by simp)
  , ?_, ?_⟩
  · refine (singletonFinsetCoconeIsColimit_desc_apply realZero realCoordinateZeroCocone
      Finset.univ (realPlaneStage.symm (1, 0))).trans ?_
    change singletonFinsetInsert realZero Finset.univ (realPlaneStage.symm (1, 0)) 0 = 1
    rw [singletonFinsetInsert_apply_of_mem realZero Finset.univ _ 0 (Finset.mem_univ 0)]
    rfl
  · refine (singletonFinsetCoconeIsColimit_desc_apply realZero realCoordinateZeroCocone
      Finset.univ (realPlaneStage.symm (0, 0))).trans ?_
    change singletonFinsetInsert realZero Finset.univ (realPlaneStage.symm (0, 0)) 0 = 0
    rw [singletonFinsetInsert_apply_of_mem realZero Finset.univ _ 0 (Finset.mem_univ 0)]
    rfl

private def emptyZero : Empty → ℝ := fun _ ↦ 0

private def emptyStagePoint : ∀ _j : (∅ : Finset Empty), ℝ := fun _ ↦ 0

/-- There is one empty stage, both carriers are singletons, and the descendant's value
is supplied by that stage. The observer is arbitrary and has no specified basepoint. -/
private theorem empty_index_desc {Y : Type w} [TopologicalSpace Y]
    (f : ∀ s : Finset Empty, C((∀ _j : s, ℝ), Y))
    (hf : ∀ {s t : Finset Empty}, s ⊆ t → (f t).comp (singletonFinsetMap emptyZero s t) = f s) :
    (∀ s : Finset Empty, s = ∅) ∧
      (∀ xs ys : (∀ _j : (∅ : Finset Empty), ℝ), xs = ys) ∧
      (∀ x y : PointProduct emptyZero, x = y) ∧
      singletonFinsetDesc emptyZero f hf (singletonFinsetInsert emptyZero ∅ emptyStagePoint) =
        f ∅ emptyStagePoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact Finset.ext (fun i ↦ Empty.elim i)
  · intro xs ys
    exact funext (fun j ↦ Empty.elim j.1)
  · intro x y
    apply RestrictedProduct.ext
    intro i
    exact Empty.elim i
  · exact singletonFinsetDesc_insert emptyZero f hf ∅ emptyStagePoint

end RestrictedProductTest.FiniteStageColimit
