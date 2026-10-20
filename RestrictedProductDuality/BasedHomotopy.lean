/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.HomotopyMaps

/-!
# Based homotopies on singleton restricted products

A family of homotopies relative to the chosen source points induces a homotopy
relative to the canonical point of the singleton-cofinite restricted product.
At every time and coordinate it is the given coordinate homotopy. The endpoint
maps are the coordinatewise based maps `RestrictedProduct.SingletonNaturality.pointMap`.

The factor spaces have arbitrary topologies, and the index type may be empty.
The parameter is the usual unit interval; no local compactness or separation
assumption on the factors is used. The induced path-component maps and positive
homotopy-group homomorphisms are independent of the chosen based-homotopic endpoint.
These statements do not invoke the T1-dependent positive comparison equivalences.

## References

This construction uses Mathlib's relative homotopies, generalized loops, and
homotopy quotients, together with the singleton finite-stage and based
postcomposition APIs of this library. The finite-support-product viewpoint
occurs in J. P. May, *A Concise Course in Algebraic Topology*.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped unitInterval

universe u v w z

namespace RestrictedProduct.SingletonNaturality

open RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

/-- Coordinatewise based homotopies assemble to a homotopy between the canonical
restricted-product maps, relative to the canonical source point. -/
def pointMapHomotopyRel (b : ∀ i, X i) (c : ∀ i, Y i)
    (f g : ∀ i, C(X i, Y i))
    (hf : ∀ i, f i (b i) = c i) (hg : ∀ i, g i (b i) = c i)
    (H : ∀ i, ContinuousMap.HomotopyRel (f i) (g i) ({b i} : Set (X i))) :
    ContinuousMap.HomotopyRel (pointMap b c f hf) (pointMap b c g hg)
      ({RestrictedProduct.singletonBasepoint b} : Set (PointProduct b)) where
  toHomotopy :=
    { toFun := fun p ↦ ⟨fun i ↦ H i (p.1, p.2 i), by
        filter_upwards [p.2.2] with i hi
        change H i (p.1, p.2 i) = c i
        have hxi : p.2 i = b i := Set.mem_singleton_iff.mp hi
        exact Eq.trans (α := Y i)
          (congrArg (fun z : X i ↦ H i (p.1, z)) hxi)
          (((H i).eq_fst p.1 (by simp)).trans (hf i))⟩
      continuous_toFun := by
        classical
        have hbase (t : I) (i : ι) : H i (t, b i) = c i :=
          ((H i).eq_fst t (by simp)).trans (hf i)
        let h : I × PointProduct b → PointProduct c := fun p ↦
          ⟨fun i ↦ H i (p.1, p.2 i), by
            filter_upwards [p.2.2] with i hi
            change H i (p.1, p.2 i) = c i
            have hxi : p.2 i = b i := Set.mem_singleton_iff.mp hi
            exact Eq.trans (α := Y i)
              (congrArg (fun z : X i ↦ H i (p.1, z)) hxi) (hbase p.1 i)⟩
        change Continuous h
        -- The same finite set supports the output at every time.
        have hs (s : Finset ι) :
            Continuous (fun p : (∀ i : s, X i) × I ↦
              h (p.2, RestrictedProduct.singletonFinsetInsert b s p.1)) := by
          have heq : (fun p : (∀ i : s, X i) × I ↦
              h (p.2, RestrictedProduct.singletonFinsetInsert b s p.1)) =
              RestrictedProduct.singletonFinsetInsert c s ∘
                (fun p : (∀ i : s, X i) × I ↦ fun i : s ↦ H i (p.2, p.1 i)) := by
            funext p
            apply RestrictedProduct.ext
            intro i
            change H i (p.2, RestrictedProduct.singletonFinsetInsert b s p.1 i) =
              RestrictedProduct.singletonFinsetInsert c s
                (fun j : s ↦ H j (p.2, p.1 j)) i
            by_cases hi : i ∈ s
            · rw [RestrictedProduct.singletonFinsetInsert_apply_of_mem b s _ i hi,
                RestrictedProduct.singletonFinsetInsert_apply_of_mem c s _ i hi]
            · rw [RestrictedProduct.singletonFinsetInsert_apply_of_notMem b s _ i hi,
                RestrictedProduct.singletonFinsetInsert_apply_of_notMem c s _ i hi]
              exact hbase p.2 i
          rw [heq]
          apply (RestrictedProduct.continuous_singletonFinsetInsert c s).comp
          apply continuous_pi
          intro i
          exact (H i).continuous.comp
            (continuous_snd.prodMk ((continuous_apply i).comp continuous_fst))
        -- Bundle time paths first, then use finality with a compact-open observer.
        let F : PointProduct b → C(I, PointProduct c) := fun x ↦
          ⟨fun t ↦ h (t, x), by
            let s := RestrictedProduct.exceptionalFinset x
            have hx := RestrictedProduct.singletonFinsetInsert_restrict b s x
              (RestrictedProduct.mem_cofiniteStage_exceptionalFinset x)
            have ht : Continuous (fun t : I ↦ h
                (t, RestrictedProduct.singletonFinsetInsert b s
                  (s.restrict (fun i ↦ x i)))) :=
              (hs s).comp (continuous_const.prodMk continuous_id)
            simpa only [hx] using ht⟩
        have hF : Continuous F := by
          apply (RestrictedProduct.continuous_dom_singleton_iff b).mpr
          intro s
          exact ContinuousMap.continuous_of_continuous_uncurry
            (F ∘ RestrictedProduct.singletonFinsetInsert b s) (hs s)
        -- Only the interval, not any factor space, needs local compactness here.
        exact (ContinuousMap.continuous_uncurry_of_continuous
          (⟨F, hF⟩ : C(PointProduct b, C(I, PointProduct c)))).comp
            (continuous_snd.prodMk continuous_fst)
      map_zero_left := by
        intro x
        apply RestrictedProduct.ext
        intro i
        exact (H i).apply_zero (x i)
      map_one_left := by
        intro x
        apply RestrictedProduct.ext
        intro i
        exact (H i).apply_one (x i) }
  prop' := by
    intro t x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    apply RestrictedProduct.ext
    intro i
    exact (H i).eq_fst t (by simp)

/-- Evaluation of the assembled homotopy at every time and coordinate. -/
@[simp]
theorem pointMapHomotopyRel_apply (b : ∀ i, X i) (c : ∀ i, Y i)
    (f g : ∀ i, C(X i, Y i))
    (hf : ∀ i, f i (b i) = c i) (hg : ∀ i, g i (b i) = c i)
    (H : ∀ i, ContinuousMap.HomotopyRel (f i) (g i) ({b i} : Set (X i)))
    (t : I) (x : PointProduct b) (i : ι) :
    pointMapHomotopyRel b c f g hf hg H (t, x) i = H i (t, x i) :=
  rfl

/-- The canonical source point remains the canonical target point at every time. -/
@[simp]
theorem pointMapHomotopyRel_base (b : ∀ i, X i) (c : ∀ i, Y i)
    (f g : ∀ i, C(X i, Y i))
    (hf : ∀ i, f i (b i) = c i) (hg : ∀ i, g i (b i) = c i)
    (H : ∀ i, ContinuousMap.HomotopyRel (f i) (g i) ({b i} : Set (X i)))
    (t : I) :
    pointMapHomotopyRel b c f g hf hg H (t, RestrictedProduct.singletonBasepoint b) =
      RestrictedProduct.singletonBasepoint c := by
  apply RestrictedProduct.ext
  intro i
  exact ((H i).eq_fst t (by simp)).trans (hf i)

/-- Based-homotopic coordinate families induce the same map on path components. -/
theorem pathMap_pointMap_eq_of_homotopyRel (b : ∀ i, X i) (c : ∀ i, Y i)
    (f g : ∀ i, C(X i, Y i))
    (hf : ∀ i, f i (b i) = c i) (hg : ∀ i, g i (b i) = c i)
    (H : ∀ i, ContinuousMap.HomotopyRel (f i) (g i) ({b i} : Set (X i))) :
    pathMap (pointMap b c f hf) = pathMap (pointMap b c g hg) := by
  exact pathMap_eq_of_homotopy (pointMap b c f hf) (pointMap b c g hg)
    (pointMapHomotopyRel b c f g hf hg H).toHomotopy

/-- Based-homotopic coordinate families induce the same positive homotopy-group
homomorphism, with the supplied cube-index decidable equality and canonical groups. -/
theorem homotopyGroup_map_pointMap_eq_of_homotopyRel
    (N : Type z) [DecidableEq N] [Nonempty N]
    (b : ∀ i, X i) (c : ∀ i, Y i)
    (f g : ∀ i, C(X i, Y i))
    (hf : ∀ i, f i (b i) = c i) (hg : ∀ i, g i (b i) = c i)
    (H : ∀ i, ContinuousMap.HomotopyRel (f i) (g i) ({b i} : Set (X i))) :
    HomotopyGroup.map N (pointMap b c f hf) (pointMap_base b c f hf) =
      HomotopyGroup.map N (pointMap b c g hg) (pointMap_base b c g hg) := by
  exact HomotopyGroup.map_eq_of_homotopyRel N
    (pointMap b c f hf) (pointMap b c g hg)
    (pointMap_base b c f hf) (pointMap_base b c g hg)
    (pointMapHomotopyRel b c f g hf hg H)

end RestrictedProduct.SingletonNaturality
