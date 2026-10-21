/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.Connectivity
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# The colimit of the ordinary finite products

For given points `b i`, finite subsets of the index type form an inclusion diagram
of ordinary dependent products. Its maps insert `b i` in newly available coordinates.
The canonical cocone has the singleton cofinite restricted product as its point,
with its final finite-stage topology and the usual finite insertion maps as legs.

Compatible continuous maps on the stages descend to continuous maps on this same
restricted product, with an independent observer universe. The categorical colimit
construction uses this descent for the legs of any cocone.

## References

The restricted-product topology is Mathlib's construction due to Anatole Dedecker.
Finite insertion and finality are from `RestrictedProductDuality.PrincipalStage`;
the quotient map from the sum of finite products is from
`RestrictedProductDuality.Connectivity`. Descent uses Mathlib's
`ContinuousMap.sigma` and `Topology.IsQuotientMap.lift`, not a different carrier
or topology. The finite-support-product viewpoint occurs in J. P. May,
*A Concise Course in Algebraic Topology*.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace RestrictedProduct

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- Insert the given points outside `s`, then restrict to `t`.

This continuous map is defined for arbitrary finite subsets `s` and `t`.
The inclusion diagram uses it only when `s ⊆ t`. -/
def singletonFinsetMap (b : ∀ i, X i) (s t : Finset ι) :
    C((∀ j : s, X j), (∀ j : t, X j)) where
  toFun xs := t.restrict (fun i ↦ singletonFinsetInsert b s xs i)
  continuous_toFun := by
    exact continuous_pi fun j ↦
      (RestrictedProduct.continuous_eval (j : ι)).comp
        (continuous_singletonFinsetInsert b s)

/-- A transition keeps each coordinate belonging to its source stage. -/
@[simp]
theorem singletonFinsetMap_apply_of_mem (b : ∀ i, X i) (s t : Finset ι)
    (xs : ∀ j : s, X j) (j : t) (hj : (j : ι) ∈ s) :
    singletonFinsetMap b s t xs j = xs ⟨j, hj⟩ := by
  exact singletonFinsetInsert_apply_of_mem b s xs j hj

/-- A transition inserts the given point at each coordinate outside its source stage. -/
@[simp]
theorem singletonFinsetMap_apply_of_notMem (b : ∀ i, X i) (s t : Finset ι)
    (xs : ∀ j : s, X j) (j : t) (hj : (j : ι) ∉ s) :
    singletonFinsetMap b s t xs j = b j := by
  exact singletonFinsetInsert_apply_of_notMem b s xs j hj

/-- Restricting an insertion back to its own stage gives the identity. -/
@[simp]
theorem singletonFinsetMap_id (b : ∀ i, X i) (s : Finset ι) :
    singletonFinsetMap b s s = ContinuousMap.id (∀ j : s, X j) := by
  apply ContinuousMap.ext
  intro xs
  exact restrict_singletonFinsetInsert b s xs

/-- Once the intermediate stage contains the source, a second restriction of insertion
agrees with the direct map. The last finite subset need not contain either stage. -/
theorem singletonFinsetMap_comp (b : ∀ i, X i) {s t : Finset ι}
    (r : Finset ι) (hst : s ⊆ t) :
    (singletonFinsetMap b t r).comp (singletonFinsetMap b s t) =
      singletonFinsetMap b s r := by
  classical
  apply ContinuousMap.ext
  intro xs
  funext j
  change singletonFinsetMap b t r (singletonFinsetMap b s t xs) j =
    singletonFinsetMap b s r xs j
  by_cases hjs : (j : ι) ∈ s
  · rw [singletonFinsetMap_apply_of_mem b t r (singletonFinsetMap b s t xs) j (hst hjs),
      singletonFinsetMap_apply_of_mem b s t xs ⟨(j : ι), hst hjs⟩ hjs,
      singletonFinsetMap_apply_of_mem b s r xs j hjs]
  · by_cases hjt : (j : ι) ∈ t
    · rw [singletonFinsetMap_apply_of_mem b t r (singletonFinsetMap b s t xs) j hjt,
        singletonFinsetMap_apply_of_notMem b s t xs ⟨(j : ι), hjt⟩ hjs,
        singletonFinsetMap_apply_of_notMem b s r xs j hjs]
    · rw [singletonFinsetMap_apply_of_notMem _ _ _ _ _ hjt,
        singletonFinsetMap_apply_of_notMem _ _ _ _ _ hjs]

/-- Insertion into the restricted product commutes with transitions along inclusions. -/
theorem singletonFinsetInsert_map (b : ∀ i, X i) {s t : Finset ι} (hst : s ⊆ t)
    (xs : ∀ j : s, X j) :
    singletonFinsetInsert b t (singletonFinsetMap b s t xs) =
      singletonFinsetInsert b s xs := by
  apply singletonFinsetInsert_restrict b t (singletonFinsetInsert b s xs)
  intro i hi
  exact Set.mem_singleton_iff.mpr
    (singletonFinsetInsert_apply_of_notMem b s xs i (fun his ↦ hi (hst his)))

/-- The inclusion diagram of ordinary finite products, with the given points inserted
outside the source finite subset. Both index and factor universes are arbitrary. -/
def singletonFinsetDiagram (b : ∀ i, X i) : Finset ι ⥤ TopCat.{max u v} where
  obj s := TopCat.of (∀ j : s, X j)
  map {s t} _ := TopCat.ofHom (singletonFinsetMap b s t)
  map_id s := by
    apply TopCat.hom_ext
    simpa only [TopCat.hom_ofHom, TopCat.hom_id] using singletonFinsetMap_id b s
  map_comp h k := by
    -- `leOfHom h` is the source-to-intermediate inclusion needed for composition.
    apply TopCat.hom_ext
    simpa only [TopCat.hom_ofHom, TopCat.hom_comp] using
      (singletonFinsetMap_comp b _ (leOfHom h)).symm

/-- The stage object has precisely the ordinary dependent Pi carrier and topology. -/
@[simp]
theorem singletonFinsetDiagram_obj (b : ∀ i, X i) (s : Finset ι) :
    (singletonFinsetDiagram b).obj s = TopCat.of (∀ j : s, X j) :=
  rfl

/-- The diagram map evaluates by restriction of the original finite insertion. -/
@[simp]
theorem singletonFinsetDiagram_map_apply (b : ∀ i, X i) {s t : Finset ι}
    (h : s ⟶ t) (xs : ∀ j : s, X j) :
    TopCat.Hom.hom
      (X := TopCat.of (∀ j : s, X j)) (Y := TopCat.of (∀ j : t, X j))
      ((singletonFinsetDiagram b).map h) xs =
      t.restrict (fun i ↦ singletonFinsetInsert b s xs i) :=
  rfl

/-- The canonical finite-insertion cocone into the singleton cofinite restricted product. -/
def singletonFinsetCocone (b : ∀ i, X i) : Cocone (singletonFinsetDiagram b) where
  pt := TopCat.of (SingletonPathComponents.PointProduct b)
  ι :=
    { app := fun s ↦ TopCat.ofHom
        ⟨singletonFinsetInsert b s, continuous_singletonFinsetInsert b s⟩
      naturality := by
        -- For a preorder morphism `h`, use `singletonFinsetInsert_map b (leOfHom h)`.
        intro s t h
        apply TopCat.ext
        intro xs
        change singletonFinsetInsert b t (singletonFinsetMap b s t xs) =
          singletonFinsetInsert b s xs
        exact singletonFinsetInsert_map b (leOfHom h) xs }

/-- The cocone point is the original singleton cofinite restricted product. -/
@[simp]
theorem singletonFinsetCocone_pt (b : ∀ i, X i) :
    (singletonFinsetCocone b).pt = TopCat.of (SingletonPathComponents.PointProduct b) :=
  rfl

/-- Each cocone leg is the existing finite insertion, evaluated on its ordinary Pi stage. -/
@[simp]
theorem singletonFinsetCocone_ι_app_apply (b : ∀ i, X i) (s : Finset ι)
    (xs : ∀ j : s, X j) :
    TopCat.Hom.hom
      (X := TopCat.of (∀ j : s, X j))
      (Y := TopCat.of (SingletonPathComponents.PointProduct b))
      ((singletonFinsetCocone b).ι.app s) xs = singletonFinsetInsert b s xs :=
  rfl

private def sigmaFinsetInsertMap (b : ∀ i, X i) :
    C((Σ s : Finset ι, ∀ j : s, X j), SingletonPathComponents.PointProduct b) :=
  ContinuousMap.sigma (fun s ↦
    ⟨singletonFinsetInsert b s, continuous_singletonFinsetInsert b s⟩)

variable {Y : Type w} [TopologicalSpace Y]

private theorem factorsThrough_sigmaFinsetInsertMap (b : ∀ i, X i)
    (f : ∀ s : Finset ι, C((∀ j : s, X j), Y))
    (hf : ∀ {s t : Finset ι}, s ⊆ t → (f t).comp (singletonFinsetMap b s t) = f s) :
    Function.FactorsThrough (ContinuousMap.sigma f) (sigmaFinsetInsertMap b) := by
  -- For two equal inserted points, restrict their equality to `s ∪ t`.
  -- The resulting transition points coincide. Apply `f (s ∪ t)` and use `hf`
  -- for both inclusions to identify the two values of `ContinuousMap.sigma f`.
  classical
  rintro ⟨s, xs⟩ ⟨t, xt⟩ h
  change singletonFinsetInsert b s xs = singletonFinsetInsert b t xt at h
  change f s xs = f t xt
  let U : Finset ι := s ∪ t
  have hU : singletonFinsetMap b s U xs = singletonFinsetMap b t U xt := by
    exact congrArg
      (fun z : SingletonPathComponents.PointProduct b ↦ U.restrict (fun i ↦ z i)) h
  calc
    f s xs = f U (singletonFinsetMap b s U xs) :=
      (congrArg (fun g : C((∀ j : s, X j), Y) ↦ g xs)
        (hf (s := s) (t := U) Finset.subset_union_left)).symm
    _ = f U (singletonFinsetMap b t U xt) := congrArg (f U) hU
    _ = f t xt :=
      congrArg (fun g : C((∀ j : t, X j), Y) ↦ g xt)
        (hf (s := t) (t := U) Finset.subset_union_right)

/-- Descend a compatible continuous family from the ordinary finite products.

The observer has its own universe and needs no chosen point. Compatibility with
the empty stage determines the value at the given-point tuple. -/
@[no_expose]
def singletonFinsetDesc (b : ∀ i, X i)
    (f : ∀ s : Finset ι, C((∀ j : s, X j), Y))
    (hf : ∀ {s t : Finset ι}, s ⊆ t → (f t).comp (singletonFinsetMap b s t) = f s) :
    C(SingletonPathComponents.PointProduct b, Y) :=
  Topology.IsQuotientMap.lift (f := sigmaFinsetInsertMap b)
    (SingletonPathComponents.isQuotientMap_sigmaFinsetInsert b)
    (ContinuousMap.sigma f) (factorsThrough_sigmaFinsetInsertMap b f hf)

/-- The descendant computes on every finite stage, not just on a selected support. -/
@[simp]
theorem singletonFinsetDesc_insert (b : ∀ i, X i)
    (f : ∀ s : Finset ι, C((∀ j : s, X j), Y))
    (hf : ∀ {s t : Finset ι}, s ⊆ t → (f t).comp (singletonFinsetMap b s t) = f s)
    (s : Finset ι) (xs : ∀ j : s, X j) :
    singletonFinsetDesc b f hf (singletonFinsetInsert b s xs) = f s xs := by
  exact DFunLike.congr_fun
    (Topology.IsQuotientMap.lift_comp (f := sigmaFinsetInsertMap b)
      (SingletonPathComponents.isQuotientMap_sigmaFinsetInsert b)
      (ContinuousMap.sigma f) (factorsThrough_sigmaFinsetInsertMap b f hf))
    ⟨s, xs⟩

/-- The bundled triangle for each finite-stage insertion commutes. -/
theorem singletonFinsetDesc_comp_insert (b : ∀ i, X i)
    (f : ∀ s : Finset ι, C((∀ j : s, X j), Y))
    (hf : ∀ {s t : Finset ι}, s ⊆ t → (f t).comp (singletonFinsetMap b s t) = f s)
    (s : Finset ι) :
    (singletonFinsetDesc b f hf).comp
      ⟨singletonFinsetInsert b s, continuous_singletonFinsetInsert b s⟩ = f s := by
  apply ContinuousMap.ext
  intro xs
  exact singletonFinsetDesc_insert b f hf s xs

/-- A continuous map is uniquely determined by its values on all finite insertions. -/
theorem singletonFinsetDesc_unique (b : ∀ i, X i)
    (f : ∀ s : Finset ι, C((∀ j : s, X j), Y))
    (hf : ∀ {s t : Finset ι}, s ⊆ t → (f t).comp (singletonFinsetMap b s t) = f s)
    (g : C(SingletonPathComponents.PointProduct b, Y))
    (hg : ∀ (s : Finset ι) (xs : ∀ j : s, X j), g (singletonFinsetInsert b s xs) = f s xs) :
    g = singletonFinsetDesc b f hf := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨⟨s, xs⟩, rfl⟩ :=
    (SingletonPathComponents.isQuotientMap_sigmaFinsetInsert b).surjective x
  exact (hg s xs).trans (singletonFinsetDesc_insert b f hf s xs).symm

private theorem singletonFinsetCocone_compatible (b : ∀ i, X i)
    (c : Cocone (singletonFinsetDiagram b)) :
    ∀ {s t : Finset ι}, s ⊆ t →
      (c.ι.app t).hom.comp (singletonFinsetMap b s t) = (c.ι.app s).hom := by
  -- Use `c.ι.naturality (homOfLE h)`; extract continuous maps with `TopCat.Hom.hom`.
  intro s t h
  have hc := c.ι.naturality (homOfLE h)
  simp only [Functor.const_obj_map] at hc
  exact congrArg TopCat.Hom.hom hc

/-- The original singleton cofinite restricted product is the colimit of its ordinary
finite products. The descendant is continuous quotient descent of the cocone legs. -/
@[no_expose]
def singletonFinsetCoconeIsColimit (b : ∀ i, X i) :
    IsColimit (singletonFinsetCocone b) where
  desc c := TopCat.ofHom (singletonFinsetDesc b (fun s ↦ (c.ι.app s).hom)
    (singletonFinsetCocone_compatible b c))
  fac c s := by
    apply TopCat.ext
    intro xs
    exact @singletonFinsetDesc_insert ι X _ c.pt c.pt.str b (fun t ↦ (c.ι.app t).hom)
      (singletonFinsetCocone_compatible b c) s xs
  uniq c m hm := by
    apply TopCat.hom_ext
    refine @singletonFinsetDesc_unique ι X _ c.pt c.pt.str b (fun s ↦ (c.ι.app s).hom)
      (singletonFinsetCocone_compatible b c) m.hom ?_
    intro s xs
    exact congrArg (fun f : (singletonFinsetDiagram b).obj s ⟶ c.pt ↦ f xs) (hm s)

/-- Categorical descent computes on each ordinary finite product. -/
@[simp]
theorem singletonFinsetCoconeIsColimit_desc_apply (b : ∀ i, X i)
    (c : Cocone (singletonFinsetDiagram b)) (s : Finset ι) (xs : ∀ j : s, X j) :
    TopCat.Hom.hom
      (X := TopCat.of (SingletonPathComponents.PointProduct b)) (Y := c.pt)
      ((singletonFinsetCoconeIsColimit b).desc c) (singletonFinsetInsert b s xs) =
      c.ι.app s xs := by
  exact @singletonFinsetDesc_insert ι X _ c.pt c.pt.str b (fun t ↦ (c.ι.app t).hom)
    (singletonFinsetCocone_compatible b c) s xs

/-- Each finite-insertion leg followed by categorical descent is the corresponding leg. -/
theorem singletonFinsetCoconeIsColimit_desc_fac (b : ∀ i, X i)
    (c : Cocone (singletonFinsetDiagram b)) (s : Finset ι) :
    (singletonFinsetCocone b).ι.app s ≫ (singletonFinsetCoconeIsColimit b).desc c =
      c.ι.app s :=
  (singletonFinsetCoconeIsColimit b).fac c s

/-- The categorical descendant is the unique morphism satisfying the leg equations. -/
theorem singletonFinsetCoconeIsColimit_desc_unique (b : ∀ i, X i)
    (c : Cocone (singletonFinsetDiagram b))
    (m : (singletonFinsetCocone b).pt ⟶ c.pt)
    (hm : ∀ s : Finset ι, (singletonFinsetCocone b).ι.app s ≫ m = c.ι.app s) :
    m = (singletonFinsetCoconeIsColimit b).desc c :=
  (singletonFinsetCoconeIsColimit b).uniq c m hm

end RestrictedProduct
