/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.PathConnected
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
public import RestrictedProductDuality.HomotopyGroups
public import RestrictedProductDuality.PathComponents

/-!
# Naturality of singleton restricted-product homotopy comparisons

Based continuous postcomposition acts on generalized loops and their homotopy
quotients for every cube-index type, and on the stock homotopy groups when the index
is nonempty. In dimension zero it agrees with the path-component map. Coordinate
evaluation commutes with this action,
both for the set-valued path-component comparison and for the multiplicative positive
homotopy-group comparison. The latter square requires T1 of both restricted products,
exactly as the two comparison maps do; the induced maps themselves need no separation.

The arrows on restricted products are the stock `mapAlong` and `mapAlongMonoidHom`.
All coordinate maps preserve the chosen points, not merely eventually. The products
carry the ordinary final topology, not a compactly generated or CW weak-product topology.

The component-map API in `ZerothHomotopy` is re-exported from
`FundamentalGroupoids.Topology.Connected.PathConnected`, and the based-postcomposition
API in `GenLoop` and `HomotopyGroup` is re-exported from
`FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map`. This module supplies the
coordinate naturality results and the empty-dimensional comparisons with
`ZerothHomotopy.map`. The `RestrictedProduct.SingletonNaturality.pathMap` names
remain as deprecated compatibility wrappers.

## References

The finite-support-product viewpoint occurs in J. P. May, *A Concise Course in
Algebraic Topology*. This construction reuses Mathlib's generalized loops and homotopy
groups (Roberto Alvarez), fundamental groups (Mark Lavrentyev and contributors),
relative homotopies, path components (Patrick Massot and contributors), quotient maps,
and restricted products (Anatole Dedecker). The component-map and based-postcomposition
definitions and proofs, originally developed in this library by Formal Frontier Agents,
are provided by [Fundamental Groupoids](https://github.com/FormalFrontier/fundamental-groupoids).
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped RestrictedProduct

universe u v w z s

namespace RestrictedProduct.SingletonNaturality

open RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

/-- Coordinatewise basedness preserves the singleton defaults at every index. -/
theorem pointMap_membership (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    ∀ᶠ i in cofinite, Set.MapsTo (f i) ({b i} : Set (X i)) ({c i} : Set (Y i)) :=
  Filter.Eventually.of_forall fun i _ hx ↦ Set.mem_singleton_iff.mpr
    ((congrArg (f i) (Set.mem_singleton_iff.mp hx)).trans (hf i))

/-- The stock continuous restricted-product arrow for coordinatewise based maps. -/
def pointMap (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    C(PointProduct b, PointProduct c) :=
  ⟨RestrictedProduct.mapAlong X Y id Filter.tendsto_id
      (fun i ↦ f i) (pointMap_membership b c f hf),
    RestrictedProduct.mapAlong_continuous X Y id Filter.tendsto_id
      (fun i ↦ f i) (pointMap_membership b c f hf) (fun i ↦ (f i).continuous)⟩

/-- The stock arrow acts coordinatewise at every coordinate. -/
@[simp]
theorem pointMap_apply (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (x : PointProduct b) (i : ι) :
    pointMap b c f hf x i = f i (x i) :=
  rfl

/-- All-coordinate basedness identifies the canonical restricted-product points. -/
@[simp]
theorem pointMap_base (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    pointMap b c f hf (RestrictedProduct.singletonBasepoint b) =
      RestrictedProduct.singletonBasepoint c := by
  apply RestrictedProduct.ext
  intro i
  exact hf i

/-- Identity coordinate maps induce the identity on the restricted product. -/
@[simp]
theorem pointMap_id (b : ∀ i, X i) :
    pointMap b b (fun i ↦ ContinuousMap.id (X i)) (fun _ ↦ rfl) =
      ContinuousMap.id (PointProduct b) := by
  apply ContinuousMap.ext
  intro a
  apply RestrictedProduct.ext
  intro i
  rfl

/-- Constant coordinate maps induce the constant map at the canonical target point. -/
@[simp]
theorem pointMap_const (b : ∀ i, X i) (c : ∀ i, Y i) :
    pointMap b c (fun i ↦ ContinuousMap.const (X i) (c i)) (fun _ ↦ rfl) =
      ContinuousMap.const (PointProduct b) (RestrictedProduct.singletonBasepoint c) := by
  apply ContinuousMap.ext
  intro x
  apply RestrictedProduct.ext
  intro i
  rfl

/-- The stock restricted-product arrow respects composition of based maps. -/
theorem pointMap_comp {Z : ι → Type z} [∀ i, TopologicalSpace (Z i)]
    (b : ∀ i, X i) (c : ∀ i, Y i) (d : ∀ i, Z i)
    (g : ∀ i, C(Y i, Z i)) (hg : ∀ i, g i (c i) = d i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    pointMap b d (fun i ↦ (g i).comp (f i))
        (fun i ↦ (congrArg (g i) (hf i)).trans (hg i)) =
      (pointMap c d g hg).comp (pointMap b c f hf) := by
  apply ContinuousMap.ext
  intro a
  apply RestrictedProduct.ext
  intro i
  rfl

/-- Compatibility name for the induced path-component map `ZerothHomotopy.map`. -/
def pathMap {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B)) :
    ZerothHomotopy A → ZerothHomotopy B :=
  ZerothHomotopy.map g

/-- Compatibility form of `ZerothHomotopy.map_mk`, preserving its original binders. -/
@[simp]
theorem pathMap_mk {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B)) (a : A) :
    pathMap g (ZerothHomotopy.mk a) = ZerothHomotopy.mk (g a) :=
  ZerothHomotopy.map_mk g a

/-- Compatibility form of the pointwise identity law `ZerothHomotopy.map_id`. -/
@[simp]
theorem pathMap_id {A : Type v} [TopologicalSpace A] (q : ZerothHomotopy A) :
    pathMap (ContinuousMap.id A) q = q :=
  ZerothHomotopy.map_id q

/-- Compatibility form of the pointwise composition law `ZerothHomotopy.map_comp`. -/
theorem pathMap_comp {A : Type v} {B : Type w} {D : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    (g : C(B, D)) (f : C(A, B)) (q : ZerothHomotopy A) :
    pathMap (g.comp f) q = pathMap g (pathMap f q) :=
  ZerothHomotopy.map_comp g f q

/-- Compatibility form of homotopy invariance `ZerothHomotopy.map_eq_of_homotopy`. -/
theorem pathMap_eq_of_homotopy {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (f g : C(A, B))
    (H : ContinuousMap.Homotopy f g) : pathMap f = pathMap g :=
  ZerothHomotopy.map_eq_of_homotopy f g H

attribute [deprecated ZerothHomotopy.map (since := "2026-10-31")] pathMap
attribute [deprecated ZerothHomotopy.map_mk (since := "2026-10-31")] pathMap_mk
attribute [deprecated ZerothHomotopy.map_id (since := "2026-10-31")] pathMap_id
attribute [deprecated ZerothHomotopy.map_comp (since := "2026-10-31")] pathMap_comp
attribute [deprecated ZerothHomotopy.map_eq_of_homotopy (since := "2026-10-31")]
  pathMap_eq_of_homotopy

/-- The coordinate path-component arrows preserve the singleton class defaults. -/
theorem componentMap_membership (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    ∀ᶠ i in cofinite, Set.MapsTo (ZerothHomotopy.map (f i))
      ({ZerothHomotopy.mk (b i)} : Set (ZerothHomotopy (X i)))
      ({ZerothHomotopy.mk (c i)} : Set (ZerothHomotopy (Y i))) := by
  apply Filter.Eventually.of_forall
  intro i a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  exact Set.mem_singleton_iff.mpr (by rw [ZerothHomotopy.map_mk, hf i])

/-- The stock set-valued restricted-product map of the coordinate path-component arrows. -/
def componentMap (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    ComponentProduct b → ComponentProduct c :=
  RestrictedProduct.map (fun i ↦ ZerothHomotopy.map (f i)) (componentMap_membership b c f hf)

/-- Evaluation of the restricted family of path-component images. -/
@[simp]
theorem componentMap_apply (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (a : ComponentProduct b) (i : ι) :
    componentMap b c f hf a i = ZerothHomotopy.map (f i) (a i) :=
  rfl

/-- Identity coordinate maps induce the identity on component families. -/
@[simp]
theorem componentMap_id (b : ∀ i, X i) (a : ComponentProduct b) :
    componentMap b b (fun i ↦ ContinuousMap.id (X i)) (fun _ ↦ rfl) a = a := by
  apply RestrictedProduct.ext
  intro i
  change ZerothHomotopy.map (ContinuousMap.id (X i)) (a i) = a i
  exact ZerothHomotopy.map_id (a i)

/-- The component-family arrow respects composition of based maps. -/
theorem componentMap_comp {Z : ι → Type z} [∀ i, TopologicalSpace (Z i)]
    (b : ∀ i, X i) (c : ∀ i, Y i) (d : ∀ i, Z i)
    (g : ∀ i, C(Y i, Z i)) (hg : ∀ i, g i (c i) = d i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) (a : ComponentProduct b) :
    componentMap b d (fun i ↦ (g i).comp (f i))
        (fun i ↦ (congrArg (g i) (hf i)).trans (hg i)) a =
      componentMap c d g hg (componentMap b c f hf a) := by
  apply RestrictedProduct.ext
  intro i
  change ZerothHomotopy.map ((g i).comp (f i)) (a i) =
    ZerothHomotopy.map (g i) (ZerothHomotopy.map (f i) (a i))
  exact ZerothHomotopy.map_comp (g i) (f i) (a i)

/-- Naturality of the set-valued path-component comparison, including empty index
sets, with no separation or local path-connectedness assumptions. -/
theorem canonicalEquiv_naturality (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (q : ZerothHomotopy (PointProduct b)) :
    canonicalEquiv c (ZerothHomotopy.map (pointMap b c f hf) q) =
      componentMap b c f hf (canonicalEquiv b q) := by
  induction q using ZerothHomotopy.rec with
  | mk x =>
    apply RestrictedProduct.ext
    intro i
    calc
      canonicalEquiv c (ZerothHomotopy.map (pointMap b c f hf) (ZerothHomotopy.mk x)) i =
          canonicalEquiv c (ZerothHomotopy.mk (pointMap b c f hf x)) i :=
        congrArg (fun q : ZerothHomotopy (PointProduct c) ↦ canonicalEquiv c q i)
          (ZerothHomotopy.map_mk (pointMap b c f hf) x)
      _ = ZerothHomotopy.mk (pointMap b c f hf x i) :=
        representative_coordinate_apply c (pointMap b c f hf x) i
      _ = ZerothHomotopy.mk (f i (x i)) :=
        congrArg (ZerothHomotopy.mk (X := Y i)) (pointMap_apply b c f hf x i)
      _ = ZerothHomotopy.map (f i) (ZerothHomotopy.mk (x i)) :=
        (ZerothHomotopy.map_mk (f i) (x i)).symm
      _ = ZerothHomotopy.map (f i) (canonicalEquiv b (ZerothHomotopy.mk x) i) :=
        congrArg (ZerothHomotopy.map (f i)) (representative_coordinate_apply b x i).symm
      _ = componentMap b c f hf (canonicalEquiv b (ZerothHomotopy.mk x)) i :=
        (componentMap_apply b c f hf (canonicalEquiv b (ZerothHomotopy.mk x)) i).symm

/-- Coordinate generalized loops commute with based postcomposition. No positivity
or separation assumption is needed. -/
theorem singletonCoordinateGenLoop_map (N : Type s)
    (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (p : GenLoop N (PointProduct b) (RestrictedProduct.singletonBasepoint b)) (i : ι) :
    RestrictedProduct.singletonCoordinateGenLoop N c
        (GenLoop.map (pointMap b c f hf) (pointMap_base b c f hf) p) i =
      GenLoop.map (f i) (hf i)
        (RestrictedProduct.singletonCoordinateGenLoop N b p i) := by
  apply GenLoop.ext
  intro t
  rfl

/-- The stock algebraic restricted-product homomorphism of the coordinate induced
maps. The default subgroups are the canonical bottom subgroups. -/
def homotopyTupleMap (N : Type s) [DecidableEq N] [Nonempty N]
    (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    (Πʳ i, [HomotopyGroup N (X i) (b i),
      (⊥ : Subgroup (HomotopyGroup N (X i) (b i)))]) →*
    (Πʳ i, [HomotopyGroup N (Y i) (c i),
      (⊥ : Subgroup (HomotopyGroup N (Y i) (c i)))]) :=
  RestrictedProduct.mapAlongMonoidHom
    (B₁ := fun i ↦ (⊥ : Subgroup (HomotopyGroup N (X i) (b i))))
    (B₂ := fun i ↦ (⊥ : Subgroup (HomotopyGroup N (Y i) (c i))))
    (fun i ↦ HomotopyGroup N (X i) (b i))
    (fun i ↦ HomotopyGroup N (Y i) (c i)) id Filter.tendsto_id
    (fun i ↦ HomotopyGroup.map N (f i) (hf i))
    (Filter.Eventually.of_forall fun i a ha ↦ Subgroup.mem_bot.mpr (by
      rw [Subgroup.mem_bot.mp ha, map_one]))

/-- Evaluate a coordinate of the homotopy-class tuple map. -/
@[simp]
theorem homotopyTupleMap_apply (N : Type s) [DecidableEq N] [Nonempty N]
    (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (a : Πʳ i, [HomotopyGroup N (X i) (b i),
      (⊥ : Subgroup (HomotopyGroup N (X i) (b i)))]) (i : ι) :
    homotopyTupleMap N b c f hf a i = HomotopyGroup.map N (f i) (hf i) (a i) :=
  rfl

/-- Identity coordinate maps induce the identity on positive homotopy families. -/
@[simp]
theorem homotopyTupleMap_id (N : Type s) [DecidableEq N] [Nonempty N]
    (b : ∀ i, X i) :
    homotopyTupleMap N b b (fun i ↦ ContinuousMap.id (X i)) (fun _ ↦ rfl) =
      MonoidHom.id (Πʳ i, [HomotopyGroup N (X i) (b i),
        (⊥ : Subgroup (HomotopyGroup N (X i) (b i)))]) := by
  apply MonoidHom.ext
  intro a
  apply RestrictedProduct.ext
  intro i
  change HomotopyGroup.map N (ContinuousMap.id (X i)) rfl (a i) = a i
  exact congrArg
    (fun h : HomotopyGroup N (X i) (b i) →* HomotopyGroup N (X i) (b i) ↦ h (a i))
    (HomotopyGroup.map_id N (X := X i) (x := b i))

/-- The positive homotopy-family arrow respects composition of based maps. -/
theorem homotopyTupleMap_comp (N : Type s) [DecidableEq N] [Nonempty N]
    {Z : ι → Type z} [∀ i, TopologicalSpace (Z i)]
    (b : ∀ i, X i) (c : ∀ i, Y i) (d : ∀ i, Z i)
    (g : ∀ i, C(Y i, Z i)) (hg : ∀ i, g i (c i) = d i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    homotopyTupleMap N b d (fun i ↦ (g i).comp (f i))
        (fun i ↦ (congrArg (g i) (hf i)).trans (hg i)) =
      (homotopyTupleMap N c d g hg).comp (homotopyTupleMap N b c f hf) := by
  apply MonoidHom.ext
  intro a
  apply RestrictedProduct.ext
  intro i
  change HomotopyGroup.map N ((g i).comp (f i)) ((congrArg (g i) (hf i)).trans (hg i))
      (a i) =
    HomotopyGroup.map N (g i) (hg i) (HomotopyGroup.map N (f i) (hf i) (a i))
  exact congrArg
    (fun h : HomotopyGroup N (X i) (b i) →* HomotopyGroup N (Z i) (d i) ↦ h (a i))
    (HomotopyGroup.map_comp N (g i) (hg i) (f i) (hf i))

/-- Naturality of the canonical positive homotopy-group comparisons. Both
restricted products require T1, precisely as the named comparisons do. -/
theorem homotopyGroupSingletonMulEquiv_naturality
    (N : Type s) [DecidableEq N] [Nonempty N]
    (b : ∀ i, X i) (c : ∀ i, Y i)
    [T1Space (PointProduct b)] [T1Space (PointProduct c)]
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (a : HomotopyGroup N (PointProduct b) (RestrictedProduct.singletonBasepoint b)) :
    RestrictedProduct.homotopyGroupSingletonMulEquiv N c
        (HomotopyGroup.map N (pointMap b c f hf) (pointMap_base b c f hf) a) =
      homotopyTupleMap N b c f hf
        (RestrictedProduct.homotopyGroupSingletonMulEquiv N b a) := by
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N (PointProduct b) (RestrictedProduct.singletonBasepoint b) ↦
      RestrictedProduct.homotopyGroupSingletonMulEquiv N c
          (HomotopyGroup.map N (pointMap b c f hf) (pointMap_base b c f hf) a) =
        homotopyTupleMap N b c f hf
          (RestrictedProduct.homotopyGroupSingletonMulEquiv N b a)) a ?_
  intro p
  apply RestrictedProduct.ext
  intro i
  exact Eq.trans (α := HomotopyGroup N (Y i) (c i))
    (congrArg (fun a : HomotopyGroup N (PointProduct c) (RestrictedProduct.singletonBasepoint c) ↦
      RestrictedProduct.homotopyGroupSingletonMulEquiv N c a i)
      (HomotopyGroup.map_class N (pointMap b c f hf) (pointMap_base b c f hf) p))
    (Eq.trans (α := HomotopyGroup N (Y i) (c i))
      (RestrictedProduct.homotopyGroupSingletonMulEquiv_apply N c
        (GenLoop.map (pointMap b c f hf) (pointMap_base b c f hf) p) i)
      (Eq.trans (α := HomotopyGroup N (Y i) (c i))
        (congrArg (fun r : GenLoop N (Y i) (c i) ↦ (⟦r⟧ : HomotopyGroup N (Y i) (c i)))
          (singletonCoordinateGenLoop_map N b c f hf p i))
        (Eq.trans (α := HomotopyGroup N (Y i) (c i))
          (HomotopyGroup.map_class N (f i) (hf i)
            (RestrictedProduct.singletonCoordinateGenLoop N b p i)).symm
          (Eq.trans (α := HomotopyGroup N (Y i) (c i))
            (congrArg (HomotopyGroup.map N (f i) (hf i))
              (RestrictedProduct.homotopyGroupSingletonMulEquiv_apply N b p i).symm)
            (homotopyTupleMap_apply N b c f hf
              (RestrictedProduct.homotopyGroupSingletonMulEquiv N b
                (⟦p⟧ : HomotopyGroup N (PointProduct b)
                  (RestrictedProduct.singletonBasepoint b))) i).symm))))

end RestrictedProduct.SingletonNaturality

namespace HomotopyGroup

variable {X : Type v} {Y : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

/-- For an empty cube-index type, postcomposition agrees with the existing
path-component map under Mathlib's empty-dimensional comparison. -/
theorem equivZerothHomotopyOfIsEmpty_mapFun (N : Type s) [IsEmpty N]
    (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup N X x) :
    homotopyGroupEquivZerothHomotopyOfIsEmpty N y (mapFun N f hf a) =
      ZerothHomotopy.map f (homotopyGroupEquivZerothHomotopyOfIsEmpty N x a) := by
  refine Quotient.inductionOn a ?_
  intro p
  exact Eq.trans (α := ZerothHomotopy Y)
    (congrArg (homotopyGroupEquivZerothHomotopyOfIsEmpty N y)
      (mapFun_class N f hf p))
    (ZerothHomotopy.map_mk f (p 0)).symm

/-- In dimension zero, postcomposition agrees with the existing path-component map
under Mathlib's canonical comparison. -/
theorem pi0EquivZerothHomotopy_mapFun (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin 0) X x) :
    pi0EquivZerothHomotopy (X := Y) (x := y) (mapFun (Fin 0) f hf a) =
      ZerothHomotopy.map f (pi0EquivZerothHomotopy (X := X) (x := x) a) := by
  exact equivZerothHomotopyOfIsEmpty_mapFun (Fin 0) f hf a

end HomotopyGroup
