/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

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

## References

The finite-support-product viewpoint occurs in J. P. May, *A Concise Course in
Algebraic Topology*. This construction reuses Mathlib's generalized loops and homotopy
groups (Roberto Alvarez), fundamental groups (Mark Lavrentyev and contributors),
relative homotopies, path components (Patrick Massot and contributors), quotient maps,
and restricted products (Anatole Dedecker). The based-postcomposition packaging in
`GenLoop` and `HomotopyGroup` is a candidate for upstream inclusion in Mathlib.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped RestrictedProduct

universe u v w z s

namespace GenLoop

variable {N : Type s} {X : Type v} {Y : Type w} {Z : Type z}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- Postcompose a based cube map by a continuous map preserving its chosen point. -/
def map (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1, fun t ht ↦ (congrArg f (GenLoop.boundary p t ht)).trans hf⟩

/-- Evaluation of based postcomposition. -/
@[simp]
theorem map_apply (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x)
    (t : N → unitInterval) : map f hf p t = f (p t) :=
  rfl

/-- The constant loop maps to the constant loop at the target point. -/
@[simp]
theorem map_const (f : C(X, Y)) (hf : f x = y) :
    map f hf (GenLoop.const : GenLoop N X x) = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact hf

/-- Based postcomposition by the identity fixes every loop. -/
@[simp]
theorem map_id (p : GenLoop N X x) :
    map (ContinuousMap.id X) rfl p = p := by
  apply GenLoop.ext
  intro t
  rfl

/-- Based postcomposition respects composition. -/
theorem map_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) :
    map (g.comp f) ((congrArg g hf).trans hg) p =
      map g hg (map f hf p) := by
  apply GenLoop.ext
  intro t
  rfl

/-- Postcomposition commutes with concatenation in any cube direction. -/
theorem map_transAt [DecidableEq N] (f : C(X, Y)) (hf : f x = y)
    (j : N) (p q : GenLoop N X x) :
    map f hf (GenLoop.transAt j p q) =
      GenLoop.transAt j (map f hf p) (map f hf q) := by
  apply GenLoop.ext
  intro t
  change f (if (t j : ℝ) ≤ 1 / 2
      then p (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j)))
      else q (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1)))) =
    if (t j : ℝ) ≤ 1 / 2
      then f (p (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j))))
      else f (q (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1))))
  split_ifs <;> rfl

/-- Based postcomposition preserves homotopies relative to the cube boundary. -/
theorem Homotopic.map (f : C(X, Y)) (hf : f x = y) {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (GenLoop.map f hf p) (GenLoop.map f hf q) := by
  change p.1.HomotopicRel q.1 (Cube.boundary N) at h
  change (f.comp p.1).HomotopicRel (f.comp q.1) (Cube.boundary N)
  exact h.comp_continuousMap f

/-- A homotopy fixed at the source point gives homotopic postcompositions of any
based cube map, without a positivity assumption on its index type. -/
theorem map_homotopic (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g ({x} : Set X)) (p : GenLoop N X x) :
    GenLoop.Homotopic (map f hf p) (map g hg p) := by
  change (f.comp p.1).HomotopicRel (g.comp p.1) (Cube.boundary N)
  refine ⟨{ H.toHomotopy.compContinuousMap p.1 with prop' := ?_ }⟩
  intro t a ha
  change H (t, p a) = f (p a)
  rw [GenLoop.boundary p a ha]
  exact H.eq_fst t (Set.mem_singleton_iff.mpr rfl)

end GenLoop

namespace HomotopyGroup

variable {X : Type v} {Y : Type w} {Z : Type z}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- Based postcomposition on the generalized-loop homotopy quotient for any
cube-index type, including an empty type. No group structure is required. -/
def mapFun (N : Type s) (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  @Quotient.map (GenLoop N X x) (GenLoop N Y y)
    (GenLoop.Homotopic.setoid N x) (GenLoop.Homotopic.setoid N y)
    (GenLoop.map f hf) (by
      intro p q h
      change GenLoop.Homotopic p q at h
      change GenLoop.Homotopic (GenLoop.map f hf p) (GenLoop.map f hf q)
      exact GenLoop.Homotopic.map f hf h)

/-- Compute based postcomposition on a representative class. -/
@[simp]
theorem mapFun_class (N : Type s) (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) :
    mapFun N f hf (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.map f hf p⟧ : HomotopyGroup N Y y) :=
  rfl

/-- The chosen constant class maps to the chosen constant class. -/
theorem mapFun_const (N : Type s) (f : C(X, Y)) (hf : f x = y) :
    mapFun N f hf (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.const⟧ : HomotopyGroup N Y y) := by
  rw [mapFun_class, GenLoop.map_const]

/-- The identity acts as the identity on the homotopy quotient in every dimension. -/
@[simp]
theorem mapFun_id (N : Type s) :
    mapFun N (ContinuousMap.id X) (x := x) rfl = id := by
  funext a
  change mapFun N (ContinuousMap.id X) rfl a = a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ mapFun N (ContinuousMap.id X) rfl a = a)
    a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N X x)
    (mapFun_class N (ContinuousMap.id X) rfl p)
    (congrArg (fun r : GenLoop N X x ↦ (⟦r⟧ : HomotopyGroup N X x))
      (GenLoop.map_id p))

/-- Based postcomposition on the homotopy quotient respects composition. -/
theorem mapFun_comp (N : Type s) (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    mapFun N (g.comp f) ((congrArg g hf).trans hg) =
      (mapFun N g hg) ∘ (mapFun N f hf) := by
  funext a
  change mapFun N (g.comp f) ((congrArg g hf).trans hg) a =
    mapFun N g hg (mapFun N f hf a)
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦
      mapFun N (g.comp f) ((congrArg g hf).trans hg) a =
        mapFun N g hg (mapFun N f hf a)) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Z z)
    (mapFun_class N (g.comp f) ((congrArg g hf).trans hg) p)
    (Eq.trans (α := HomotopyGroup N Z z)
      (congrArg (fun r : GenLoop N Z z ↦ (⟦r⟧ : HomotopyGroup N Z z))
        (GenLoop.map_comp g hg f hf p))
      (Eq.trans (α := HomotopyGroup N Z z)
        (mapFun_class N g hg (GenLoop.map f hf p)).symm
        (congrArg (mapFun N g hg) (mapFun_class N f hf p).symm)))

/-- Maps homotopic relative to the chosen source point act identically on the
homotopy quotient, without a positivity assumption on the cube index. -/
theorem mapFun_eq_of_homotopyRel (N : Type s) (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g ({x} : Set X)) :
    mapFun N f hf = mapFun N g hg := by
  funext a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ mapFun N f hf a = mapFun N g hg a) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Y y)
    (mapFun_class N f hf p)
    (Eq.trans (α := HomotopyGroup N Y y)
      (Quotient.sound (GenLoop.map_homotopic f g hf hg H p))
      (mapFun_class N g hg p).symm)

/-- Based postcomposition on the stock quotient, with its canonical positive group
structure. Multiplication uses the stock reversed concatenation convention. -/
def map (N : Type s) [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y :=
  -- Retain the homotopy-group carriers when using the underlying quotient API.
  let classMap : HomotopyGroup N X x → HomotopyGroup N Y y := mapFun N f hf
  { toFun := classMap
    map_one' := by
      have hclass :
          classMap (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
            (⟦GenLoop.map f hf GenLoop.const⟧ : HomotopyGroup N Y y) := rfl
      exact Eq.trans (α := HomotopyGroup N Y y)
        (congrArg classMap (HomotopyGroup.one_def (N := N) (X := X) (x := x)))
        (Eq.trans (α := HomotopyGroup N Y y) hclass
          (Eq.trans (α := HomotopyGroup N Y y)
            (congrArg (fun p : GenLoop N Y y ↦ (⟦p⟧ : HomotopyGroup N Y y))
              (GenLoop.map_const f hf))
            (HomotopyGroup.one_def (N := N) (X := Y) (x := y)).symm))
    map_mul' a b := by
      refine Quotient.inductionOn₂
        (motive := fun a b : HomotopyGroup N X x ↦
          classMap (a * b) = classMap a * classMap b) a b ?_
      intro p q
      let j : N := Classical.arbitrary N
      have hmul := HomotopyGroup.mul_spec (N := N) (X := X) (x := x)
        (i := j) (p := p) (q := q)
      refine Eq.trans (α := HomotopyGroup N Y y) (congrArg classMap hmul) ?_
      change (⟦GenLoop.map f hf (GenLoop.transAt j q p)⟧ : HomotopyGroup N Y y) =
        ((· * ·) : HomotopyGroup N Y y → HomotopyGroup N Y y → HomotopyGroup N Y y)
          ⟦GenLoop.map f hf p⟧ ⟦GenLoop.map f hf q⟧
      exact Eq.trans (α := HomotopyGroup N Y y)
        (congrArg (fun r : GenLoop N Y y ↦ (⟦r⟧ : HomotopyGroup N Y y))
          (GenLoop.map_transAt f hf j q p))
        (HomotopyGroup.mul_spec (N := N) (X := Y) (x := y)
          (i := j) (p := GenLoop.map f hf p) (q := GenLoop.map f hf q)).symm }

/-- The positive homomorphism has the all-index map as its underlying function,
with the given decidable equality and the canonical homotopy-group structures. -/
theorem coe_map_eq_mapFun (N : Type s) [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) :
    (map N f hf : HomotopyGroup N X x → HomotopyGroup N Y y) = mapFun N f hf :=
  rfl

/-- Compute the induced homomorphism on a representative. -/
@[simp]
theorem map_class (N : Type s) [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) :
    map N f hf (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.map f hf p⟧ : HomotopyGroup N Y y) :=
  rfl

/-- The identity induces the identity homomorphism. -/
@[simp]
theorem map_id (N : Type s) [DecidableEq N] [Nonempty N] :
    map N (ContinuousMap.id X) (x := x) rfl =
      MonoidHom.id (HomotopyGroup N X x) := by
  apply MonoidHom.ext
  intro a
  change map N (ContinuousMap.id X) rfl a = a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ map N (ContinuousMap.id X) rfl a = a)
    a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N X x)
    (map_class N (ContinuousMap.id X) rfl p)
    (congrArg (fun r : GenLoop N X x ↦ (⟦r⟧ : HomotopyGroup N X x))
      (GenLoop.map_id p))

/-- The homomorphism induced by a composite is the composite homomorphism. -/
theorem map_comp (N : Type s) [DecidableEq N] [Nonempty N]
    (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y) :
    map N (g.comp f) ((congrArg g hf).trans hg) =
      (map N g hg).comp (map N f hf) := by
  apply MonoidHom.ext
  intro a
  change map N (g.comp f) ((congrArg g hf).trans hg) a = map N g hg (map N f hf a)
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦
      map N (g.comp f) ((congrArg g hf).trans hg) a = map N g hg (map N f hf a)) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Z z)
    (map_class N (g.comp f) ((congrArg g hf).trans hg) p)
    (Eq.trans (α := HomotopyGroup N Z z)
      (congrArg (fun r : GenLoop N Z z ↦ (⟦r⟧ : HomotopyGroup N Z z))
        (GenLoop.map_comp g hg f hf p))
      (Eq.trans (α := HomotopyGroup N Z z)
        (map_class N g hg (GenLoop.map f hf p)).symm
        (congrArg (map N g hg) (map_class N f hf p).symm)))

/-- Maps homotopic relative to the source point induce the same homomorphism on
positive homotopy groups. -/
theorem map_eq_of_homotopyRel (N : Type s) [DecidableEq N] [Nonempty N]
    (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g ({x} : Set X)) :
    map N f hf = map N g hg := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ map N f hf a = map N g hg a) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Y y)
    (map_class N f hf p)
    (Eq.trans (α := HomotopyGroup N Y y)
      (Quotient.sound (GenLoop.map_homotopic f g hf hg H p))
      (map_class N g hg p).symm)

/-- In dimension one, based postcomposition agrees with Mathlib's fundamental-group
map, under Mathlib's comparison with generalized loops. -/
theorem pi1MulEquivFundamentalGroup_map (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin 1) X x) :
    pi1MulEquivFundamentalGroup (X := Y) (x := y) (map (Fin 1) f hf a) =
      FundamentalGroup.mapOfEq f hf
        (pi1MulEquivFundamentalGroup (X := X) (x := x) a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_class, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
      (genLoopEquivOfUnique (Fin 1) (GenLoop.map f hf p)) =
    ((Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) p)).map f).cast
      hf.symm hf.symm
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

end HomotopyGroup

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

/-- A continuous map descends to the stock set quotient by path connectedness. -/
def pathMap {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B)) :
    ZerothHomotopy A → ZerothHomotopy B :=
  @Quotient.map A B (pathSetoid A) (pathSetoid B) g
    (fun _ _ h ↦ h.map g.continuous)

/-- The path-component arrow sends a point class to the class of its image. -/
@[simp]
theorem pathMap_mk {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B)) (a : A) :
    pathMap g (ZerothHomotopy.mk a) = ZerothHomotopy.mk (g a) :=
  rfl

/-- The identity acts trivially on path components. -/
@[simp]
theorem pathMap_id {A : Type v} [TopologicalSpace A] (q : ZerothHomotopy A) :
    pathMap (ContinuousMap.id A) q = q := by
  refine Quotient.inductionOn q ?_
  intro a
  rfl

/-- Postcomposition on path components respects composition. -/
theorem pathMap_comp {A : Type v} {B : Type w} {D : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    (g : C(B, D)) (f : C(A, B)) (q : ZerothHomotopy A) :
    pathMap (g.comp f) q = pathMap g (pathMap f q) := by
  refine Quotient.inductionOn q ?_
  intro a
  rfl

/-- Homotopic continuous maps induce the same function on path components. -/
theorem pathMap_eq_of_homotopy {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (f g : C(A, B))
    (H : ContinuousMap.Homotopy f g) : pathMap f = pathMap g := by
  funext q
  induction q using ZerothHomotopy.rec with
  | mk a =>
    rw [pathMap_mk, pathMap_mk]
    exact ZerothHomotopy.sound (H.evalAt a)

/-- The coordinate path-component arrows preserve the singleton class defaults. -/
theorem componentMap_membership (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    ∀ᶠ i in cofinite, Set.MapsTo (pathMap (f i))
      ({ZerothHomotopy.mk (b i)} : Set (ZerothHomotopy (X i)))
      ({ZerothHomotopy.mk (c i)} : Set (ZerothHomotopy (Y i))) := by
  apply Filter.Eventually.of_forall
  intro i a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  exact Set.mem_singleton_iff.mpr (by rw [pathMap_mk, hf i])

/-- The stock set-valued restricted-product map of the coordinate path-component arrows. -/
def componentMap (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i) :
    ComponentProduct b → ComponentProduct c :=
  RestrictedProduct.map (fun i ↦ pathMap (f i)) (componentMap_membership b c f hf)

/-- Evaluation of the restricted family of path-component images. -/
@[simp]
theorem componentMap_apply (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (a : ComponentProduct b) (i : ι) :
    componentMap b c f hf a i = pathMap (f i) (a i) :=
  rfl

/-- Identity coordinate maps induce the identity on component families. -/
@[simp]
theorem componentMap_id (b : ∀ i, X i) (a : ComponentProduct b) :
    componentMap b b (fun i ↦ ContinuousMap.id (X i)) (fun _ ↦ rfl) a = a := by
  apply RestrictedProduct.ext
  intro i
  change pathMap (ContinuousMap.id (X i)) (a i) = a i
  exact pathMap_id (a i)

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
  change pathMap ((g i).comp (f i)) (a i) = pathMap (g i) (pathMap (f i) (a i))
  exact pathMap_comp (g i) (f i) (a i)

/-- Naturality of the set-valued path-component comparison, including empty index
sets, with no separation or local path-connectedness assumptions. -/
theorem canonicalEquiv_naturality (b : ∀ i, X i) (c : ∀ i, Y i)
    (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (b i) = c i)
    (q : ZerothHomotopy (PointProduct b)) :
    canonicalEquiv c (pathMap (pointMap b c f hf) q) =
      componentMap b c f hf (canonicalEquiv b q) := by
  induction q using ZerothHomotopy.rec with
  | mk x =>
    apply RestrictedProduct.ext
    intro i
    calc
      canonicalEquiv c (pathMap (pointMap b c f hf) (ZerothHomotopy.mk x)) i =
          canonicalEquiv c (ZerothHomotopy.mk (pointMap b c f hf x)) i :=
        congrArg (fun q : ZerothHomotopy (PointProduct c) ↦ canonicalEquiv c q i)
          (pathMap_mk (pointMap b c f hf) x)
      _ = ZerothHomotopy.mk (pointMap b c f hf x i) :=
        representative_coordinate_apply c (pointMap b c f hf x) i
      _ = ZerothHomotopy.mk (f i (x i)) :=
        congrArg (ZerothHomotopy.mk (X := Y i)) (pointMap_apply b c f hf x i)
      _ = pathMap (f i) (ZerothHomotopy.mk (x i)) :=
        (pathMap_mk (f i) (x i)).symm
      _ = pathMap (f i) (canonicalEquiv b (ZerothHomotopy.mk x) i) :=
        congrArg (pathMap (f i)) (representative_coordinate_apply b x i).symm
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
      RestrictedProduct.SingletonNaturality.pathMap f
        (homotopyGroupEquivZerothHomotopyOfIsEmpty N x a) := by
  refine Quotient.inductionOn a ?_
  intro p
  exact Eq.trans (α := ZerothHomotopy Y)
    (congrArg (homotopyGroupEquivZerothHomotopyOfIsEmpty N y)
      (mapFun_class N f hf p))
    (RestrictedProduct.SingletonNaturality.pathMap_mk f (p 0)).symm

/-- In dimension zero, postcomposition agrees with the existing path-component map
under Mathlib's canonical comparison. -/
theorem pi0EquivZerothHomotopy_mapFun (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin 0) X x) :
    pi0EquivZerothHomotopy (X := Y) (x := y) (mapFun (Fin 0) f hf a) =
      RestrictedProduct.SingletonNaturality.pathMap f
        (pi0EquivZerothHomotopy (X := X) (x := x) a) := by
  exact equivZerothHomotopyOfIsEmpty_mapFun (Fin 0) f hf a

end HomotopyGroup
