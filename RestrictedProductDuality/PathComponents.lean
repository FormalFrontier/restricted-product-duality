/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.PrincipalStage
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Data.Quot
public import Mathlib.Topology.Order

/-!
# Path components of singleton cofinite restricted products

Coordinate evaluation identifies the stock quotient by `Joined` with the set-valued
cofinite restricted product of the factor path components. The inverse chooses
representatives only on the target's finite exceptional set, and inserts the
chosen points everywhere else. No separation or local path-connectedness is needed:
a path joining two points can be constructed in the union of their finite supports.

All products have the ordinary Pi/final restricted-product topology. This is a set
equivalence, not a group equivalence or a homeomorphism of component spaces.

## References

Mathlib's path-component quotient and path operations (Patrick Massot and subsequent
contributors), restricted products (Anatole Dedecker), and quotient API are reused.
Finite insertion and exceptional finite sets are reused from
`RestrictedProductDuality.PrincipalStage` and `RestrictedProductDuality.CompactStage`.
The finite-support-product viewpoint occurs in J. P. May,
*A Concise Course in Algebraic Topology*.
-/

@[expose] public section

noncomputable section

open Filter Set Topology

universe u v

namespace RestrictedProduct.SingletonPathComponents

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- The singleton cofinite restricted product with Mathlib's final topology. -/
abbrev PointProduct (b : ∀ i, X i) :=
  RestrictedProduct X (fun i ↦ ({b i} : Set (X i))) Filter.cofinite

/-- The set-valued restricted product of path-component quotients.
No algebraic operations or topology on this target are part of the comparison. -/
abbrev ComponentProduct (b : ∀ i, X i) :=
  RestrictedProduct (fun i ↦ ZerothHomotopy (X i))
    (fun i ↦ ({ZerothHomotopy.mk (b i)} : Set (ZerothHomotopy (X i))))
    Filter.cofinite

-- The stock restricted-product map supplies the eventual-membership proof.
private def pointClasses (b : ∀ i, X i) (x : PointProduct b) : ComponentProduct b :=
  RestrictedProduct.map (fun i (z : X i) ↦ ZerothHomotopy.mk z)
    (Filter.Eventually.of_forall fun i _ hz ↦
      Set.mem_singleton_iff.mpr
        (congrArg (ZerothHomotopy.mk (X := X i)) (Set.mem_singleton_iff.mp hz))) x

-- Quotient descent uses continuous coordinate evaluation.
private def forward (b : ∀ i, X i) :
    ZerothHomotopy (PointProduct b) → ComponentProduct b :=
  ZerothHomotopy.lift (pointClasses b) (fun _ _ p ↦
    RestrictedProduct.ext (fun i ↦ ZerothHomotopy (X i))
      (fun i ↦ ({ZerothHomotopy.mk (b i)} : Set (ZerothHomotopy (X i))))
      (fun i ↦ ZerothHomotopy.sound
        (Path.map p (RestrictedProduct.continuous_eval
          (R := X) (A := fun i ↦ ({b i} : Set (X i))) i))))

-- Choose representatives only at exceptional coordinates; insert b elsewhere.
private def reconstruction (b : ∀ i, X i) (a : ComponentProduct b) : PointProduct b :=
  RestrictedProduct.singletonFinsetInsert b (RestrictedProduct.exceptionalFinset a)
    (fun i ↦ @Quotient.out (X i) (pathSetoid (X i)) (a i))

private def backward (b : ∀ i, X i) (a : ComponentProduct b) :
    ZerothHomotopy (PointProduct b) :=
  ZerothHomotopy.mk (reconstruction b a)

private theorem reconstruction_coordinate (b : ∀ i, X i) (a : ComponentProduct b) (i : ι) :
    ZerothHomotopy.mk (reconstruction b a i) = a i := by
  classical
  by_cases hi : i ∈ RestrictedProduct.exceptionalFinset a
  · rw [reconstruction, RestrictedProduct.singletonFinsetInsert_apply_of_mem b _ _ i hi]
    exact Quotient.out_eq (a i)
  · rw [reconstruction, RestrictedProduct.singletonFinsetInsert_apply_of_notMem b _ _ i hi]
    exact (Set.mem_singleton_iff.mp
      (RestrictedProduct.mem_cofiniteStage_exceptionalFinset a i hi)).symm

private theorem finite_joined_iff (b : ∀ i, X i) (x y : PointProduct b) :
    Joined x y ↔ ∀ i, Joined (x i) (y i) := by
  classical
  constructor
  · intro h i
    exact h.map (RestrictedProduct.continuous_eval i)
  · intro h
    let s : Finset ι :=
      RestrictedProduct.exceptionalFinset x ∪ RestrictedProduct.exceptionalFinset y
    have hx : x ∈ RestrictedProduct.cofiniteStage
        (R := X) (A := fun i ↦ ({b i} : Set (X i))) s :=
      RestrictedProduct.cofiniteStage_mono
        (show RestrictedProduct.exceptionalFinset x ⊆ s from Finset.subset_union_left)
        (RestrictedProduct.mem_cofiniteStage_exceptionalFinset x)
    have hy : y ∈ RestrictedProduct.cofiniteStage
        (R := X) (A := fun i ↦ ({b i} : Set (X i))) s :=
      RestrictedProduct.cofiniteStage_mono
        (show RestrictedProduct.exceptionalFinset y ⊆ s from Finset.subset_union_right)
        (RestrictedProduct.mem_cofiniteStage_exceptionalFinset y)
    let p : Path (s.restrict (fun i ↦ x i)) (s.restrict (fun i ↦ y i)) :=
      Path.pi (fun i : s ↦ (h i).somePath)
    exact ⟨(p.map (RestrictedProduct.continuous_singletonFinsetInsert b s)).cast
      (RestrictedProduct.singletonFinsetInsert_restrict b s x hx).symm
      (RestrictedProduct.singletonFinsetInsert_restrict b s y hy).symm⟩

/-- Coordinate evaluation identifies path components with finite-support families of
factor path components at the classes of the chosen points. No separation, finiteness,
nonemptiness, countability, or path-connectedness hypotheses are imposed.

The finite-support-product viewpoint follows May, *A Concise Course in Algebraic
Topology*; the quotient and restricted-product constructions are Mathlib's. -/
@[no_expose]
def canonicalEquiv (b : ∀ i, X i) :
    ZerothHomotopy (PointProduct b) ≃ ComponentProduct b where
  toFun := forward b
  invFun := backward b
  left_inv := by
    intro q
    induction q using ZerothHomotopy.rec with
    | mk x =>
      apply Quotient.sound
      apply (finite_joined_iff b _ x).mpr
      intro i
      exact Quotient.exact (reconstruction_coordinate b (pointClasses b x) i)
  right_inv := by
    intro a
    apply RestrictedProduct.ext
    intro i
    exact reconstruction_coordinate b a i

/-- Representative coordinate computation for the canonical comparison. -/
@[simp]
theorem representative_coordinate_apply (b : ∀ i, X i) (x : PointProduct b) (i : ι) :
    canonicalEquiv b (ZerothHomotopy.mk x) i = ZerothHomotopy.mk (x i) := by
  rfl

/-- The coordinate map is quotient descent of continuous evaluation,
with both path-setoid dictionaries explicit. -/
theorem coordinate_apply (b : ∀ i, X i) (q : ZerothHomotopy (PointProduct b)) (i : ι) :
    canonicalEquiv b q i =
      @Quotient.map (PointProduct b) (X i)
        (pathSetoid (PointProduct b)) (pathSetoid (X i))
        (fun x ↦ x i)
        (fun _ _ h ↦ h.map (RestrictedProduct.continuous_eval i)) q := by
  induction q using ZerothHomotopy.rec with
  | mk x => rfl

/-- Inverse reconstruction uses finite insertion and quotient representatives. -/
theorem inverse_reconstruction (b : ∀ i, X i) (a : ComponentProduct b) :
    (canonicalEquiv b).symm a =
      ZerothHomotopy.mk
        (RestrictedProduct.singletonFinsetInsert b (RestrictedProduct.exceptionalFinset a)
          (fun i ↦ @Quotient.out (X i) (pathSetoid (X i)) (a i))) := by
  rfl

/-- The inverse is characterized on every source class by descended coordinate evaluation. -/
theorem inverse_eq_iff (b : ∀ i, X i) (a : ComponentProduct b)
    (q : ZerothHomotopy (PointProduct b)) :
    (canonicalEquiv b).symm a = q ↔
      ∀ i, @Quotient.map (PointProduct b) (X i)
        (pathSetoid (PointProduct b)) (pathSetoid (X i))
        (fun x ↦ x i)
        (fun _ _ h ↦ h.map (RestrictedProduct.continuous_eval i)) q = a i := by
  constructor
  · intro h i
    rw [← coordinate_apply b q i, ← h, Equiv.apply_symm_apply]
  · intro h
    apply (canonicalEquiv b).injective
    rw [Equiv.apply_symm_apply]
    apply RestrictedProduct.ext
    intro i
    rw [coordinate_apply b q i]
    exact (h i).symm

/-- A point represents the inverse class exactly when all its coordinate classes are prescribed. -/
theorem inverse_eq_mk_iff (b : ∀ i, X i) (a : ComponentProduct b) (x : PointProduct b) :
    (canonicalEquiv b).symm a = ZerothHomotopy.mk x ↔
      ∀ i, ZerothHomotopy.mk (x i) = a i := by
  exact inverse_eq_iff b a (ZerothHomotopy.mk x)

/-- Path detection in the restricted product is coordinatewise path detection.
Only the union of the two endpoints' finite supports is needed. -/
theorem joined_iff (b : ∀ i, X i) (x y : PointProduct b) :
    Joined x y ↔ ∀ i, Joined (x i) (y i) := by
  exact finite_joined_iff b x y

/-- The representative coordinate formula uniquely specifies the equivalence. -/
theorem unique (b : ∀ i, X i)
    (e : ZerothHomotopy (PointProduct b) ≃ ComponentProduct b)
    (he : ∀ (x : PointProduct b) i, e (ZerothHomotopy.mk x) i = ZerothHomotopy.mk (x i)) :
    e = canonicalEquiv b := by
  apply Equiv.ext
  intro q
  induction q using ZerothHomotopy.rec with
  | mk x =>
    apply RestrictedProduct.ext
    intro i
    exact (he x i).trans (representative_coordinate_apply b x i).symm

/-- Every finitely exceptional family of path classes has a representative in the
singleton cofinite restricted product. -/
theorem exists_representative (b : ∀ i, X i) (a : ComponentProduct b) :
    ∃ x : PointProduct b, ∀ i, ZerothHomotopy.mk (x i) = a i :=
  ⟨reconstruction b a, reconstruction_coordinate b a⟩

end RestrictedProduct.SingletonPathComponents
