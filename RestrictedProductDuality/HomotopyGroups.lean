/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.FiniteStage
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Homotopy groups of singleton cofinite restricted products

Coordinate evaluation identifies the homotopy group of a T1 singleton cofinite
restricted product with the algebraic restricted product of the coordinate
homotopy groups at their bottom subgroups. The cube index is an arbitrary
nonempty type, independent of the index and fiber universes.

Compactness of the cube gives a finite stage for each representative. Relative
homotopies are assembled in the union of two such stages; finite insertion also
reconstructs representatives from finitely supported coordinate classes. These
are ordinary Pi stages and the restricted-product final topology, not a comparison
with compactly generated products or CW weak products.

## References

The ordinary finite-support-product viewpoint is that of J. P. May,
*A Concise Course in Algebraic Topology*. The construction reuses Mathlib's
homotopy groups by Roberto Alvarez, relative homotopies and their products,
and restricted products by Anatole Dedecker.
-/

@[expose] public section

noncomputable section

open Filter
open scoped RestrictedProduct

universe u v w

namespace RestrictedProduct

variable {ι : Type u} {R : ι → Type v}

/-- The chosen coordinate family as a point of the singleton cofinite restricted product. -/
def singletonBasepoint (b : ∀ i, R i) :
    RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite :=
  ⟨b, Filter.Eventually.of_forall (fun i ↦ by rfl)⟩

/-- Evaluation of the chosen point is the originally chosen coordinate point. -/
@[simp]
theorem singletonBasepoint_apply (b : ∀ i, R i) (i : ι) :
    singletonBasepoint b i = b i :=
  rfl

variable [∀ i, TopologicalSpace (R i)]

/-- The coordinate of a generalized loop in the singleton cofinite restricted product.

Continuity is the stock global restricted-product evaluation continuity, followed
by the original continuous cube map. The boundary equation is the original
GenLoop boundary equation evaluated in that same coordinate. -/
def singletonCoordinateGenLoop (N : Type w) (b : ∀ i, R i)
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) :
    GenLoop N (R i) (b i) :=
  ⟨(⟨(fun z : RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite ↦ z i),
      RestrictedProduct.continuous_eval i⟩ :
      C(RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite, R i)).comp p.1,
    by
      intro y hy
      exact congrArg
        (fun z : RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite ↦ z i)
        (GenLoop.boundary p y hy)⟩

/-- The coordinate loop is the actual original coordinate function on the cube. -/
@[simp]
theorem singletonCoordinateGenLoop_apply (N : Type w) (b : ∀ i, R i)
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) (y : N → unitInterval) :
    singletonCoordinateGenLoop N b p i y = p y i :=
  rfl

/-- Existence of a multiplicative comparison with the coordinate-class formula. -/
def singletonHomotopyGroupComparisonSpec (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i) : Prop :=
  ∃ e : HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) ≃*
      (Πʳ i, [HomotopyGroup N (R i) (b i),
        (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]),
    ∀ (p : GenLoop N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b)) (i : ι),
      e (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite)
          (singletonBasepoint b)) i =
        (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i))

private theorem singletonCoordinateGenLoop_homotopic (N : Type w) (b : ∀ i, R i)
    {p q : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)} (h : GenLoop.Homotopic p q) (i : ι) :
    GenLoop.Homotopic (singletonCoordinateGenLoop N b p i)
      (singletonCoordinateGenLoop N b q i) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h
    (⟨(fun z : RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite ↦ z i),
      RestrictedProduct.continuous_eval i⟩ :
      C(RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite, R i))

/-- Assemble a finite family of based cube maps and insert the chosen points elsewhere. -/
def singletonFinsetGenLoop (N : Type w) (b : ∀ i, R i) (s : Finset ι)
    (a : ∀ i : s, GenLoop N (R i) (b i)) :
    GenLoop N (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b) := by
  letI : DecidableEq ι := Classical.decEq ι
  refine ⟨(⟨singletonFinsetInsert b s, continuous_singletonFinsetInsert b s⟩ :
    C((∀ i : s, R i),
      RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)).comp
    (ContinuousMap.pi fun i : s ↦ (a i).1), ?_⟩
  intro y hy
  apply RestrictedProduct.ext
  intro i
  change singletonFinsetInsert b s (fun j : s ↦ a j y) i = b i
  by_cases hi : i ∈ s
  · rw [singletonFinsetInsert_apply_of_mem b s _ i hi]
    exact GenLoop.boundary (a ⟨i, hi⟩) y hy
  · exact singletonFinsetInsert_apply_of_notMem b s _ i hi

/-- On the finite stage, the assembled loop has the prescribed coordinate value. -/
theorem singletonFinsetGenLoop_apply_of_mem (N : Type w) (b : ∀ i, R i)
    (s : Finset ι) (a : ∀ i : s, GenLoop N (R i) (b i))
    (y : N → unitInterval) (i : ι) (hi : i ∈ s) :
    singletonFinsetGenLoop N b s a y i = a ⟨i, hi⟩ y := by
  change singletonFinsetInsert b s (fun j : s ↦ a j y) i = a ⟨i, hi⟩ y
  exact singletonFinsetInsert_apply_of_mem b s _ i hi

/-- Outside the finite stage, the assembled loop is at the chosen point. -/
theorem singletonFinsetGenLoop_apply_of_notMem (N : Type w) (b : ∀ i, R i)
    (s : Finset ι) (a : ∀ i : s, GenLoop N (R i) (b i))
    (y : N → unitInterval) (i : ι) (hi : i ∉ s) :
    singletonFinsetGenLoop N b s a y i = b i := by
  change singletonFinsetInsert b s (fun j : s ↦ a j y) i = b i
  exact singletonFinsetInsert_apply_of_notMem b s _ i hi

/-- The coordinate loop on the finite stage is the prescribed based cube map. -/
theorem singletonCoordinateGenLoop_singletonFinsetGenLoop_of_mem
    (N : Type w) (b : ∀ i, R i) (s : Finset ι)
    (a : ∀ i : s, GenLoop N (R i) (b i)) (i : ι) (hi : i ∈ s) :
    singletonCoordinateGenLoop N b (singletonFinsetGenLoop N b s a) i = a ⟨i, hi⟩ := by
  apply GenLoop.ext
  intro y
  exact singletonFinsetGenLoop_apply_of_mem N b s a y i hi

/-- The coordinate loop outside the finite stage is the constant based cube map. -/
theorem singletonCoordinateGenLoop_singletonFinsetGenLoop_of_notMem
    (N : Type w) (b : ∀ i, R i) (s : Finset ι)
    (a : ∀ i : s, GenLoop N (R i) (b i)) (i : ι) (hi : i ∉ s) :
    singletonCoordinateGenLoop N b (singletonFinsetGenLoop N b s a) i =
      (GenLoop.const : GenLoop N (R i) (b i)) := by
  apply GenLoop.ext
  intro y
  exact singletonFinsetGenLoop_apply_of_notMem N b s a y i hi

/-- A based cube map into a T1 singleton restricted product is fixed outside one finite set. -/
private theorem exists_genLoop_eq_basepoint_outside_finset (N : Type w) (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) :
    ∃ s : Finset ι, ∀ y : N → unitInterval, ∀ i : ι, i ∉ s → p y i = b i := by
  obtain ⟨s, g, _, hg⟩ :=
    exists_singletonFinsetInsert_factorization b p.1.continuous
  refine ⟨s, ?_⟩
  intro y i hi
  calc
    p y i = singletonFinsetInsert b s (g y) i :=
      congrArg (fun z : RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite ↦
        z i) (hg y).symm
    _ = b i := singletonFinsetInsert_apply_of_notMem b s (g y) i hi

/-- Coordinate relative homotopies assemble through the union of two finite stages. -/
private theorem homotopic_of_singletonCoordinateGenLoop (N : Type w) (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p q : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b))
    (h : ∀ i, GenLoop.Homotopic (singletonCoordinateGenLoop N b p i)
      (singletonCoordinateGenLoop N b q i)) :
    GenLoop.Homotopic p q := by
  let : DecidableEq ι := Classical.decEq ι
  obtain ⟨s, hs⟩ := exists_genLoop_eq_basepoint_outside_finset N b p
  obtain ⟨t, ht⟩ := exists_genLoop_eq_basepoint_outside_finset N b q
  let S : Finset ι := s ∪ t
  let P : C((N → unitInterval), ∀ i : S, R i) :=
    ContinuousMap.pi fun i : S ↦ (singletonCoordinateGenLoop N b p i.1).1
  let Q : C((N → unitInterval), ∀ i : S, R i) :=
    ContinuousMap.pi fun i : S ↦ (singletonCoordinateGenLoop N b q i.1).1
  let H : ∀ i : S,
      ContinuousMap.HomotopyRel (singletonCoordinateGenLoop N b p i.1).1
        (singletonCoordinateGenLoop N b q i.1).1 (Cube.boundary N) :=
    fun i ↦ Classical.choice (h i.1)
  let K : ContinuousMap.HomotopyRel P Q (Cube.boundary N) :=
    ContinuousMap.HomotopyRel.pi H
  let ins : C((∀ i : S, R i),
      RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite) :=
    ⟨singletonFinsetInsert b S, continuous_singletonFinsetInsert b S⟩
  have hp : ins.comp P = p.1 := by
    apply ContinuousMap.ext
    intro y
    apply RestrictedProduct.ext
    intro i
    by_cases hi : i ∈ S
    · exact singletonFinsetInsert_apply_of_mem b S (P y) i hi
    · have his : i ∉ s := fun his ↦ hi (Finset.mem_union.mpr (Or.inl his))
      calc
        ins (P y) i = b i := singletonFinsetInsert_apply_of_notMem b S (P y) i hi
        _ = p y i := (hs y i his).symm
  have hq : ins.comp Q = q.1 := by
    apply ContinuousMap.ext
    intro y
    apply RestrictedProduct.ext
    intro i
    by_cases hi : i ∈ S
    · exact singletonFinsetInsert_apply_of_mem b S (Q y) i hi
    · have hit : i ∉ t := fun hit ↦ hi (Finset.mem_union.mpr (Or.inr hit))
      calc
        ins (Q y) i = b i := singletonFinsetInsert_apply_of_notMem b S (Q y) i hi
        _ = q y i := (ht y i hit).symm
  exact ⟨(K.compContinuousMap ins).cast hp hq⟩

/-- Homotopy of singleton restricted-product cube maps is detected coordinatewise. -/
theorem singletonCoordinateGenLoop_homotopic_iff (N : Type w) (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p q : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) :
    (∀ i, GenLoop.Homotopic (singletonCoordinateGenLoop N b p i)
      (singletonCoordinateGenLoop N b q i)) ↔ GenLoop.Homotopic p q := by
  constructor
  · exact homotopic_of_singletonCoordinateGenLoop N b p q
  · intro h i
    exact singletonCoordinateGenLoop_homotopic N b h i

/-- Every bottom-subgroup restricted family of homotopy classes has a based cube representative. -/
private theorem exists_genLoop_of_singletonClasses (N : Type w) [DecidableEq N] [Nonempty N]
    (b : ∀ i, R i)
    (c : Πʳ i, [HomotopyGroup N (R i) (b i),
      (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]) :
    ∃ p : GenLoop N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b),
      ∀ i, (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) =
        c i := by
  -- Only the factor index gets a classical DecidableEq. The N dictionary is unchanged.
  let : DecidableEq ι := Classical.decEq ι
  let s : Finset ι := exceptionalFinset c
  let r : ∀ i : s, Setoid (GenLoop N (R i) (b i)) :=
    fun i ↦ GenLoop.Homotopic.setoid N (b i)
  let e := Setoid.piQuotientEquiv r
  let d : ∀ i : s, Quotient (r i) := fun i ↦ c i
  let a : ∀ i : s, GenLoop N (R i) (b i) := (e d).out
  have ha : ∀ i : s, (⟦a i⟧ : HomotopyGroup N (R i) (b i)) = c i := by
    have hrep : (⟦a⟧ : Quotient (@piSetoid _ _ r)) = e d := Quotient.out_eq (e d)
    have he : e.symm (⟦a⟧ : Quotient (@piSetoid _ _ r)) = d := by
      rw [hrep]
      exact e.symm_apply_apply d
    intro i
    have hi := congrFun he i
    change (⟦a i⟧ : Quotient (r i)) = d i at hi
    exact hi
  refine ⟨singletonFinsetGenLoop N b s a, ?_⟩
  intro i
  by_cases hi : i ∈ s
  · rw [singletonCoordinateGenLoop_singletonFinsetGenLoop_of_mem N b s a i hi]
    exact ha ⟨i, hi⟩
  · rw [singletonCoordinateGenLoop_singletonFinsetGenLoop_of_notMem N b s a i hi]
    have hc : c i = (1 : HomotopyGroup N (R i) (b i)) := Subgroup.mem_bot.mp
      (mem_cofiniteStage_exceptionalFinset c i hi)
    have hconst : (⟦GenLoop.const⟧ : HomotopyGroup N (R i) (b i)) =
        (1 : HomotopyGroup N (R i) (b i)) :=
      (HomotopyGroup.one_def (N := N) (X := R i) (x := b i)).symm
    exact Eq.trans (α := HomotopyGroup N (R i) (b i)) hconst hc.symm


private theorem singletonCoordinateGenLoop_transAt (N : Type w) [DecidableEq N]
    (b : ∀ i, R i) (j : N)
    (p q : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) :
    singletonCoordinateGenLoop N b (GenLoop.transAt j p q) i =
      GenLoop.transAt j (singletonCoordinateGenLoop N b p i)
        (singletonCoordinateGenLoop N b q i) := by
  apply GenLoop.ext
  intro y
  change (if (y j : ℝ) ≤ 1 / 2
      then p (Function.update y j (Set.projIcc 0 1 zero_le_one (2 * y j)))
      else q (Function.update y j (Set.projIcc 0 1 zero_le_one (2 * y j - 1)))) i =
    if (y j : ℝ) ≤ 1 / 2
      then p (Function.update y j (Set.projIcc 0 1 zero_le_one (2 * y j))) i
      else q (Function.update y j (Set.projIcc 0 1 zero_le_one (2 * y j - 1))) i
  split_ifs <;> rfl

/-- The coordinate homotopy classes of a based cube map, as an algebraic restricted
family at the bottom subgroups. Compact finite-stage factorization makes the family
finitely supported. -/
def singletonGenLoopClasses (N : Type w) [DecidableEq N] [Nonempty N]
    (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) :
    Πʳ i, [HomotopyGroup N (R i) (b i),
      (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))] :=
  ⟨fun i ↦ ⟦singletonCoordinateGenLoop N b p i⟧, by
    obtain ⟨s, hs⟩ := exists_genLoop_eq_basepoint_outside_finset N b p
    filter_upwards [s.eventually_cofinite_notMem] with i hi
    apply Subgroup.mem_bot.mpr
    have hconst : singletonCoordinateGenLoop N b p i = GenLoop.const := by
      apply GenLoop.ext
      intro y
      exact hs y i hi
    rw [HomotopyGroup.one_def, hconst]⟩

/-- Evaluating the class family of a based cube map gives its coordinate class. -/
@[simp]
theorem singletonGenLoopClasses_apply (N : Type w) [DecidableEq N] [Nonempty N]
    (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) :
    singletonGenLoopClasses N b p i =
      (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) :=
  rfl

private theorem singletonGenLoopClasses_homotopic (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    {p q : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)} (h : GenLoop.Homotopic p q) :
    singletonGenLoopClasses N b p = singletonGenLoopClasses N b q := by
  apply RestrictedProduct.ext
  intro i
  exact Quotient.sound (singletonCoordinateGenLoop_homotopic N b h i)

/-- Coordinate evaluation on homotopy classes as a homomorphism to the algebraic
restricted product at the bottom subgroups. Compact finite-stage factorization
ensures that all but finitely many coordinate classes are the identity. -/
def homotopyGroupSingletonHom (N : Type w) [DecidableEq N] [Nonempty N]
    (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)] :
    HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) →*
      (Πʳ i, [HomotopyGroup N (R i) (b i),
        (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]) where
  toFun := Quotient.lift (singletonGenLoopClasses N b) (by
    intro p q h
    exact singletonGenLoopClasses_homotopic N b h)
  map_one' := by
    apply RestrictedProduct.ext
    intro i
    change (⟦singletonCoordinateGenLoop N b GenLoop.const i⟧ :
      HomotopyGroup N (R i) (b i)) = (1 : HomotopyGroup N (R i) (b i))
    rw [HomotopyGroup.one_def]
    rfl
  map_mul' a c := by
    let classMap : HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) →
        (Πʳ i, [HomotopyGroup N (R i) (b i),
          (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]) :=
      Quotient.lift (singletonGenLoopClasses N b) (by
        intro p q h
        exact singletonGenLoopClasses_homotopic N b h)
    change classMap (a * c) = classMap a * classMap c
    refine Quotient.inductionOn₂
      (motive := fun a c : HomotopyGroup N
          (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
          (singletonBasepoint b) ↦
        classMap (a * c) = classMap a * classMap c) a c ?_
    intro p q
    let j : N := Classical.arbitrary N
    have hmul := HomotopyGroup.mul_spec (N := N)
      (X := RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (x := singletonBasepoint b) (i := j) (p := p) (q := q)
    refine Eq.trans (α := Πʳ i, [HomotopyGroup N (R i) (b i),
      (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]) (congrArg classMap hmul) ?_
    apply RestrictedProduct.ext
    intro i
    change (⟦singletonCoordinateGenLoop N b (GenLoop.transAt j q p) i⟧ :
      HomotopyGroup N (R i) (b i)) =
        ((· * ·) : HomotopyGroup N (R i) (b i) → HomotopyGroup N (R i) (b i) →
          HomotopyGroup N (R i) (b i))
          ⟦singletonCoordinateGenLoop N b p i⟧ ⟦singletonCoordinateGenLoop N b q i⟧
    have hcoord := HomotopyGroup.mul_spec (N := N) (X := R i) (x := b i) (i := j)
      (p := singletonCoordinateGenLoop N b p i) (q := singletonCoordinateGenLoop N b q i)
    exact Eq.trans (α := HomotopyGroup N (R i) (b i))
      (congrArg (fun r : GenLoop N (R i) (b i) ↦
        (⟦r⟧ : HomotopyGroup N (R i) (b i)))
        (singletonCoordinateGenLoop_transAt N b j q p i)) hcoord.symm

/-- The coordinate homomorphism evaluates a representative by its coordinate loop. -/
@[simp]
theorem homotopyGroupSingletonHom_apply (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) :
    homotopyGroupSingletonHom N b
        (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite)
          (singletonBasepoint b)) i =
      (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) :=
  singletonGenLoopClasses_apply N b p i

private theorem homotopyGroupSingletonHom_bijective (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)] :
    Function.Bijective (homotopyGroupSingletonHom N b) := by
  constructor
  · intro a c
    refine Quotient.inductionOn₂ a c ?_
    intro p q h
    apply Quotient.sound
    apply homotopic_of_singletonCoordinateGenLoop N b p q
    intro i
    have hcoord :
        (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) =
          (⟦singletonCoordinateGenLoop N b q i⟧ : HomotopyGroup N (R i) (b i)) :=
      Eq.trans (α := HomotopyGroup N (R i) (b i))
        (homotopyGroupSingletonHom_apply N b p i).symm
        (Eq.trans (α := HomotopyGroup N (R i) (b i))
          (congrArg (fun z : Πʳ j, [HomotopyGroup N (R j) (b j),
            (⊥ : Subgroup (HomotopyGroup N (R j) (b j)))] ↦ z i) h)
          (homotopyGroupSingletonHom_apply N b q i))
    exact Quotient.exact (s := GenLoop.Homotopic.setoid N (b i))
      (a := singletonCoordinateGenLoop N b p i) (b := singletonCoordinateGenLoop N b q i) (by
        exact hcoord)
  · intro c
    obtain ⟨p, hp⟩ := exists_genLoop_of_singletonClasses N b c
    refine ⟨⟦p⟧, ?_⟩
    apply RestrictedProduct.ext
    intro i
    rw [homotopyGroupSingletonHom_apply]
    exact hp i

/-- The canonical multiplicative comparison given by coordinate evaluation.

Only T1 of the singleton restricted product is required. The cube index can be
any nonempty type with decidable equality, using Mathlib's homotopy-group
multiplication. See J. P. May, *A Concise Course in Algebraic Topology*, for the
finite-support-product viewpoint; the topology here is the ordinary final one. -/
def homotopyGroupSingletonMulEquiv (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)] :
    HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) ≃*
      (Πʳ i, [HomotopyGroup N (R i) (b i),
        (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]) :=
  MulEquiv.ofBijective (homotopyGroupSingletonHom N b)
    (by exact homotopyGroupSingletonHom_bijective N b)

/-- The comparison sends every representative to its coordinate classes. -/
@[simp]
theorem homotopyGroupSingletonMulEquiv_apply (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) (i : ι) :
    homotopyGroupSingletonMulEquiv N b
        (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite)
          (singletonBasepoint b)) i =
      (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) :=
  homotopyGroupSingletonHom_apply N b p i

/-- Coordinate classes characterize inverse reconstruction from a class family. -/
theorem homotopyGroupSingletonMulEquiv_symm_eq_iff (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (c : Πʳ i, [HomotopyGroup N (R i) (b i),
      (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))])
    (p : GenLoop N
      (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
      (singletonBasepoint b)) :
    (homotopyGroupSingletonMulEquiv N b).symm c =
        (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
          (singletonBasepoint b)) ↔
      ∀ i, c i =
        (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i)) := by
  let e := homotopyGroupSingletonMulEquiv N b
  constructor
  · intro h i
    have hc : c = e ⟦p⟧ := (e.apply_symm_apply c).symm.trans (congrArg e h)
    exact (congrArg (fun z ↦ z i) hc).trans
      (homotopyGroupSingletonMulEquiv_apply N b p i)
  · intro h
    apply e.injective
    calc
      e (e.symm c) = c := e.apply_symm_apply c
      _ = e ⟦p⟧ := by
        apply RestrictedProduct.ext
        intro i
        exact (h i).trans (homotopyGroupSingletonMulEquiv_apply N b p i).symm

/-- The representative coordinate formula uniquely determines the comparison. -/
theorem homotopyGroupSingletonMulEquiv_unique (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)]
    (e : HomotopyGroup N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b) ≃*
      (Πʳ i, [HomotopyGroup N (R i) (b i),
        (⊥ : Subgroup (HomotopyGroup N (R i) (b i)))]))
    (he : ∀ (p : GenLoop N
        (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)
        (singletonBasepoint b)) (i : ι),
      e (⟦p⟧ : HomotopyGroup N
          (RestrictedProduct R (fun j ↦ ({b j} : Set (R j))) cofinite)
          (singletonBasepoint b)) i =
        (⟦singletonCoordinateGenLoop N b p i⟧ : HomotopyGroup N (R i) (b i))) :
    e = homotopyGroupSingletonMulEquiv N b := by
  apply MulEquiv.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro p
  apply RestrictedProduct.ext
  intro i
  exact (he p i).trans (homotopyGroupSingletonMulEquiv_apply N b p i).symm

/-- Existence follows from the named comparison and its coordinate formula. -/
theorem exists_homotopyGroupSingletonMulEquiv (N : Type w)
    [DecidableEq N] [Nonempty N] (b : ∀ i, R i)
    [T1Space (RestrictedProduct R (fun i ↦ ({b i} : Set (R i))) cofinite)] :
    singletonHomotopyGroupComparisonSpec N b :=
  ⟨homotopyGroupSingletonMulEquiv N b, homotopyGroupSingletonMulEquiv_apply N b⟩

end RestrictedProduct
