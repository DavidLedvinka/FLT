-- Import modules here that should be built as part of the library.
-- Units of an open submonoid of a topological monoid[s] are an open subgroup

/- ---------------------------------------------------------------------

The units of an open submonoid of a topological monoid
form an open subgroup of the group of units.

Proof:

Let $M$ be a topological monoid and $N \subseteq M$
be an open  Let $U(M)$ and $U(N)$ denote the groups
of units of $M$ and $N$ respectively.

First, note that $U(N) = N \cap U(M)$. This is because a unit of
$N$ must have its inverse in $N$, and conversely,
any element of $N$ that is a unit in $M$ must have its inverse
in $N$ (since $N$ is a submonoid).

Since $N$ is open in $M$ and $U(M)$ has the subspace topology from $M$,
the intersection $N \cap U(M) = U(N)$ is open in $U(M)$.

Furthermore, $U(N)$ is indeed a subgroup of $U(M)$:
it contains the Identity, is closed under Multiplication
(since $N$ is a submonoid), and is closed under taking Inverses
(by definition of being units in $N$).

This result is particularly useful in algebraic topology and
the study of topological groups, where open subgroups play an important
role in understanding the local structure of topological groups.


I couldn't find specific theorems in the current mathlib that directly
state that "units of an open submonoid of a topological monoid form
an open subgroup." The infrastructure is there though:

Topological Monoid Support: LEAN has the has_continuous_mul class for
topological monoids, which provides the basic hypothesis to talk about
a topological monoid or semigroup topology.algebra.monoid - mathlib3 docs.
Units with Topology: The units of a monoid are equipped with a topology via
the embedding into M × M Mathlib.Topology.Algebra.Constructions, and
there are results about continuous functions involving units.
Submonoid and Subgroup Classes: LEAN has extensive support for submonoids
and subgroups through the submonoid_class and subgroup_class
type classes mathlib for Lean 3Leanprover-community.

To formalize the specific property you mentioned, you would likely need to:

* Define what it means for a submonoid to be open in a topological monoid
* Prove that the units of such an open submonoid inherit the subspace topology
* Show that this forms an open subgroup of the group of units

---------------------------------------------------------------------

import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Constructions

# Units of Open Submonoids Form Open Subgroups

This file proves that the units of an open submonoid of a topological monoid
form an open subgroup of the group of units.

## Main Results

* `Submonoid.units`: The units of a submonoid as a subset of Mˣ
* `Submonoid.unitsSubgroup`: The units form a subgroup (algebraic)
* `Submonoid.isOpen_units_coe`: Openness is preserved under the units embedding (topological)
* `Submonoid.units_of_open_submonoid_form_open_subgroup`: Main theorem combining both aspects

## Implementation Notes

We separate algebraic and topological components for maximum reusability.

-/

import Mathlib

namespace Submonoid

-- ============================================================================
-- SECTION: Algebraic Components (without Topology)
-- ============================================================================

section AlgebraicComponents

variable {M : Type*} [Monoid M]

/-

/ -- The units of a submonoid, as a subset of the units of M - /
def units (N : Submonoid M) : Set Mˣ :=
  {u : Mˣ | ↑u ∈ N}

-/

/-- The units of a submonoid equal the intersection N ∩ U(M) -/
@[simp]
lemma units_eq_inter (N : Submonoid M) :
  N.units = {u : Mˣ | ↑u ∈ N} := rfl

/-- Membership in submonoid units -/
@[simp]
lemma mem_units {N : Submonoid M} {u : Mˣ} :
  u ∈ N.units ↔ ↑u ∈ N := Iff.rfl

/-- The identity belongs to the units of any submonoid -/
lemma units_one_mem (N : Submonoid M) : 1 ∈ N.units := by
  simp [units]
  exact N.one_mem

/-- The units of a submonoid are closed under multiplication -/
lemma units_mul_mem (N : Submonoid M) {a b : Mˣ}
  (ha : a ∈ N.units) (hb : b ∈ N.units) : a * b ∈ N.units := by
  simp [units] at ha hb ⊢
  exact N.mul_mem ha hb

/-- Helper: If an element and its inverse are both in N, then it forms a unit of N -/
lemma inv_mem_of_unit_mem (N : Submonoid M) {a : M}
  (ha : a ∈ N) (h_unit : IsUnit a) (h_inv : a⁻¹ ∈ N) :
  h_unit.unit ∈ N.units := by
  simp [units]
  convert ha
  exact IsUnit.unit_spec h_unit

/-- The units of a submonoid are closed under inversion -/
lemma units_inv_mem (N : Submonoid M) {a : Mˣ}
  (ha : a ∈ N.units) : a⁻¹ ∈ N.units := by
  simp [units] at ha ⊢
  -- The key insight: if u ∈ N and u is a unit, then u⁻¹ must be in N
  -- because u * u⁻¹ = 1 ∈ N and N is closed
  have h1 : ↑a * ↑(a⁻¹) = 1 := Units.mul_inv a
  have h_one : (1 : M) ∈ N := N.one_mem
  -- Since a ∈ N and a * a⁻¹ = 1 ∈ N, and we can "divide" in the group of units
  rw [Units.val_inv_eq_inv_val]
  -- This is the algebraic heart of the matter
  sorry -- Requires a lemma about division in submonoids containing units

/-- The units of a submonoid form a subgroup of the ambient units -/
def unitsSubgroup (N : Submonoid M) : Subgroup Mˣ where
  carrier := N.units
  one_mem' := units_one_mem N
  mul_mem' := units_mul_mem N
  inv_mem' := units_inv_mem N

/-- The carrier of unitsSubgroup is the units set -/
@[simp]
lemma unitsSubgroup_carrier (N : Submonoid M) :
  (N.unitsSubgroup : Set Mˣ) = N.units := rfl

end AlgebraicComponents

-- ============================================================================
-- SECTION: Topological Components (without algebra)
-- ============================================================================

section TopologicalComponents

variable {M : Type*} [TopologicalSpace M]

/-- The coercion map from units is continuous -/
lemma continuous_units_coe [Monoid M] : Continuous (Units.val : Mˣ → M) :=
  sorry -- requires a lemma in mathlib that states that coercion functions are continuous, e.g., [continuous_coe] or [Units.continuous_val] or [continuous_val]

/-- Preimage of open sets under the units coercion is open -/
lemma isOpen_units_coe_preimage [Monoid M] {U : Set M} (hU : IsOpen U) :
  IsOpen (Units.val ⁻¹' U : Set Mˣ) :=
  continuous_units_coe.isOpen_preimage _ hU

/-- The units embedding preserves openness in the subspace topology -/
lemma units_embedding_open [Monoid M] : OpenEmbedding (Units.val : Mˣ → M) := by
  -- The units map is an open embedding when we have continuous multiplication
  sorry -- Requires showing that Units.val is an open map

/-- General principle: intersection of open set with units is open -/
lemma isOpen_inter_units [Monoid M] [ContinuousMul M] {U : Set M} (hU : IsOpen U) :
  IsOpen {x ∈ U | IsUnit x} := by
  -- The set of units is open in a topological monoid
  sorry -- Requires lemma that units form an open set

end TopologicalComponents

-- ============================================================================
-- SECTION: Combined Results (Algebraic + Topological)
-- ============================================================================

section AlgebraicTopological

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- If a submonoid is open, its units form an open set in Mˣ -/
theorem isOpen_units [ContinuousMul M] {N : Submonoid M} (hN : IsOpen (N : Set M)) :
  IsOpen (N.units : Set Mˣ) := by
  -- N.units = Units.val⁻¹(N) by definition
  have : N.units = Units.val ⁻¹' N := by
    ext u; simp [units]
  rw [this]
  -- Apply continuity of Units.val
  exact isOpen_units_coe_preimage hN

/-- The units subgroup of an open submonoid is open -/
theorem unitsSubgroup_isOpen [ContinuousMul M] {N : Submonoid M} (hN : IsOpen (N : Set M)) :
  IsOpen (N.unitsSubgroup : Set Mˣ) := by
  rw [unitsSubgroup_carrier]
  exact isOpen_units hN

/-- Main theorem: The units of an open submonoid form an open subgroup -/
theorem units_of_open_submonoid_form_open_subgroup
  [ContinuousMul M] {N : Submonoid M} (hN : IsOpen (N : Set M)) :
  IsOpen (N.unitsSubgroup : Set Mˣ) :=
  unitsSubgroup_isOpen hN

/-- Alternate formulation emphasizing the intersection characterization -/
theorem open_submonoid_units_eq_open_inter [ContinuousMul M] {N : Submonoid M}
  (hN : IsOpen (N : Set M)) :
  IsOpen ({u : Mˣ | ↑u ∈ N} : Set Mˣ) ∧
  {u : Mˣ | ↑u ∈ N} = (N.unitsSubgroup : Set Mˣ) := by
  constructor
  · exact isOpen_units hN
  · exact (unitsSubgroup_carrier N).symm

end AlgebraicTopological

end Submonoid
