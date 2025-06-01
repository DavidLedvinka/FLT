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

* `Define` what it means for a submonoid to be open in a topological monoid
* `Prove` that the units of such an open submonoid inherit the subspace topology
* `Show` that this forms an open subgroup of the group of units

---------------------------------------------------------------------

import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Topology.Algebra.Group.Basic

-/

import Mathlib

namespace Submonoid

-- ============================================================================
-- SECTION: Algebraic Components (No topology needed)
-- ============================================================================

section AlgebraicComponents

variable {M : Type*} [Monoid M]

/-!
# Units of Open Submonoids Form Open Subgroups

This file proves that the units of an open submonoid of a topological monoid
form an open subgroup of the group of units.

## Main Results

* `Submonoid.mem_units_iff`: Characterization of membership in `N.units`
* `Submonoid.isOpen_units`: The units of an open submonoid form an open subset of Mˣ
* `Submonoid.units_of_open_submonoid_form_open_subgroup`: Main theorem

## Implementation Notes

We use the existing `Submonoid.units` from mathlib, which defines the units as:
  `S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹`
This is equivalent to `{u : Mˣ | ↑u ∈ S ∧ ↑(u⁻¹) ∈ S}`.
-/

-- ============================================================================
-- SECTION: Algebraic Components (using mathlib's definition)
-- ============================================================================

section AlgebraicComponents

variable {M : Type*} [Monoid M]

/-- Membership in the units of a submonoid is characterized by both u and u⁻¹ being in N -/
lemma mem_units_inter_iff {N : Submonoid M} {u : Mˣ} :
  u ∈ N.units ↔ ↑u ∈ N ∧ ↑(u⁻¹) ∈ N := by
  -- Unfold the definition from mathlib
  simp only [units, Subgroup.mem_mk, Submonoid.mem_inf, Submonoid.mem_comap,
             Submonoid.mem_inv, Units.coeHom_apply]
  -- This gives us exactly what we want
  rfl

/-- The carrier set of N.units equals {u : Mˣ | ↑u ∈ N ∧ ↑(u⁻¹) ∈ N} -/
lemma units_carrier (N : Submonoid M) :
  (N.units : Set Mˣ) = {u : Mˣ | ↑u ∈ N ∧ ↑(u⁻¹) ∈ N} := by
  ext u
  exact mem_units_inter_iff

end AlgebraicComponents

/-- The carrier of unitsSubgroup is the units set -/
@[simp]
lemma unitsSubgroup_carrier (N : Submonoid M) :
  (N.units : Set Mˣ) = N.units := rfl

end AlgebraicComponents

-- ============================================================================
-- SECTION: Topological Components (Topology without algebra)
-- ============================================================================

section TopologicalComponents

variable {M : Type*} [TopologicalSpace M]

/-- The coercion map from units is continuous -/
lemma continuous_units_coe [Monoid M] : Continuous (Units.val : Mˣ → M) :=
  Units.continuous_val

/-- Preimage of open sets under the units coercion is open -/
lemma isOpen_units_coe_preimage [Monoid M] {U : Set M} (hU : IsOpen U) :
  IsOpen (Units.val ⁻¹' U : Set Mˣ) :=
  continuous_units_coe.isOpen_preimage _ hU

end TopologicalComponents

-- ============================================================================
-- SECTION: Combined Results (Algebraic + Topological)
-- ============================================================================

section CombinedResults

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- If a submonoid is open, its units form an open subset in Mˣ -/
theorem isOpen_units [ContinuousMul M] {N : Submonoid M} (hN : IsOpen (N : Set M)) :
  IsOpen (N.units : Set Mˣ) := by
  -- Use the characterization of N.units
  rw [units_carrier]

  -- We need to show {u : Mˣ | ↑u ∈ N ∧ ↑(u⁻¹) ∈ N} is open
  -- This is the intersection of two open sets
  simp only [Set.setOf_and]
  apply IsOpen.inter

  -- First set: {u : Mˣ | ↑u ∈ N} = Units.val ⁻¹' N
  · have : {u : Mˣ | ↑u ∈ N} = Units.val ⁻¹' N := by ext; simp
    rw [this]
    exact isOpen_units_coe_preimage hN

  -- Second set: {u : Mˣ | ↑(u⁻¹) ∈ N}
  · have : {u : Mˣ | ↑(u⁻¹) ∈ N} = (fun u => u⁻¹) ⁻¹' (Units.val ⁻¹' N) := by
      ext u; simp
    rw [this]
    -- The inverse map on units is continuous
    apply Continuous.isOpen_preimage
    · exact continuous_inv -- This uses ContinuousMul M
    · exact isOpen_units_coe_preimage hN

/-- Main theorem: The units of an open submonoid form an open subgroup -/
theorem units_of_open_submonoid_form_open_subgroup
  [ContinuousMul M] {N : Submonoid M} (hN : IsOpen (N : Set M)) :
  IsOpen (N.units : Set Mˣ) :=
  isOpen_units hN

end CombinedResults

end Submonoid
