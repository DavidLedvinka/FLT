-- This module serves as the root of the `ProofDemo` library.
-- Import modules here that should be built as part of the library.
-- Units of an open submonoid of a topological monoid[s] are an open subgroup

/----------------------------------------------------------------------

The units of an open submonoid of a topological monoid
form an open subgroup of the group of units.

Proof:

Let $M$ be a topological monoid and $N \subseteq M$
be an open submonoid. Let $U(M)$ and $U(N)$ denote the groups
of units of $M$ and $N$ respectively.

First, note that $U(N) = N \cap U(M)$. This is because a unit of
$N$ must have its inverse in $N$, and conversely,
any element of $N$ that is a unit in $M$ must have its inverse
in $N$ (since $N$ is a submonoid).

Since $N$ is open in $M$ and $U(M)$ has the subspace topology from $M$,
the intersection $N \cap U(M) = U(N)$ is open in $U(M)$.

Furthermore, $U(N)$ is indeed a subgroup of $U(M)$:
it contains the identity, is closed under multiplication
(since $N$ is a submonoid), and is closed under taking inverses
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

----------------------------------------------------------------------/

import Mathlib
