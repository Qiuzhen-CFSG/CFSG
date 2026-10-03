module
public import Glauberman.Signalizer.LocalToGlobal
public import Theory.GroupTheory.Signalizer.Induction

/-!
# Solvable binary signalizer completion

A finite elementary abelian two-group of order at least eight acting on a
finite group has complete odd solvable signalizer families. The family has
only its original local hypotheses: odd solvable invariant values fixed by
the indexing actor, and balance. Completeness concerns the actual supremum
of those subgroups; the existing fixed-value theorem gives exact recovery
of every value as the fixed subgroup of that supremum.

The proved local-to-global theorem supplies the criterion in the general
minimal-counterexample induction. That induction passes through the exact
restricted and quotient actions and decreases ambient order plus the sum
of the orders of the values. No local completeness or normalizer
factorization hypothesis remains in this final theorem.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, Theorem 11.2.9,
printed p.325 (the binary solvable signalizer theorem of Goldschmidt),
using the proved factorization argument of Lemmas 11.2.6–11.2.8.
-/

namespace Glauberman
open Theory.GroupTheory

/-- Every odd solvable signalizer family for an elementary binary actor of
order at least eight is complete under its original supplied action. -/
public theorem solvable_two_signalizer_complete
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) (hA : 8 ≤ Nat.card A) : θ.IsComplete := by
  exact TwoSignalizerFamily.complete_of_local_criterion hA
    (fun H _ _ _ η hcard hlocal => complete_of_locally_complete η hcard hlocal) θ

end Glauberman
