module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.Source
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Placement

/-!
# Actual algebraic torus placement of the binary Ree odd elements

The connected F4 carrier satisfies the newly assembled Borel element-coverage
theorem. The existing finite-order semisimplicity, unipotent-radical
conjugation and maximal-torus conjugacy proofs therefore produce an actual
conjugator and the literal positive-coroot coordinates, with no additional
Borel coverage premise.

Sources: GLS3 Theorem 1.6.3 and §§1.14, 2.8; Guralnick–Malle II,
Lemma 8.8, internal p.57.
-/

public section
open Theory.AlgebraicGroup
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage

/-- The actual order-five/order-thirteen elements lie in conjugates of the
specified coroot torus, with their original coefficient embeddings retained. -/
theorem placement (F : Type*) [Field F] [IsAlgClosed F] [CharP F 2] : Placement F :=
  placement_of_borel_coverage (fun hG _ hB x => BorelElementCoverage.exists_conjugate_mem hG hB x)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
