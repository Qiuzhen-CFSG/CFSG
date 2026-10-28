module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.Contracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.CoordinateReduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.EndpointSquares

/-!
# Positive Ree involution coverage from two coordinate branches

Unique positive fixed coordinates reduce the coverage problem to the eighth
paired parameter. A zero parameter allows the endpoint-square calculation
to place the element in D; a nonzero parameter is the other conjugacy branch.
Both cases retain ambient conjugacy to the literal root curves in the contract.

The proved endpoint squares and the two explicit conjugacy constructions
discharge all inputs to `unipotentRootCoverage` for m ≥ 1. The conditional
assembly is retained as a separate interface.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal p.57; GLS3 Table 2.4, 2.4.5(d), and Lemma 3.3.9.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
open UnipotentClasses ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent

/-- The literal positive-subgroup coverage follows once the two conjugacy
branches and the separately owned endpoint-square calculation are proved. -/
theorem unipotentRootCoverage_of_coordinate_branches {m : ℕ}
    (hendpoint : EndpointSquareSupport m) (houtside : OutsideCConjugacy m)
    (hD : DConjugacy m) : UnipotentRootCoverage m := by
  intro x hx hne hsq
  obtain ⟨p, hp⟩ := exists_positiveWord m x hx
  have he : wordElement m p = x := by
    apply toSplitGroup_injective m
    rw [wordElement_coe, hp]
  by_cases h0 : p.pair 0 = 0
  · exact hD x (hendpoint p h0 x hp hsq) hne hsq
  · simpa only [he] using houtside p h0 (by simpa only [he] using hsq)

/-- Every nonidentity square-one element of the positive Ree subgroup is
ambient-conjugate to a nonzero point of the long- or short-root curve.
The endpoint-square and both coordinate-conjugacy premises are discharged. -/
theorem unipotentRootCoverage (m : ℕ) (hm : 1 ≤ m) : UnipotentRootCoverage m :=
  unipotentRootCoverage_of_coordinate_branches
    (ElementaryTwoBound.Replacement.mem_D_of_positiveWord_sq m)
    (outsideCConjugacy m) (dConjugacy m hm)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
