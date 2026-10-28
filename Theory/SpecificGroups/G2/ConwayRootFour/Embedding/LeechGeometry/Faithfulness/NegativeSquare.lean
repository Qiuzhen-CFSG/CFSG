module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.Kernel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.NegativeSquare.Exclusion

/-!
# Negative-square lifts in the restricted Leech kernel

A negative-square lift fixing the literal U-fixed binary space commutes with
some nonidentity quaternionic U-scalar. Their product is an involution fixing
that space. The constructed long frame and the monomial short-displacement
calculation force this product to be a central sign. Thus the proposed lift's
projective image belongs to U; centralization of the full tetrahedral group I
then gives the contradiction.

The checked exclusion supplies exactly the negative-square premise of
`centralizerFaithful_of_lattice_involutions` in the parent `Faithfulness`
module. All geometric inputs are discharged, using the actual scalar embedding,
central quotient and mod-two action from `ScalarFour`.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, printed
pp.283–284, and Section 48, p.269. This is the negative-square kernel branch
for the restricted Leech action, not a separate numbered assertion of the book.
-/

public section

open Atlas.Conway Atlas.Lattices

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry

/-- A lift fixing the literal U-fixed space and projectively centralizing I
cannot square to central negation. No additional geometric premise remains. -/
theorem negative_square_kernel
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = negationIsometry) : False :=
  NegativeSquare.negative_square_kernel h hh hfix hsq

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
