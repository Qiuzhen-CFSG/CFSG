module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.ConstructionInputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.Reflection
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialReduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy

/-!
# Scalar-class fusion for the placed local A₅

The placed reflection has order two and binary fixed-space dimension six.
The proved exclusion of this dimension for positive-square integral lifts
forces its lift to square to negation. The odd-cross argument places that
lift in the signed Golay permutation group, where the Mathieu and sign
conjugators identify its scalar class in the literal Leech central quotient.
A₅ fusion transports that class to the specified `A5Placement.involution`.

The final theorem discharges both premises of the retained conditional
assembly. It supplies the conjugacy required by `exists_geometry_of_placement`;
constructing the placement remains an independent obligation. Neither the
construction of `Geometry` nor faithfulness of the whole tetrahedral centralizer
is used.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using the root-four class in Lemma 47.2, p.261, and the conventions on p.269.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

/-- The local fusion assembly, with its two integral inputs left explicit
for reuse. A negative-square calculation alone is not used as
a conjugacy theorem. -/
theorem A5Placement.involution_isConj_scalar_of_lattice
    {L : LongFrame} (P : A5Placement L)
    (hpositive : ∀ h : LeechIsometryGroup,
      leechCentralProjection h ∈ centralizerI → h ^ 2 = 1 →
      Module.finrank Bit
        ↥(fixedSpace ⊓ LinearMap.ker (difference (leechCentralProjection h))) ≠ 6)
    (hmono : ∀ m : GolayMonomialGroup,
      (monomialEmbedding m) ^ 2 = negationIsometry →
      IsConj (leechCentralProjection (monomialEmbedding m)) scalarInvolution) :
    IsConj (P.involution : LeechCentralQuotient) scalarInvolution := by
  obtain ⟨h, hh, hsq⟩ := P.reflection_lift_of_positive_exclusion hpositive
  apply P.involution_isConj_reflection.trans
  rw [← hh]
  exact Fusion.projection_isConj_scalar_of_monomial hmono h hsq

/-- Every placed local A₅ has its specified involution in the actual scalar
class. The positive-square exclusion and genuine monomial conjugacy discharge
both integral premises of the fusion assembly. -/
theorem A5Placement.involution_isConj_scalar {L : LongFrame} (P : A5Placement L) :
    IsConj (P.involution : LeechCentralQuotient) scalarInvolution :=
  P.involution_isConj_scalar_of_lattice
    (Fusion.positive_fixedSpace_finrank_ne_six L)
    Fusion.monomial_projection_isConj_scalar

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
