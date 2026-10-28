module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Lattice
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ComparisonData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ScalarInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison.Integral
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison.Scalars
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.MarkedComparison

/-!
# The explicit marked quaternion-to-icosian lattice comparison

`quaternionComparison` is the displayed rational linear equivalence. Its Gram
identity proves isometry, both integer coefficient certificates prove lattice
membership equivalence, and its quaternion blocks prove right scalar
compatibility. The theorems below apply all three results to the exact existing
`toLeechOfIcosianComparison` map, including its sign and scalar conventions.
The independent finite scalar marking remains with the realization assembly.

Source conventions: John Bray's ATLAS `6L34G1-Ar6aB0`, and Gerald Höhn's
icosian and Golay lattice comparison, ATLAS revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. The derived tables retain the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. This explicit comparison discharges the lattice
and scalar-intertwining premises of the marked block transport.
-/

@[expose] public noncomputable section
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

/-- Application to the literal retained Leech homomorphism. -/
theorem quaternionComparison_toLeech_injective :
    Function.Injective (toLeechOfIcosianComparison quaternionComparison
      quaternionComparison_form quaternionComparison_lattice) :=
  toLeechOfIcosianComparison_injective _ _ _

/-- The central sign preimage is exactly the original matrix sign subgroup. -/
theorem quaternionComparison_toLeech_signs :
    leechCentralSigns.comap (toLeechOfIcosianComparison quaternionComparison
      quaternionComparison_form quaternionComparison_lattice) = matrixSigns :=
  toLeechOfIcosianComparison_signs _ _ _

/-- The transported action commutes with the actual integral rational scalars. -/
theorem quaternionComparison_toLeech_scalar (g : matrixGroup) (u : rationalScalarUnits) :
    Commute (toLeechOfIcosianComparison quaternionComparison
      quaternionComparison_form quaternionComparison_lattice g) (icosianScalarsToCo0 u.val) :=
  toLeechOfIcosianComparison_scalar _ _ _ quaternionComparison_right g u

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
