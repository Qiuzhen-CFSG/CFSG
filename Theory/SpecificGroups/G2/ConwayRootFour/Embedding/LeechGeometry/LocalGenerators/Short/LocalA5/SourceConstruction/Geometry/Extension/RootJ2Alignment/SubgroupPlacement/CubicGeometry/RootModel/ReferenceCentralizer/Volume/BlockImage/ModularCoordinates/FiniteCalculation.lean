module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Cubic
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Golden
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Scalars

/-!
# Integral-basis finite calculation for the reference block

Both orientations of the cubic have checked integral coordinate matrices.
The four GoldenFour embeddings and the rational-unit scalar comparison
construct the finite coordinates for every projective cubic scalar. Transport
through the actual scalarFieldEquiv preserves injectivity, quaternion fixedness,
the full scalar rule, the cubic equation, and both literal generator equations.
Thus neither finite comparison remains a premise of finiteCoordinates.

This supplies the finite-module input to referenceBlockCoordinates_of_finiteData.
The geometric alignment transport remains with that theorem's assembly owner.

Source consumer: Aschbacher, Sporadic Groups (1994), 49.5, pp.283–284.
John Bray's matrices and Gerald Höhn's icosian comparison retain the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
namespace ReferenceBlock.ModularCoordinates

/-- The actual integral-basis finite coordinates for either left-cubic
orientation and every rational scalar with projective order three. -/
theorem finiteCoordinates (inverse : Bool) (u : Long.Block.Realization.rationalScalarUnits)
    (hu : orderOf (Long.Block.Realization.rationalScalarToFive u) = 3) :
    Nonempty (FiniteCoordinates inverse u) :=
  finiteCoordinates_of_comparisons FiniteCalculation.scalarComparison
    FiniteCalculation.goldenCoordinates inverse u hu

end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
