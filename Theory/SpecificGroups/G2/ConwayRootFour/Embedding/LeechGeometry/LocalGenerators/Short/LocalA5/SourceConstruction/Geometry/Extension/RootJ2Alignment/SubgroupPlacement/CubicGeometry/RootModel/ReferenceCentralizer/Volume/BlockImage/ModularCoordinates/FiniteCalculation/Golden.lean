module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Model
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Cubic
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Golden.Certificates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Transport

/-!
# The four golden embeddings and their scalar-comparison consumer

The finite witnesses combine the binary basis certificates with the global
field and contragredient automorphisms of SL₃(GoldenFour). The consumer uses
the existing transport through the actual scalarFieldEquiv and leaves only
ScalarComparison explicit; the reference-block assembly owns its discharge.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284,
the natural and dual SL₃(4) constituents. The displayed matrices and integral
comparison retain John Bray and Gerald Höhn's ATLAS attribution and Research
and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation
namespace Golden
open Long.Block Long.Block.Realization

/-- All four finite witnesses, with every clause extended from six binary basis vectors. -/
def coordinates (inverse opposite : Bool) : GoldenCoordinates inverse opposite where
  embed := (embedding (columns inverse opposite)).toAddMonoidHom
  injective := embedding_injective (columns inverse opposite) (retraction inverse opposite)
    (left_inverse inverse opposite)
  twist := twist inverse opposite
  fixed v := fixed_of_basis (embedding (columns inverse opposite))
    (fixed_certificate inverse opposite) v
  scalar a v := scalar_of_tau (embedding (columns inverse opposite)) opposite
    (scalar_certificate inverse opposite) a v
  cubic v := cubic_of_basis inverse opposite (embedding (columns inverse opposite))
    (cubic_certificate inverse opposite) v
  generatorA v := generator_of_basis (embedding (columns inverse opposite))
    (generatorACoordinates.map (Int.castRingHom Bit)) (twist inverse opposite threeA)
    (generatorA_certificate inverse opposite) v
  generatorB v := generator_of_basis (embedding (columns inverse opposite))
    (generatorBCoordinates.map (Int.castRingHom Bit)) (twist inverse opposite threeB)
    (generatorB_certificate inverse opposite) v

end Golden

/-- The natural, dual, and field-twisted finite constituents in all four orientations. -/
theorem goldenCoordinates (inverse opposite : Bool) :
    Nonempty (GoldenCoordinates inverse opposite) := ⟨Golden.coordinates inverse opposite⟩

/-- Application to the literal integral-basis coordinates. The sole remaining
premise is the independent comparison with the rational inverse-right scalars. -/
theorem finiteCoordinates_of_golden (h : ScalarComparison)
    (inverse : Bool) (u : Long.Block.Realization.rationalScalarUnits)
    (hu : orderOf (Long.Block.Realization.rationalScalarToFive u) = 3) :
    Nonempty (FiniteCoordinates inverse u) :=
  finiteCoordinates_of_comparisons h goldenCoordinates inverse u hu

end ReferenceBlock.ModularCoordinates.FiniteCalculation
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
