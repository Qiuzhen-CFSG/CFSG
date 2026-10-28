module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.IntegralSpectrum

/-!
# The reference eigenspace determinant

The explicit integral block realizes every special-linear matrix in the full
reference common-centralizer action, while the rank-24 integral Leech action
excludes the Singer matrix of order 63. Applying the conditional reduction
therefore gives determinant one for the intrinsic eigenspace action and a
concrete homomorphism to SL₃(4). Faithfulness remains the separate integral
sign-kernel assertion.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, states
X ≤ C_G(IX) ≅ SL₃(4) for X in the distinguished cubic class and I a root A₄
subgroup of C_G(X); 49.5, p.283, uses its natural and dual modules. This
This assembly assumes no source-class identification or completed G₂ embedding.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

/-- The full reference common centralizer acts with determinant one on the
intrinsic three-dimensional eigenspace. -/
theorem referenceEigenAction_det (g : referenceCentralizer) :
    LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1 :=
  referenceEigenAction_det_of_block_and_integral_obstruction
    referenceSpecialLinearCoverage referenceSingerExcluded g

/-- The determinant-one action yields the concrete special-linear homomorphism
used by the root-model consumer. -/
def referenceCentralizerToSLOfReferenceEigenAction :
    referenceCentralizer →* SL(3,F) :=
  referenceCentralizerToSLOfDet referenceEigenAction_det

theorem referenceCentralizerToSLOfReferenceEigenAction_apply
    (g : referenceCentralizer) :
    (referenceCentralizerToSLOfReferenceEigenAction g).val =
      referenceMatrixAction g := rfl

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
