module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.Transport

/-!
# Assembly of the octad central-quotient orthogonal realization

The transport module constructs the orthogonal action and proves its
equivariance from square-compatible coordinates. It also identifies its kernel
with Q C_H(Q). This assembly applies both facts to the literal integral
centralizer and restriction kernel.

The three geometric inputs remain explicit: split square coordinates, exact
Omega image, and a two-group relative centralizer. Their independent producers
must discharge them before the conditional extraspecial realization theorem
can be concluded. No existence of an OrthogonalModel is claimed from
extraspeciality alone in this module.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 and 46.1,
pp.132–134 and 251.
-/

public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization

/-- The local geometric inputs assemble to the published quotient-action model. -/
theorem nonempty_orthogonalModel_of_squareCoordinates (C : SquareCoordinates)
    (hExtra : IsExtraspecial 2 action.ker)
    (hRange : C.orthogonalAction.range = SelectedGeometry.omega)
    (hc : IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer))) :
    Nonempty OrthogonalModel :=
  ⟨C.toOrthogonalModel hRange (kernelQuotientAction_isTwoGroup_of_centralizer hExtra hc)⟩

end Realization
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

