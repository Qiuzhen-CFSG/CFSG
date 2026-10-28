module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.SingularOrbit.Primitive
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.SingularOrbit.Sextet

/-!
# The singular orbit of the reduced octad lattice

A genuine compatible sextet supplies a nonmonomial element of the literal
integral centralizer. Primitivity of the exact binary Omega action then
makes the reduced action transitive once its monomial axis stabilizer
contains the Omega stabilizer.

The remaining stabilizer premise is precisely the independent input used by
`projectiveLatticeEquivOfLocalGeometry`. It must be discharged before the
unconditional `singular_orbit` theorem is asserted. No norm-representative,
unrelated group-model, or full E8-isometry assumption is used.

Source: Aschbacher, *Sporadic Groups* (1994), 25.3–25.5, pp.133–134.
-/

public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

/-- The actual singular-orbit conclusion with only the separately owned
monomial stabilizer calculation still explicit. The sextet premise is proved. -/
theorem singular_orbit_of_axis_stabilizer
    (C : Coordinates) (i : Coordinate)
    (hStabilizer : ∀ g : SelectedGeometry.Orthogonal,
      g.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i)) →
      (g ∈ C.orthogonalAction.range ↔ g ∈ SelectedGeometry.omega))
    (w : SelectedGeometry.Space) (hw0 : w ≠ 0) (hw : SelectedGeometry.form w = 0) :
    ∃ g : centralizer,
      (C.orthogonalAction g).val (C.coordinates (reduction (axis i))) = w :=
  singular_orbit_of_stabilizer_and_escape C i
    (fun a ha => (hStabilizer a.val ha).mpr a.prop)
    exists_nonmonomial_centralizer w hw0 hw

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

