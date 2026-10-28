module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.ReducedKernel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.LocalToGlobal

/-!
# Assembly of the genuine projective octad-lattice image

Binary reduction of the actual integral lattice has exactly the published
projective kernel. Split coordinates, singular-vector transitivity, and the
monomial axis stabilizer therefore give an isomorphism of that projective
image with the literal Siegel-generated Omega subgroup.

The reduced kernel is proved here without extraspeciality. The three geometric
inputs remain explicit until their independent coordinate, monomial, and sextet
calculations are supplied. This conditional assembly does not assert the
requested unconditional-in-these-inputs lattice-image theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, especially 25.5(7),
pp.132–134.
-/

@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage

/-- The source local-to-global argument, with its remaining geometric
premises stated on the literal octad reduction action. -/
def projectiveLatticeEquivOfLocalGeometry
    (C : LatticeModel.Coordinates) (i : Coordinate)
    (hOrbit : ∀ w : SelectedGeometry.Space, w ≠ 0 → SelectedGeometry.form w = 0 →
      ∃ g : centralizer, (C.orthogonalAction g).val
        (C.coordinates (LatticeModel.reduction (LatticeModel.axis i))) = w)
    (hStabilizer : ∀ g : SelectedGeometry.Orthogonal,
      g.val (C.coordinates (LatticeModel.reduction (LatticeModel.axis i))) =
        C.coordinates (LatticeModel.reduction (LatticeModel.axis i)) →
      (g ∈ C.orthogonalAction.range ↔ g ∈ SelectedGeometry.omega)) :
    ProjectiveLatticeImage ≃* SelectedGeometry.omega :=
  C.projectiveEquiv LatticeModel.linearAction_ker_eq_projectiveLatticeKernel
    (LatticeModel.eq_omega_of_singular_orbit_and_stabilizer
      C.orthogonalAction.range (C.coordinates (LatticeModel.reduction (LatticeModel.axis i)))
      (C.axis_ne_zero i) (C.axis_singular i)
      (by
        intro w hw hq
        obtain ⟨g, hg⟩ := hOrbit w hw hq
        exact ⟨C.orthogonalAction.rangeRestrict g, hg⟩)
      hStabilizer)

/-- The assembled isomorphism is induced by the actual integral centralizer
action on the binary reduction, with the published quotient map. -/
theorem projectiveLatticeEquivOfLocalGeometry_mk
    (C : LatticeModel.Coordinates) (i : Coordinate)
    (hOrbit : ∀ w : SelectedGeometry.Space, w ≠ 0 → SelectedGeometry.form w = 0 →
      ∃ g : centralizer, (C.orthogonalAction g).val
        (C.coordinates (LatticeModel.reduction (LatticeModel.axis i))) = w)
    (hStabilizer : ∀ g : SelectedGeometry.Orthogonal,
      g.val (C.coordinates (LatticeModel.reduction (LatticeModel.axis i))) =
        C.coordinates (LatticeModel.reduction (LatticeModel.axis i)) →
      (g ∈ C.orthogonalAction.range ↔ g ∈ SelectedGeometry.omega))
    (g : centralizer) :
    (projectiveLatticeEquivOfLocalGeometry C i hOrbit hStabilizer
      (projectiveLatticeMap g)).val = C.orthogonalAction g := rfl

end Realization.OmegaImage
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
