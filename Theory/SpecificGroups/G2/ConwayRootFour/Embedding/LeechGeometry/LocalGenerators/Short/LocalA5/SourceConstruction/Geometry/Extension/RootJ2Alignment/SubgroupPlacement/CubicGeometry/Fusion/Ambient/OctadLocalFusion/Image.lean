module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Restriction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass

/-!
# Reduction of octad image fusion to the specified local cubic class

The coordinate geometry and central-quotient comparison are proved in the
leaves. Final image fusion still requires both the polynomial class-selection
argument and conjugacy of that quaternion commutator class in the actual image.
The theorem below keeps these two independent obligations explicit; it does
not assert the unconditional `imageFusion` requested by the assembly owner.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, 25.9, §46 and 49.3(2).
-/

@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

/-- The whole-Leech class-selection and actual-image conjugacy obligations assemble here. -/
theorem imageFusion_of_quaternion_class
    (hselect : PolynomialClassSelection) (hfuse : QuaternionImageFusion) : ImageFusion := by
  intro u v hu hv
  obtain ⟨r, hr, hor, hpr⟩ := hu
  obtain ⟨s, hs, hos, hps⟩ := hv
  obtain ⟨c, hc⟩ := hfuse r s hor hos (hselect r hor hpr) (hselect s hos hps)
  exact ⟨c, by simpa only [hr, hs] using hc⟩


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
