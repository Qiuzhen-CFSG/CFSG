module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient

/-!
# The ambient consumers of the octad restriction reduction

Apply `octadLocalFusion_of_restriction` to the existing octad-placement
consumers, using their literal central projection and cyclic-subgroup maps.
The two-group kernel premise is discharged. The image-classification premise
remains explicit; these theorems assert no unconditional fusion or placement.

Source: Aschbacher, *Sporadic Groups* (1994), 25.9, Exercise 9.6, and 49.3(2).
-/

public section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- Feed the actual local restriction obligations into the integral placement consumer. -/
theorem ambientFusion_of_integral_octad_restriction
    (hplacement : IntegralOctadPlacement)
    (himage : OctadRestriction.ImageFusion) : AmbientFusion :=
  ambientFusion_of_integral_octad_data hplacement
    (octadLocalFusion_of_imageFusion himage)

/-- The geometric placement form of the same actual ambient consumer. -/
theorem ambientFusion_of_octad_restriction
    (hplacement : OctadPlacement)
    (himage : OctadRestriction.ImageFusion) : AmbientFusion :=
  ambientFusion_of_octad_data hplacement
    (octadLocalFusion_of_imageFusion himage)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
