module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.Preparation
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Restriction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.SylowLift
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Kernel

/-!
# Reducing local octad cubic fusion to the actual restriction image

Lift each local binary fixed-free cubic to an order-three integral isometry
commuting with the marked octad sign. Its restriction belongs to the literal
octad action image and retains a polynomial lift on the whole Leech lattice.
Conjugacy in that image lifts through a two-group kernel by Sylow conjugacy.
Finally the original central projection gives the required conjugator in the
centralizer of `ambientOctad`, with the published orientation of subgroup maps.

`Kernel` proves the two-group property of the literal restriction kernel.
Thus `octadLocalFusion_of_imageFusion` retains only the concrete image
classification. This is conditional assembly and does not assert
`OctadLocalFusion` unconditionally. Final discharge of the image premise belongs
here; ambient placement and ambient fusion remain with their existing owners.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, 25.9, Exercise 9.6,
and 49.3(2), pp.280–281. The latter concerns the specified cubic class; the
whole-lattice polynomial in the image obligation retains its necessary
fixed-free class-selection problem.
-/

@[expose] public noncomputable section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
open OctadRestriction

/-- The actual restriction kernel and image classification suffice for the published local fusion. -/
theorem octadLocalFusion_of_restriction
    (hkernel : IsPGroup 2 action.ker) (himage : ImageFusion) : OctadLocalFusion := by
  intro a b hca hcb hoa hob hfa hfb
  obtain ⟨r, hr, hor, hpr⟩ := exists_polynomial_lift_in_centralizer hoa hfa hca
  obtain ⟨s, hs, hos, hps⟩ := exists_polynomial_lift_in_centralizer hob hfb hcb
  have him := himage ⟨action r, ⟨r, rfl⟩⟩ ⟨action s, ⟨s, rfl⟩⟩
    ⟨r, rfl, hor, hpr⟩ ⟨s, rfl, hos, hps⟩
  obtain ⟨c, hc⟩ := cyclic_fusion_of_image_fusion action hkernel hor hos him
  refine ⟨projection c, projection_commutes c, ?_⟩
  have he := congrArg (fun P : Subgroup centralizer => P.map projection) hc
  simpa [MonoidHom.map_zpowers, MulAut.conj_apply, hr, hs] using he

/-- Only the actual image classification remains after discharging the kernel premise. -/
theorem octadLocalFusion_of_imageFusion (himage : ImageFusion) : OctadLocalFusion :=
  octadLocalFusion_of_restriction kernel_isTwoGroup himage

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
