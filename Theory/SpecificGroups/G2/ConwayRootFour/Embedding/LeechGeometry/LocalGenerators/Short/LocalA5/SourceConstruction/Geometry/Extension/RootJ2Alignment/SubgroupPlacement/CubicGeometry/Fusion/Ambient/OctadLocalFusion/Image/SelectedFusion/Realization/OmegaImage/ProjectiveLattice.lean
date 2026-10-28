module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting

/-!
# The projective octad-lattice quotient

The octad sign is central in its actual integral centralizer and restricts to
minus the identity on the octad lattice. Thus quotienting the centralizer by
the restriction kernel and this sign gives the projective lattice image.
For extraspecial restriction kernel, this projective kernel acts trivially on
the actual central quotient. This is the first comparison needed to pass from
Aschbacher's lattice calculation to conjugation on Q/Z(Q).

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, pp.132–134.
-/

@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization
namespace OmegaImage

/-- The marked sign, regarded as an element of its own centralizer. -/
def octadSign : centralizer := ⟨sign, mem_centralizer.mpr (Commute.refl sign)⟩

theorem octadSign_mem_center : octadSign ∈ Subgroup.center centralizer := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer.mp g.prop).eq

/-- The scalar killed on passing from the lattice action to its projectivization. -/
theorem action_octadSign (x : lattice) : action octadSign x = -x := by
  apply Subtype.ext
  exact x.prop

instance octadSign_zpowers_normal : (Subgroup.zpowers octadSign).Normal where
  conj_mem x hx g := by
    have hc : x ∈ Subgroup.center centralizer :=
      (Subgroup.zpowers_le.mpr octadSign_mem_center) hx
    rw [(Subgroup.mem_center_iff.mp hc g), mul_assoc, mul_inv_cancel, mul_one]
    exact hx

/-- Kernel of the projective lattice action, with the actual restriction map. -/
def projectiveLatticeKernel : Subgroup centralizer :=
  action.ker ⊔ Subgroup.zpowers octadSign

instance projectiveLatticeKernel_normal : projectiveLatticeKernel.Normal :=
  inferInstanceAs (action.ker ⊔ Subgroup.zpowers octadSign).Normal

/-- This subgroup is exactly the preimage of the scalar sign in the lattice image. -/
theorem projectiveLatticeKernel_eq_comap :
    projectiveLatticeKernel = (Subgroup.zpowers (action octadSign)).comap action := by
  rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq, sup_comm]
  rfl

/-- The genuine projective octad-lattice image, expressed as an ambient quotient. -/
abbrev ProjectiveLatticeImage := centralizer ⧸ projectiveLatticeKernel

/-- The literal quotient homomorphism used in the lattice-to-kernel comparison. -/
def projectiveLatticeMap : centralizer →* ProjectiveLatticeImage :=
  QuotientGroup.mk' projectiveLatticeKernel

theorem projectiveLatticeMap_surjective : Function.Surjective projectiveLatticeMap :=
  QuotientGroup.mk'_surjective _

theorem projectiveLatticeMap_ker :
    projectiveLatticeMap.ker = projectiveLatticeKernel := QuotientGroup.ker_mk' _

/-- Both the extraspecial kernel and the central lattice sign act trivially on Q/Z(Q). -/
theorem projectiveLatticeKernel_le_quotientAction_ker
    (hExtra : IsExtraspecial 2 action.ker) :
    projectiveLatticeKernel ≤ kernelQuotientAction.ker := by
  rw [kernelQuotientAction_ker_eq hExtra]
  apply sup_le le_sup_left
  apply le_sup_of_le_right
  exact (Subgroup.zpowers_le.mpr octadSign_mem_center).trans
    (Subgroup.center_le_centralizer _)

end OmegaImage
end Realization
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
