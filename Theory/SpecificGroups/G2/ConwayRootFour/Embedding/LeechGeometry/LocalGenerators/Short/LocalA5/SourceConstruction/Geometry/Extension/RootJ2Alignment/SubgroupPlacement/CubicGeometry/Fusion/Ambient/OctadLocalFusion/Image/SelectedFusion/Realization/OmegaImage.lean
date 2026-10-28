module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.ProjectiveLattice
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity

/-!
# Comparing the octad lattice image with the extraspecial quotient action

Let Q be the literal restriction kernel. The projective lattice kernel
Q⟨s⟩, where s is the octad sign, lies in the kernel of conjugation on Q/Z(Q).
If the projective lattice image is Omega and the relative centralizer of Q
is a two-group, simplicity forces equality of these kernels. The first
isomorphism theorem then identifies the actual quotient-action image
abstractly with Omega.

The ambient commutator bound finishes the comparison: the image is perfect,
so it lies in the Siegel-generated Omega subgroup, and equal cardinality
gives equality. This works for every square-compatible coordinate system,
without identifying the lattice module with Q/Z(Q).

The projective lattice-image isomorphism and ambient commutator bound remain
explicit independent inputs. Their producers must discharge both before
the requested unconditional-in-these-inputs image theorem is assembled.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 and 46.1,
pp.132–134 and 251.
-/

@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization
namespace OmegaImage

private theorem omega_simple : IsSimpleGroup SelectedGeometry.omega := by
  let : MulAction.IsPreprimitive
      ClassicalOrthogonal.BinaryEightObstruction.Simplicity.E
      ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Point :=
    ClassicalOrthogonal.BinaryEightObstruction.Simplicity.singular_preprimitive
  exact ClassicalOrthogonal.BinaryEightObstruction.Simplicity.elementary_simple_of_preprimitive

private theorem omega_perfect : Group.IsPerfect SelectedGeometry.omega := by
  let := ClassicalOrthogonal.BinaryEightObstruction.Simplicity.singular_pretransitive
  exact ClassicalOrthogonal.BinaryEightObstruction.Simplicity.perfect_of_pretransitive

private theorem omega_not_twoGroup : ¬ IsPGroup 2 SelectedGeometry.omega := by
  let := omega_simple
  let := omega_perfect
  intro h
  exact Group.IsPerfect.not_isNilpotent SelectedGeometry.omega h.isNilpotent

/-- A simple projective lattice image identifies the kernel of the actual
central-quotient action, using the relative-centralizer two-group bound. -/
theorem quotientAction_ker_eq_of_latticeImage
    (hExtra : IsExtraspecial 2 action.ker)
    (hc : IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer)))
    (e : ProjectiveLatticeImage ≃* SelectedGeometry.omega) :
    kernelQuotientAction.ker = projectiveLatticeKernel := by
  let := omega_simple
  let f : centralizer →* SelectedGeometry.omega :=
    e.toMonoidHom.comp projectiveLatticeMap
  have hf : Function.Surjective f := e.surjective.comp projectiveLatticeMap_surjective
  have hfk : f.ker = projectiveLatticeKernel := by
    ext g
    change e (projectiveLatticeMap g) = 1 ↔ g ∈ projectiveLatticeKernel
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  apply le_antisymm ?_ (projectiveLatticeKernel_le_quotientAction_ker hExtra)
  have hn : (kernelQuotientAction.ker.map f).Normal :=
    (inferInstance : kernelQuotientAction.ker.Normal).map f hf
  have htwo := (kernelQuotientAction_isTwoGroup_of_centralizer hExtra hc).map f
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · rw [← hfk]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  · rw [htop] at htwo
    exact (omega_not_twoGroup (htwo.of_equiv Subgroup.topEquiv)).elim

/-- Comparison with the lattice image uses equality of the literal kernels;
it does not identify the two natural eight-dimensional modules. -/
def rangeEquivOfLatticeImage
    (hExtra : IsExtraspecial 2 action.ker) (C : SquareCoordinates)
    (hc : IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer)))
    (e : ProjectiveLatticeImage ≃* SelectedGeometry.omega) :
    C.orthogonalAction.range ≃* SelectedGeometry.omega :=
  (QuotientGroup.quotientKerEquivRange C.orthogonalAction).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (C.orthogonalAction_ker.trans (quotientAction_ker_eq_of_latticeImage hExtra hc e))).trans e)

/-- Perfectness and the ambient commutator bound identify any isomorphic subgroup with the
literal Siegel-generated Omega subgroup of this full orthogonal group. -/
theorem subgroup_eq_omega_of_equiv
    (hDerived : commutator SelectedGeometry.Orthogonal ≤ SelectedGeometry.omega)
    (R : Subgroup SelectedGeometry.Orthogonal) (e : R ≃* SelectedGeometry.omega) :
    R = SelectedGeometry.omega := by
  let := omega_perfect
  let : Group.IsPerfect R :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hle : R ≤ SelectedGeometry.omega := by
    rw [← Subgroup.commutator_eq_self (H := R)]
    exact (Subgroup.commutator_mono le_top le_top).trans hDerived
  exact Subgroup.eq_of_le_of_card_ge hle (Nat.card_congr e.toEquiv).symm.le

end OmegaImage

/-- Conditional source assembly: the two independent geometric inputs are
the genuine projective lattice-image model and the intrinsic commutator bound. -/
theorem orthogonalAction_range_of_latticeImage
    (hExtra : IsExtraspecial 2 action.ker) (C : SquareCoordinates)
    (hc : IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer)))
    (e : OmegaImage.ProjectiveLatticeImage ≃* SelectedGeometry.omega)
    (hDerived : commutator SelectedGeometry.Orthogonal ≤ SelectedGeometry.omega) :
    C.orthogonalAction.range = SelectedGeometry.omega :=
  OmegaImage.subgroup_eq_omega_of_equiv hDerived C.orthogonalAction.range
    (OmegaImage.rangeEquivOfLatticeImage hExtra C hc e)
end Realization
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
