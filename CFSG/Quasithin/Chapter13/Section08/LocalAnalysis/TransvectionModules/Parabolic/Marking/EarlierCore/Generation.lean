module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Seed

/-!
# Generation of the actual natural subgroup by L₂

The fixed-point-free cubic actor in the plane stabilizer's residual supplies
both natural-model calculations. Finite residual-image transport lifts them
to the literal source subgroup V, without a specialized generation premise.

Source: Aschbacher–Smith, proof of 13.8.6(3), printed p.948.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

include d

/-- Both ambient generation identities follow from the natural action. -/
theorem plane_generation :
    V = conjugateSpanBy V₃ (localResidual L V₂) ∧ V = ⁅V, localResidual L V₂⁆ := by
  obtain ⟨Q, hQ⟩ := d.image_sylow
  have hs : (Q : Subgroup d.permutation.range).map d.permutation.range.subtype ≤
      subspaceStabilizer naturalAction d.plane := by
    rw [hQ]
    exact d.sylow_plane_stable
  obtain ⟨hc, ho⟩ := PlaneGeometry.plane_generation d.permutation.range
    d.alternating_le_range Q d.plane d.hyperplane d.plane_dim d.hyperplane_dim hs
  exact ⟨d.conjugateSpan_eq_of_plane_orbit ho, d.commutator_eq_of_plane_displacement hc⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup
