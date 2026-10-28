module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.FlagGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Seed

/-!
# The source plane generates V₃ under the actual L₁

The coordinate calculation is transported using finite residual images and
conjugation on the literal V. This is the source identity needed to transport
the weight-four point into the whole plane in U_H/V₁.

Source: Aschbacher–Smith, §B.3, pp.83–85 and the flag calculation used
in 13.8.6, printed p.948.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

include d

/-- The flag-generation input for `CompatibleFlags.augmentation_source_flags`,
with J equal to the literal L₁. Its containment in H is supplied by 13.7.6. -/
theorem seed_eq_plane_conjugateSpan : V₃ = conjugateSpanBy V₂ (localResidual L V₁) := by
  apply le_antisymm
  · apply d.seed_le_of_naturalImage _ (d.line_le_plane.trans (le_conjugateSpanBy _ _))
    obtain ⟨Q, hQ⟩ := d.image_sylow
    have hp : (Q : Subgroup d.permutation.range).map d.permutation.range.subtype ≤
        subspaceStabilizer naturalAction d.point := by
      rw [hQ]
      exact d.sylow_flag_stable.1
    have hd : (Q : Subgroup d.permutation.range).map d.permutation.range.subtype ≤
        subspaceStabilizer naturalAction d.plane := by
      rw [hQ]
      exact d.sylow_plane_stable
    have hdp : d.plane ≤ Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form.orthogonal d.point := by
      rw [← d.hyperplane_eq_orthogonal]
      exact d.plane_le_hyperplane
    rw [d.hyperplane_eq_orthogonal, ← PlaneGeometry.flag_generation d.permutation.range
      d.alternating_le_range Q d.point d.plane d.point_dim d.plane_dim hp hd hdp]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, hw, rfl⟩
    rw [← d.one_image] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have he : (d.coordinate v).toAdd = w := hv
    have hv₂ : v.val ∈ V₂ := by
      rw [d.plane_eq]
      exact (mem_flagPreimage_iff _ _ v).mpr (he.symm ▸ hw)
    refine ⟨V.normalizerMonoidHom ⟨a.val, d.normalizes_V a.property⟩ v, ?_, ?_⟩
    · exact subset_closure ⟨a.val, ha, v.val, hv₂, rfl⟩
    · change (d.coordinate (V.normalizerMonoidHom
        ⟨a.val, d.normalizes_V a.property⟩ v)).toAdd = naturalAction (d.permutation a) w
      rw [d.conjugation, he]
  · exact conjugateSpanBy_le d.plane_le_seed d.one_normalizes_seed

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup
