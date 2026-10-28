module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Transport

/-!
# Transport of the plane-residual generation calculation

Finite residual images identify the actual L₂ action with the two-residual
of the natural-plane stabilizer. Its linear displacements and the orbit
of the hyperplane lift to actual commutators and conjugates in V.

The two purely linear model calculations are explicit premises here.
They must be discharged before assembling 13.8.6; these transfer lemmas
do not assert those model calculations or the source theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the natural-module identities in the proof of 13.8.6, printed p.948.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup

open Subgroup Representation.BinaryOffender

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

/-- Full displacement of the literal natural model gives V = [V,L₂]. -/
theorem commutator_eq_of_plane_displacement
    (h : subspaceCommutator naturalAction ⊤
      (residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.plane)) = ⊤) :
    V = ⁅V, localResidual L V₂⁆ := by
  apply le_antisymm
  · apply d.le_of_naturalImage_le le_rfl
    have hd := d.displacement_image (localResidual L V₂) V
    rw [d.naturalImage_self, d.two_image, h, commutator_comm] at hd
    rw [d.naturalImage_self]
    exact hd
  · exact le_normalizer_iff_commutator_le_left.mp
      ((localResidual_le L V₂).trans (le_sup_left.trans d.normalizes_V))

/-- The model hyperplane orbit generates the source subgroup by actual conjugation. -/
theorem conjugateSpan_eq_of_plane_orbit
    (h : Submodule.span (ZMod 2) {v : Natural |
      ∃ g ∈ residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.plane),
        ∃ w ∈ d.hyperplane, naturalAction g w = v} = ⊤) :
    V = conjugateSpanBy V₃ (localResidual L V₂) := by
  apply le_antisymm
  · apply d.le_of_naturalImage_le le_rfl
    rw [d.naturalImage_self, ← h]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, hw, rfl⟩
    rw [← d.two_image] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have he : (d.coordinate v).toAdd = w := hv
    have hv₃ : v.val ∈ V₃ := by
      rw [d.seed_eq]
      exact (mem_flagPreimage_iff _ _ v).mpr (he.symm ▸ hw)
    refine ⟨V.normalizerMonoidHom ⟨a.val, d.normalizes_V a.property⟩ v, ?_, ?_⟩
    · exact subset_closure ⟨a.val, ha, v.val, hv₃, rfl⟩
    · change (d.coordinate (V.normalizerMonoidHom
        ⟨a.val, d.normalizes_V a.property⟩ v)).toAdd = naturalAction (d.permutation a) w
      rw [d.conjugation, he]
  · exact conjugateSpanBy_le d.seed_le
      ((localResidual_le L V₂).trans (le_sup_left.trans d.normalizes_V))

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup

end
