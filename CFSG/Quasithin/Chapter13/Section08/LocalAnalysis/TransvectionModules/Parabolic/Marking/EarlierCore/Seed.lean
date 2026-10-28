module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Transport
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualAction

/-!
# The source hyperplane and its point-residual generation

The actual Sylow action makes V₃ perpendicular to V₁. The two-residual
of the point stabilizer therefore preserves V₃ and generates V₃/V₁ by
commutators. Both conclusions are transported to the ambient subgroups
using the ordinary natural action; no triple-cover factorization is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877; the seed generation in 13.8.5–6,
printed pp.947–948. The separate L₂ calculation concerns a plane
stabilizer and is not asserted here.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup

open Subgroup Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

include d

/-- The compatible Sylow-stable line and hyperplane are perpendicular in
the natural model, without choosing canonical coordinates. -/
theorem hyperplane_eq_orthogonal : d.hyperplane = form.orthogonal d.point := by
  obtain ⟨Q, hQ⟩ := d.image_sylow
  apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes.sylow_invariant_hyperplane_eq_orthogonal
    d.permutation.range d.alternating_le_range Q d.point d.hyperplane
    d.point_dim d.hyperplane_dim
  · rw [hQ]
    exact d.sylow_flag_stable.1
  · rw [hQ]
    exact d.sylow_flag_stable.2

/-- The literal residual L₁ normalizes the actual V₃. -/
theorem one_normalizes_seed : localResidual L V₁ ≤ normalizer (V₃ : Set G) := by
  apply d.normalizes_seed_of_image _ ((localResidual_le L V₁).trans le_sup_left)
  rw [d.one_image, d.hyperplane_eq_orthogonal]
  exact (residual_le _).trans (inf_le_right.trans
    (stabilizer_le_orthogonal_stabilizer d.point))

/-- On the source quotient V₃/V₁, commutators with the actual L₁ generate
the whole space. This is an equality of ambient subgroups before quotienting. -/
theorem seed_eq_commutator_sup_line : V₃ = ⁅V₃, localResidual L V₁⁆ ⊔ V₁ := by
  apply le_antisymm
  · rw [commutator_comm]
    apply d.seed_le_commutator_sup_of_displacement
    rw [d.one_image, d.hyperplane_eq_orthogonal]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualAction.point_residual_displacement
      d.permutation.range d.alternating_le_range d.point d.point_dim
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp d.one_normalizes_seed)
      (d.line_le_plane.trans d.plane_le_seed)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup

end
