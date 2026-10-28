module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionResiduals
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionSetup

/-!
# LocalAnalysisNaturalFourExclusionResiduals at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionResiduals`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem four_pointLocal_eq_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointLocal z = S.fourPointModuleNormalizer z := by
  apply le_antisymm
  · exact le_inf (S.hypothesis.source_point_normalizes_chosen_at structural S.chosen hz hz1 le_rfl)
      inf_le_right
  · exact inf_le_inf_right _ (S.normalizer_le_component_at structural)

theorem four_pointLocal_normalizes_perfect_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointLocal z ≤ normalizer (S.fourPointPerfect z : Set G) := by
  rw [S.four_pointLocal_eq_at structural hz hz1]
  exact (le_normalizer_embedded_pResidual 2 (S.fourPointModuleNormalizer z)).trans
    (normalizer_le_normalizer_characteristic_image (S.fourPointResidual z)
      (solvableResidual (S.fourPointResidual z)))

theorem FourResidualData.module_le_at {S : Setup T L V} {z : G}
    (D : S.FourResidualData z)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hz : z ∈ V) (hz1 : z ≠ 1) : V ≤ S.fourPointPerfect z := by
  exact D.moved.le.trans (le_normalizer_iff_commutator_le_right.mp
    ((S.four_module_le_pointLocal hz).trans
      (S.four_pointLocal_normalizes_perfect_at structural hz hz1)))

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

