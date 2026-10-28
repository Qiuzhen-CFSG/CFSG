module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionEndgame
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionResiduals

/-!
# LocalAnalysisNaturalFourExclusionEndgame at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionEndgame`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem four_pointPerfect_normalizer_of_residualData_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) (D : S.FourResidualData z) :
    S.fourPointCentralizer z ⊓ normalizer (S.fourPointPerfect z : Set G) =
      S.fourPointLocal z := by
  have he : conjugateSpanBy (S.fourPointPerfect z) (S.fourPointLocal z) =
      S.fourPointPerfect z :=
    le_antisymm (conjugateSpanBy_le le_rfl
      (S.four_pointLocal_normalizes_perfect_at structural hz hz1)) (le_conjugateSpanBy _ _)
  have h := D.pushingUp.normalizer_span_eq
  rwa [he] at h

theorem four_false_of_residual_normality_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) (D : S.FourResidualData z)
    (hn : S.fourPointCentralizer z ≤ normalizer (S.fourPointPerfect z : Set G)) : False := by
  have he := S.four_pointPerfect_normalizer_of_residualData_at structural hz hz1 D
  rw [inf_eq_left.mpr hn] at he
  exact S.four_all_pointCentralizers_escape escape e hd hz hz1 (he.le.trans inf_le_left)

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

