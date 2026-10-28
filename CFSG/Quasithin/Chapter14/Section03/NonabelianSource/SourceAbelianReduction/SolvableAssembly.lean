module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Complete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.Completion

/-!
# Solvable-input assembly for the original nonabelian transfer

The 14.3.20 self-centralization and 14.3.22 core-collapse producers are
proved on the literal original factor.  Consequently the nonabelian transfer
needs only terminal solvability: 14.3.21 supplies outside-point nonfusion
from that same solvability.  This adapter keeps the rank-two plane and all
original M, Mc and flag hypotheses, while removing the three discharged
callbacks from the public endpoint.

Source: Aschbacher--Smith, 14.3.20--22, printed pp.997--999.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open SelfCentralizing CoreCollapse
variable {G : Type*} [Group G] [Finite G]

/-- The original nonabelian transfer with self-centralization and core
collapse discharged by their completed source producers. -/
theorem source_theoremE_of_nonabelian_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hsolvable : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_solvable_self_and_collapse
    hG T hempty hM hu hmany hrank hsolvable
  · intro hnot F hneF g hgP hgH hs
    obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
    let := rankTwoSeed_elementary (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)
    exact factorSelfCentralizing_of_source_hypotheses hG T hempty hM hu hmany hcard e hnot
      F hneF g hgP hgH hs
  · intro hnot F hneF g hgP hgH hs hself hout
    obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
    let := rankTwoSeed_elementary (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)
    exact source_core_eq_U hG T hempty hM hu hmany hcard e hnot F hneF g hgP hgH hs hself hout
  · exact hne

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
