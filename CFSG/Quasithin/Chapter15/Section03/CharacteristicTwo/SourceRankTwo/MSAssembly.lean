module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo.SmallMSInput
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThree

/-!
# Original rank-two exclusion from the shared MS classifications

At a minimal characteristic-two outside subgroup, the proved source model
sieve leaves the binary projective groups of degrees three, four and five.
Degree five descends to a smaller outside subgroup. For degrees three and
four, the actual binary MS inputs satisfy the same earlier C.1.34 contract
used in the rank-one argument. Its five alternatives feed the already proved
source contradictions. This supplies 15.3.13 for the original local data;
the earlier MS classification remains an explicit source obligation.

Source: Aschbacher–Smith 15.3.13–24, printed pp.1125–1130.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo
open ChapterA.Section05To06 RankOneConfiguration.SmallExtension.MarkedMS
open RankTwoElimination.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 15.3.13, retaining only the shared earlier MS classification. -/
theorem source_lemma_15_3_13_of_MS_classifications
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hrank : primeRank 3 d.Yplus = 2) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  intro I hI
  have htwo := ComponentIntersection.rank_two_case_of_three_rank_two d I
    (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany I hI).local_structure hrank
  apply uniform_exclusion_of_binary_exclusions hG d hempty hM hu hmany hI htwo
    (fun J hJ hj hf c e => ?_) (fun J hJ hj hf c e => ?_) I hI
  · exact source_lemma_15_3_23_of_binary_ms hG d hempty hM hu hmany hJ hj hf c e
      (fun b P hRP => binary_ms_alternatives_of_classifications earlier b P hRP)
  · exact source_lemma_15_3_24_four_of_binary_ms hG d hempty hM hu hmany hJ hj hf c e
      (fun _ _ _ b P hRP => binary_ms_alternatives_of_classifications earlier b P hRP)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo
