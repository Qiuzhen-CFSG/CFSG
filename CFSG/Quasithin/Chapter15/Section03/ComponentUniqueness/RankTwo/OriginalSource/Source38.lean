module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.CompleteSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.OriginalSource.Complete

/-!
# The minimal-outside shadow with source38 discharged

The completed rank-two component containment theorem supplies the exact missing premise of the original source35 assembly. The independent original13 exclusion remains explicit for the final Chapter E consumer.
Source: Aschbacher–Smith, 15.3.35–38, printed pp.1135–1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original minimal-outside shadow, with source38 discharged. -/
theorem source_lemma_15_3_35_shadow_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) : SymmetricThreeShadow d.Yplus d.S := by
  apply source_lemma_15_3_35_shadow_of_earlier hG d hempty hM hu hmany h13 hI
  intro htwo L hLI hL hrank
  exact DiagonalOuter.CoverReduction.Assembly.source_lemma_15_3_38_from_selection
    hG d hempty hM hu hmany h13 hI.1 htwo hLI hL hrank

end CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource
