module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.AssemblyFixedLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup

/-!
# Original 15.3.25 from the small MS classifications

The small-branch contradiction uses only the surviving C.1.32/C.1.34 cases
and simplicity of the actual component quotient. Both follow from the small
MS classification and the original local data. The additional B.5 constituent
record is unnecessary for this consumer, so no FF classification is assumed.
The fixed-line identity and paired terminal discharge the middle branch.

Source: Aschbacher–Smith C.1.32/C.1.34 and 15.3.25–32,
printed pp.135–137 and 1130–1134.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension
open SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 15.3.25 with only the two earlier MS classifications remaining. -/
theorem source_lemma_15_3_25_of_MS_classifications
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_not_characteristicTwo_of_branches hG d hempty hM hu hmany hshadow
  · intro I c s hm
    obtain ⟨_, hcases, hsimple⟩ := survivingSmallCases_of_source earlier d s.minimal.1 c
      s.sqtk s.characteristicTwo s.contains s.generated s.normal ⟨s.sylow, s.sylow_eq⟩
      s.characteristic s.facts s.solvableControl s.omega hm
    exact source_small_false_of_MS_cases s hm hcases hsimple
  · intro I c e mark
    exact source_lemma_15_3_32_3 hG d hempty hM hu hmany hshadow
      e.source.minimal e.source.characteristicTwo c mark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
