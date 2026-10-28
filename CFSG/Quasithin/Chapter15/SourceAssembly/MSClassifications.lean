module
public import CFSG.Quasithin.Chapter15.SourceAssembly.MSRankOne
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo.MSAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.RankTwoBinary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoG2Quotient

/-!
# Theorem E from the shared small MS classifications and 15.1.3

Apply the original rank-two exclusion to each permitted choice of Yplus,
keeping its local groups, orthogonal action and Sylow subgroup unchanged.
Together with the proved rank-one source assembly this discharges both
15.3.13 and 15.3.25 from the same earlier C.1.32/C.1.34 input. Only that
shared earlier classification and the separate 15.1.3 source branch remain.

The binary C.1.32 row is proved for the actual small MS pair and original
source marking. The G₂ row has its literal central-cover quotient and
projection comparison. These partial branches are re-exported here; the
A₆/G₂ whole-core reconstruction and full C.1.34 classification remain
necessary to construct the shared earlier-classification input below.

Source: Aschbacher–Smith 15.3.13–32 and the final proof of Theorem E,
printed pp.1125–1134 and 1165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The final E consumer with both characteristic-two source exclusions supplied. -/
theorem source_theoremE_of_MS_classifications
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M))) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_MS_rank_one earlier hG T hmany hempty h1513
  intro d hd hM hu Yplus hchoice hrank
  let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
  have he : MainForward.faithfulLocalComponents d.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard := hd ▸ hmany
  exact CharacteristicTwo.SourceRankTwo.source_lemma_15_3_13_of_MS_classifications
    earlier hG d' he hM hu hn hrank

end CFSG.Quasithin.Chapter15
