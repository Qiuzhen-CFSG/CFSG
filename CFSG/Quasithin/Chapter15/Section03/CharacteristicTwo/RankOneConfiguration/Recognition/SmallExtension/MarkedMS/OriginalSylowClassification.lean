module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Reconstruction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# C.1.32 on actual Sylow small MS pairs

The binary and G2 rows are proved source theorems. In the A6 row, the
quotient center is trivial or cubic. The natural whole-core recognition
handles the first case; the exceptional whole-core reconstruction uses
the actual Sylow witness in the second. All five original conclusions,
including relative blockhood and the full exceptional core, are retained.

The Sylow premise is essential to this source assembly. No classification
of arbitrary nonsylow MS2(a) pairs is asserted.
Source: Aschbacher--Smith C.1.31--32 and MS93 (5.12), Section7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- The exact C.1.32 alternatives for an original small MS pair whose
specified radical is the actual Sylow subgroup of the full join. -/
theorem SmallMSPair.rankTwo_of_original_sylow_knownSimple
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R)) : RankTwoAlternatives L R := by
  rcases h.rankTwo with hb | ha | hg
  · obtain ⟨e⟩ := hb
    exact h.rankTwo_of_binary e
  · obtain ⟨e⟩ := ha
    rcases h.alternating_center_cases e with hz | hz
    · obtain ⟨he,hc,hm⟩ :=
        Natural.Exhaustion.LargeDistance.naturalCore_of_distanceFour_knownSimple
          Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple
          G L R h e hz
      exact h.rankTwo_of_alternatingSix_reconstruction e
        ⟨he,hc,hm.alternating_six_irreducible,Or.inl hm⟩
    · exact Exceptional.OriginalSylow.rankTwo h e hz hSyl
  · obtain ⟨e⟩ := hg
    exact h.rankTwo_g2_knownSimple e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
