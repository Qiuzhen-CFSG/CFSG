module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Complete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source

/-!
# C.1.32 for original small MS pairs

The binary, alternating-six and G2 sources are now complete. Their original
rank-two split yields all C.1.32 alternatives, including relative blockhood,
for the specified radical with no additional Sylow hypothesis.
Source: Aschbacher--Smith C.1.31--32; MS93 Main Theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u

/-- The full original C.1.32 classification for a small MS pair. -/
theorem SmallMSPair.rankTwo_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) : RankTwoAlternatives L R := by
  rcases h.rankTwo with hb | ha | hg
  · obtain ⟨e⟩ := hb
    exact h.rankTwo_of_binary e
  · obtain ⟨e⟩ := ha
    exact h.rankTwo_of_alternatingSix_knownSimple e
  · obtain ⟨e⟩ := hg
    exact h.rankTwo_g2_knownSimple e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
