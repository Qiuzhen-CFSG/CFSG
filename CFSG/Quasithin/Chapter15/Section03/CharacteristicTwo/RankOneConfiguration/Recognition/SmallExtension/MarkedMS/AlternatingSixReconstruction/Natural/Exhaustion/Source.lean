module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Inputs

/-!
# Assembly of the two alternating-six exhaustion branches

The characteristic minimum has positive even critical distance. The
large-distance theorem therefore puts it at distance two. Reconstruction in
that branch bounds its whole graph core by the unchanged initial moved
layer. Pullback through the two specified inclusions exhausts the original
commutator, including any central attachment.

Both distance arguments remain explicit source obligations. This module
does not yet assert unconditional core exhaustion.
Source: MS93 (3.6), Section 5 and Section 7, pp.870--872, 913--927 and932--933.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion
universe u

/-- Discharge exhaustion once the two independent source branches are supplied. -/
theorem coreExhaustion_of_distance_inputs {κ : GroupClass.{u}}
    (hl : LargeDistanceInput κ) (ht : DistanceTwoInput κ) : CoreExhaustionInput κ := by
  intro G _ _ L R h e hz hn
  let d := replacement h
  have hb := replacementDistance_eq_two h d (hl G L R h e hz hn d)
  exact exhaustion_of_graph_core_le h d (ht G L R h e hz hn d hb)

end AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
