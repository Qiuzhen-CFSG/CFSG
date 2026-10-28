module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Control

/-!
# Derived critical estimates on the actual characteristic replacement

The original moved cover has order sixteen or thirty-two. In the A₆
image case, elementary Thompson and critical endpoint images are the
unique even offender. Endpoint reciprocity, self-centralization, and
normal generation prove the literal source-(2.3)(c,d) estimates.

The actual application gives distance four, escape and relative midpoint
normality whenever the critical distance exceeds two. The radius-two
contradiction and full symmetric Section5 exclusion remain with final
owner qt-e-ms-small-a6-exhaustion-large-distance; they are not consequences
of declaring or proving the critical-estimate input.

Source: MS93 (2.3), pp.857--859, and (3.8), p.877.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
universe u

/-- The derived critical estimates hold for any supplied group class. -/
theorem estimates {κ : GroupClass.{u}} : EstimatesInput κ := by
  intro G _ _ L R h e hz hn d _ himage
  exact Estimates.criticalEstimates h e hz hn d himage

/-- The original known-simple input, with every critical-estimate premise discharged. -/
theorem estimates_knownSimple : EstimatesInput.{u} KnownSimple.IsKnownSimple := estimates

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
