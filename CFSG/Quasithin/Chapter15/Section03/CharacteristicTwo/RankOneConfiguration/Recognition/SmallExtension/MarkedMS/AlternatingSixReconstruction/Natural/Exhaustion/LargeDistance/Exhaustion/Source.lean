module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Application
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Complete.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Recognition.Source

/-!
# Final natural exhaustion consumer over the distance-four source input

The large-distance source family reduces the original characteristic
replacement to distance two once the independent MS93 (5.12) distance-four
exclusion is supplied.  The existing distance-two branch then supplies the
literal whole-core containment.  This module keeps the distance-four input as
the only unresolved premise and applies the result to the existing natural
recognition consumer.

The replacement is the minimum-order characteristic subgroup of the original
MS2(a) radical; no Sylow, split-cover, point-image, or extra natural-subgroup
hypothesis is introduced here.  Both the order-sixteen and order-thirty-two
moved covers remain in the imported branches.

Source: MS93 (3.6), (5.11)--(5.12), and Section 7, pp.870--872,
923--927, 932--933; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u

/-- The whole-core exhaustion consumer with only the independent
MS93 distance-four exclusion remaining. -/
theorem coreExhaustion_of_distanceFour_knownSimple
    (hfour : SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple) :
    CoreExhaustionInput.{u} KnownSimple.IsKnownSimple :=
  coreExhaustion_of_distance_inputs
    (_root_.CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.largeDistance_knownSimple_of_distanceFour_input hfour)
    DistanceTwo.distanceTwo_knownSimple

/-- The natural-core consumer after the initial natural section and the two
MS93 distance branches have been discharged.  The only explicit source input
is the distance-four exclusion. -/
theorem naturalCore_of_distanceFour_knownSimple
    (hfour : SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple) :
    NaturalCoreInput.{u} KnownSimple.IsKnownSimple :=
  naturalCore_of_initial_and_exhaustion
    _root_.CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.initialRecognition_knownSimple
    (coreExhaustion_of_distanceFour_knownSimple hfour)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
