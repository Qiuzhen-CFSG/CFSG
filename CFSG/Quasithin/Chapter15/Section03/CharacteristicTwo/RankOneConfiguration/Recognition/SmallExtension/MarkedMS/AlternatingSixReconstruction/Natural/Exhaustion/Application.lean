module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Source

/-!
# The natural-core consumer of the distance-branch assembly

Apply exhaustion to the existing literal block-module construction. Initial
recognition and both unfinished graph arguments remain explicit. Final
assembly must discharge the latter before claiming the C.1.32 natural row.
Source: Aschbacher--Smith C.1.32(2), pp.135--136, using MS93 Section 7.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion
universe u

/-- The actual whole-core consumer, pending the two source graph arguments. -/
theorem naturalCore_of_distance_inputs {κ : GroupClass.{u}}
    (hi : InitialRecognitionInput κ) (hl : LargeDistanceInput κ)
    (ht : DistanceTwoInput κ) : NaturalCoreInput κ :=
  naturalCore_of_initial_and_exhaustion hi (coreExhaustion_of_distance_inputs hl ht)

end AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
