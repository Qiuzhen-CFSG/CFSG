module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Recognition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Source

/-!
# Whole-core assembly after initial alternating-six recognition

The proved initial natural action discharges the recognition premise in the
literal whole-core assembly. The MS93 exhaustion equality remains explicit;
its separate producer must establish it before the unconditional natural-core
conclusion follows.

Source: Aschbacher--Smith C.1.32(2), printed pp.135--136;
Meierfrankenfeld--Stellmacher (1993), (3.2)(vi), (3.6), and Section 7.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural
universe u

/-- The natural whole-core input now requires only the separate exhaustion step. -/
theorem naturalCore_knownSimple_of_exhaustion
    (hx : CoreExhaustionInput.{u} KnownSimple.IsKnownSimple) :
    NaturalCoreInput.{u} KnownSimple.IsKnownSimple :=
  naturalCore_of_initial_and_exhaustion initialRecognition_knownSimple hx

end AlternatingSixReconstruction.Natural
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
