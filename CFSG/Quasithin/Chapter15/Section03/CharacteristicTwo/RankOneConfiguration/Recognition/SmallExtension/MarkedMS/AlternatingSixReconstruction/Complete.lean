module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.SourceComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion

/-!
# Complete original alternating-six reconstruction

Both original whole-core sources are supplied here. The natural branch uses
its proved distance-four terminal input; the exceptional branch uses the
completed cubic exhaustion. The quotient-center split and unchanged C.1.32
consumer therefore need no remaining core, Sylow, or distance input.
Source: Aschbacher--Smith C.1.31--32; MS93 Main Theorem (2),(6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction
universe u

/-- The complete center-free source, including the original full core. -/
theorem AlternatingSixReconstruction.naturalCore_knownSimple :
    NaturalCoreInput.{u} KnownSimple.IsKnownSimple :=
  Natural.Exhaustion.LargeDistance.naturalCore_of_distanceFour_knownSimple
    Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple

/-- Both actual source branches of alternating-six reconstruction. -/
theorem alternatingSixReconstruction_knownSimple :
    AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple :=
  alternatingSixReconstruction_of_core_cases naturalCore_knownSimple
    Exceptional.exceptionalCore_knownSimple

/-- The original marked alternating-six pair satisfies C.1.32. -/
theorem SmallMSPair.rankTwo_of_alternatingSix_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : Exceptional.CentralMarking L) : RankTwoAlternatives L R :=
  h.rankTwo_of_alternatingSix_reconstruction e
    (alternatingSixReconstruction_knownSimple G L R h e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
