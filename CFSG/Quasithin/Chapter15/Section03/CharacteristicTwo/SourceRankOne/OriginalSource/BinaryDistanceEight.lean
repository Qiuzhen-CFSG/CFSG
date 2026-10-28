module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryCentralFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier

/-!
# The original binary source31 consumer above critical distance four

The source-specific final calculation now constructs the complete Earlier
record from the actual common facts, b>4 and prescribed replacement. The
included H factor is then an elementary four-group, and the original Sylow,
MS3 and omega-center bound exclude it when the original two-core fixes it.

The two independent remaining source inputs are stated literally: prescribed
replacement on regular critical paths, and the action of the original two-core
on the included factor. Neither universal local control nor a classification
of all core layers is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5.1), pp.890--896;
Aschbacher--Smith C.1.34(4), pp.136--137, and 15.3.31, p.1132.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry.NaturalModule.Recognition
  SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree ChapterC
open BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The literal original source application of the completed final-calculation adapter. -/
theorem source_binary_large_distance_false_of_replacement_and_core_action
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SmallExtension.CentralCover.LinearThree.SL)
    (t : InputSetup (source_binaryMSInput s e))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p)
    (hc : t.reducedCentralFour ≤ centralizer (pCore 2 I : Set I)) : False :=
  source_binary_distance_eight_false_of_fixedFactor_centralizes_core s e t common
    (Source44.SourceEarlier.earlier common hb replacement) hc

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
