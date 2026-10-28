module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.TerminalLine

/-!
# Distance two for the complete point-core image

The source-(5.11) point-core bound leaves distances two and four. The
source-(5.12) paired-kernel contradiction excludes four for either moving
cover. Thus the actual characteristic replacement has distance two, with
no assumption on the order of its moved layer and no distance-four input.

Source: MS93 (5.11)--(5.12), printed pp.923--927.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}

/-- The complete point-core image forces distance two for both moving covers. -/
theorem full_point_distance_two_knownSimple
    {d : Replacement L R} (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementDistance h d = 2 := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact hb
  · exact (DistanceFour.Terminal.full_point_distance_four_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hfull).elim

/-- Application to the literal minimum characteristic replacement. -/
theorem original_full_point_distance_two_knownSimple
    (u : Equiv.Perm (Fin 6))
    (hfull : (replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h)) =
        pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementDistance h (replacement h) = 2 :=
  full_point_distance_two_knownSimple u hfull

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
