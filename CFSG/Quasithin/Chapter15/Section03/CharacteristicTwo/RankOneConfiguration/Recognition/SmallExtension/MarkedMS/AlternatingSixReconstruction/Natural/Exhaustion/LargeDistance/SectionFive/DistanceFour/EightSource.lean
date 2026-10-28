module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightWholeCore

/-!
# Distance two for a nonelementary radical image of order eight

The source-(5.11) bound leaves distances two and four. The two backward
selections in the source-(5.12) image-eight argument exclude four. Consequently
the literal characteristic replacement has distance two, with both moving
covers and the entire central layer retained. The final application uses the
original minimum characteristic replacement.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.11)--(5.12), printed pp.923--927.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}

/-- A nonelementary radical image of order eight forces distance two, with no
distance-four input or additional choice of path. -/
theorem nonelementary_eight_distance_two_knownSimple
    {d : Replacement L R}
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8) :
    replacementDistance h d = 2 := by
  rcases EightTerminal.distance_two_or_four_knownSimple
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d) with hb | hb
  · exact hb
  · exact (DistanceFour.Terminal.eight_distance_four_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb).elim

/-- Application to the original minimum characteristic replacement. -/
theorem original_nonelementary_eight_distance_two_knownSimple
    (hne : ¬ IsElementaryAbelian 2 ((replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h))))
    (hcard : Nat.card ((replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h))) = 8) :
    replacementDistance h (replacement h) = 2 :=
  nonelementary_eight_distance_two_knownSimple hne hcard

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
