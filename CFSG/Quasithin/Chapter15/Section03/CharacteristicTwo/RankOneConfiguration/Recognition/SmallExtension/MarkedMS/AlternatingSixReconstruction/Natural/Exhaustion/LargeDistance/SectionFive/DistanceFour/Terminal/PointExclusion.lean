module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointSmallCompatible
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointSmallNormalization

/-!
# Full point-core exclusion at critical distance four

The paired point-core construction supplies a critical path whose full seed
triple is central at the midpoint. The backward failure-line argument excludes
that path. This proves the full point-core branch of MS93 (5.12) for the
original replacement, both moving covers and all central attachments.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12), printed pp.924--927.
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- A full point-core radical image cannot have critical distance four. -/
theorem full_point_distance_four_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) : False := by
  obtain ⟨a, z, p, hcentral⟩ :=
    PointSmallCompatible.full_point_exists_central_critical_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hfull
  exact full_point_forward_triple_false_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull p hcentral

include e hz hn in
/-- The full point-core branch of the natural distance-four exclusion. -/
theorem full_point_distance_ne_four_knownSimple
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) : replacementDistance h d ≠ 4 := by
  intro hb
  exact full_point_distance_four_false_knownSimple (e := e) (hz := hz) (hn := hn) hb u hfull

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
