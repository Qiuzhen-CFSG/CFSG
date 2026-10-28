module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointSmallOpposite

/-!
# Full point-core selection bridge

The full point-core image gives a strict opposite Baumann slice on every
critical path.  Combined with the existing initial selection, this packages
the selected path with both strict slices and exposes the precise contradiction
for any attempted opposite-small branch.  No equality with a whole radius core
is inferred.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The full point-core initial selector can be chosen with both Baumann
slices strict. -/
theorem full_point_initial_selection_all_slices_strict_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d)
        (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 < (B d.radical (p.walk.getVert 2)
        ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical z) := by
  obtain ⟨z, p, hnon, hforward⟩ :=
    DistanceFour.full_point_initial_selection_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hfull
  exact ⟨z, p, hnon, hforward,
    full_point_opposite_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hfull p⟩

include e hz hn in
/-- An opposite-small slice is impossible under the full point-core image.
This is the direct branch eliminator for the full point-core selected route. -/
theorem full_point_selected_opposite_small_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) : False := by
  exact (not_le_of_gt (full_point_opposite_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull p)) hopposite

include e hz hn in
/-- A literal critical path with a small opposite slice forces distance two
in the full point-core branch; the distance-four source alternative is
eliminated by the preceding branch theorem. -/
theorem full_point_distance_two_of_small_opposite_slice_knownSimple
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) :
    replacementDistance h d = 2 := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact hb
  · exact (full_point_selected_opposite_small_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hfull p hopposite).elim

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
