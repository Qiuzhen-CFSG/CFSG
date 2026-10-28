module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PointControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Source

/-!
# The full-cover point estimates on the original alternating-six replacement

Source (3.8) supplies the full symmetric marking, and the all-distance
central-layer theorem identifies the actual graph moving subgroup. These
applications discharge both premises of the critical index, radius commutator,
and nonquadratic edge estimates. Only the displayed point-radical conditions
and, for the radius estimate, the critical index remain.

The final Section 5 exclusion remains with the large-distance owner; none of
these statements assumes a natural subgroup or removes the central line.
Source: MS93 (3.8), (5.2), (5.10)--(5.12), printed pp.877--879,914,922--927.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

/-- The critical commutator package on the original characteristic
replacement, with its full action and central layer both discharged. -/
theorem critical_cover_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    C d.radical a = Q d.radical a ∧
      CriticalPair d.radical a' a ((replacementGeometry h d).exists_critical a' p.end_color) ∧
      ⁅Z d.radical a,Z d.radical a'⁆ ≤ U d.radical a ⊓ U d.radical a' ∧
      ⁅Z d.radical a,Z d.radical a'⁆ ≠ ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact ⟨C_eq_Q s hc a p.start_color, critical_reverse_pair s hc p,
    critical_Z_commutator_le_moving (h := h) p, critical_Z_commutator_ne_bot s hc p⟩

/-- The opposite critical index bound uses the canonical marking and the
proved central layer on the original replacement, including an order-32 cover. -/
theorem critical_opposite_index_le_four_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d)
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) a') :
    (Q d.radical
      (alpha d.radical)).relIndex
        (Z d.radical a') ≤ 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  apply critical_opposite_index_le_four s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) t _ p
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]

/-- Source (5.2)'s point-core radius estimate on the original replacement.
Only the displayed point containment and critical index remain; there is no
natural-subgroup or central-layer premise. -/
theorem critical_radius_commutator_le_Z_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d)
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hcard : 4 ≤ (Q d.radical a').relIndex
      (Z d.radical a)) :
    ⁅V d.radical a ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2)),
      Z d.radical a'⁆ ≤ Z d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  apply critical_radius_commutator_le_Z s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) t _ hb p hcard
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]

/-- The actual full point radical gives a nonzero double commutator on
all original graph edges, including when the moved cover has order thirty-two. -/
theorem edge_double_commutator_ne_bot_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d)
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    {a b : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b) :
    ⁅⁅U d.radical a,Q d.radical b⁆,Q d.radical b⁆ ≠ ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  apply edge_double_commutator_ne_bot s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) t _ ha hab
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
