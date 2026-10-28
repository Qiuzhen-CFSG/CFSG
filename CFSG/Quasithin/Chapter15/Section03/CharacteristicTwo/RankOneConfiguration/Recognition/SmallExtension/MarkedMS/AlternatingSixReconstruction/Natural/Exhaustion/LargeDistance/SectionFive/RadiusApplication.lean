module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Application
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusCentrality

/-!
# Full-cover radius control on the original known-simple replacement

The proved source-(3.8) reduction and all-distance central layer discharge
the action and graph-layer premises. The reverse critical actor uses no
point-image assumption. For the radius bounds, the literal canonical radical
image is still required to lie in a conjugate point core; the final Section 5
assembly must handle that premise and the other radical images.

Source: MS93 (5.2)(ii)--(iii), pp.914--915. Final assembly remains with
qt-e-ms-small-a6-exhaustion-large-distance.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R) (hb : 2 < replacementDistance h d)

include e hz hn hb

/-- The reverse critical index on the unchanged replacement and full cover. -/
theorem reverse_critical_image_four_le_knownSimple
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    4 ≤ (Q d.radical a).relIndex (Z d.radical a') :=
  reverse_critical_image_four_le (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d)
    (replacementDistance_pos h d) p hforward

/-- The even actor is in the image under the original canonical projection. -/
theorem critical_even_actor_knownSimple {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ a ∈ ((Z d.radical a').comap (embedM d.radical)).map
        (SourceReduction.projection h e hz hn d),
      orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hactor := exists_even_involution_reverse_critical_image s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d)
    (replacementDistance_pos h d) p hforward
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hactor

/-- The source radius conclusions, retaining only actual point-core containment.
The central cover can have order sixteen or thirty-two. -/
theorem radius_bounds_knownSimple
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (a' c : Vertex d.radical) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅V d.radical a,V d.radical a⁆ ≤ X d.radical a ∧
      ⁅⁅X d.radical a' ⊓ Q d.radical a,V d.radical a ⊓ Q d.radical c⁆,
        V d.radical a ⊓ Q d.radical c⁆ = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  apply radius_bounds_of_two_lt s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) t _ hb ha a' c
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
