module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelFutureLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalSmallFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The unequal image-eight backward slice with future generation

The literal unequal edge fixes the failure line at the starting vertex.
Future generation and the first backward transporter carry this fixedness to
the critical endpoint. The resulting full-kernel normalization contradicts the
strict selected slice through the existing normalized-actor obstruction.
Both moving covers and the full central attachments remain unchanged.
Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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
/-- Future generation closes the literal unequal image-eight strict backward
slice. No compatibility of the second transporter with the first midpoint is
needed: the first transporter moves the future midpoint back to the start. -/
theorem eight_unequal_small_future_strict_false_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c y : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hne : EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1) ≠
      EightEdgeComparison.edgeMover (d := d) a (q.walk.getVert 1))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (r : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) y)
    (hr2 : r.walk.getVert 2 = z)
    (hfuture : Q d.radical (p.walk.getVert 1) ⊔ Z d.radical y =
      stabilizer d.radical (p.walk.getVert 2))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (hga : act d.radical g z = a) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hbad
    have hline := eight_unequal_small_failure_line_fixed_knownSimple
      s hc hne₀ hcard hb p hsmall q hq2 hqsmall hne hgen hbad
    have hql : q.walk.length = 4 := q.length_eq_b.trans hb
    have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
      rw [←hq2,q.dist_start (by omega)]
    exact hbad (small_backward_kernel_normalized_of_future_line_fixed s hc hb p hsmall
      q.start_color hca r hr2 hfuture g hg hga hline.1)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hmid : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hZzQ : Z d.radical z ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hfix : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ hmid)).trans (centralizer_le hZzQ))
  exact strict_small_normalized_actor_false s hc hb q hqsmall (Z d.radical z)
    (by simpa only [hq2] using hgen) (by simpa only [hq2] using hstrict)
    (by simpa only [hq2] using hnorm) hfix

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
