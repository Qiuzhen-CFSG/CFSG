module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationCompatible
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The compatible small-critical order-sixteen contradiction

Two overlapping small critical paths retain their actual backward transporter,
common edge mover and strict Baumann slice. Under the two compatible triple-seed
centrality conclusions, failure of kernel normalization forces X = Z. The common
mover then puts the whole neighboring core movement in the middle seed. The
normalization bridge and the full-cover strict-slice obstruction give False.

This is the actual consumer of the compatible selections in MS93 (5.12)(1)
and (3), printed pp.924--927. The two triple centrality hypotheses retain the
precise source compatibility obligation; a common fixed-space equality alone
does not supply them. Both moving covers and all central attachments remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
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
/-- The literal compatible order-sixteen backward selection contradicts a
strict slice once both overlapping critical images are small. -/
theorem sixteen_equal_compatible_strict_false_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq1 : q.walk.getVert 1 = t) (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hbackward : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hbad
    have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
      rw [←hq2,q.dist_start (by omega)]
    have hXgen := (small_backward_kernel_normalized_or_centrally_generated s hc hb p hsmall
      q.start_color hca).resolve_left hbad
    have hX := SylowPairedFixer.central_generation_eq_seed (h := h) p.start_color hat
      (hXgen a p.start_color)
    have hcontrol := SixteenEqual.sixteen_equal_mover_omega_control_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat hct hequal hX
    have hQJ := (SixteenUnequal.sixteen_edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat).1
    have hmove : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a :=
      (commutator_mono le_rfl hQJ).trans
        (hcontrol.2.trans (hcontrol.1.le.trans inf_le_left))
    exact hbad (small_backward_kernel_normalized_of_triple_central s hc hb p hsmall q hq2 hqsmall
      hmove g hg hgc hforward hbackward)
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
    (by simpa only [hq1,hq2] using hgen) (by simpa only [hq2] using hstrict)
    (by simpa only [hq2] using hnorm) hfix

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
