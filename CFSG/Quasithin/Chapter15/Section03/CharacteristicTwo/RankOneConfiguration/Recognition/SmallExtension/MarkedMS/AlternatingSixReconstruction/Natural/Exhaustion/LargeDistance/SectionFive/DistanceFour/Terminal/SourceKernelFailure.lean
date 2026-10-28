module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SourceKernelBridge
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.LargeImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The source failure line on a strict backward selection

A strict backward Baumann slice rules out normalization of the complete
backward-kernel join by the endpoint seed. The source-kernel bridge turns
this into failure of the moving-U/full-X inequality of MS93 (5.12)(1).
Its full failure line has order two, lies in all three actual seeds, and
is contained in the original critical commutator joined with the entire
endpoint center.

The small-image premises are discharged by the proved distance-four
large-image exclusion. Thus the application retains only the original
consecutive critical paths, midpoint identity, literal edge/endpoint
generation, and strict slice. It supplies the source calculation's
failure configuration; the remaining mover argument must still exclude it.
No moving-cover order or central-attachment restriction is imposed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(1), printed pp.924--925. In the small-image case the hatted
endpoint seed in that formula is the full endpoint seed.
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
/-- A literal strict backward selection forces failure of the moving-kernel
bound from the source calculation. Its nonzero failure line is the full-X
commutator, with both central attachments retained. -/
theorem strict_small_backward_source_failure_knownSimple
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    let K := U d.radical c ⊓ Q d.radical (p.walk.getVert 2)
    let H := ⁅K,X d.radical z ⊓ Q d.radical a⁆
    Nat.card (H : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      H ≤ Z d.radical c ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ∧
      H ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
      ¬ ⁅K,Z d.radical z⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔ H := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hpSmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  have hqSmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hZzQ : Z d.radical z ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,
      SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hfix : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ q.end_color)).trans (centralizer_le hZzQ))
  have hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hnorm
    exact strict_small_normalized_actor_false s hc hb q hqSmall (Z d.radical z)
      (by simpa only [hq2] using hgen) (by simpa only [hq2] using hstrict)
      (by simpa only [hq2] using hnorm) hfix
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  obtain ⟨_,hcard,hseeds⟩ := small_backward_kernel_nonnormal_three_seed_line
    s hc hb p hpSmall q.start_color hca hbad
  have he := small_backward_failure_line_eq_source s hc hb p hpSmall q hq2 hbad
  have haligned := (small_backward_kernel_nonnormal_line
    s hc hb p hpSmall q.start_color hca hbad).2.2
  rw [he] at hcard hseeds haligned
  refine ⟨hcard,hseeds,haligned,?_⟩
  intro hsource
  exact hbad (small_backward_kernel_normalized_of_source_bound s hc hb p hpSmall q hq2 hsource)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
