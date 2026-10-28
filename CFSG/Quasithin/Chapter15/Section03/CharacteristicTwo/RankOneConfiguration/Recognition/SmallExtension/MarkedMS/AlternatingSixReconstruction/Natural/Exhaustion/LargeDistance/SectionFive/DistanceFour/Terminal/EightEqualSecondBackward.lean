module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightSmallOpposite
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalSecondBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The equal second backward step at distance four

Two equal mover intersections identify the literal first and second seed
intersections with the same omega center.  The compatible selector can
therefore use its actual strict neighbor `delta`; the resulting triple
centrality contains the failure line of the second backward kernel.  The
future-path normalization theorem then contradicts the selected strict slice.

Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
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
theorem eight_equal_second_backward_strict_false_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z =
      stabilizer d.radical a)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hequal : EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1) =
      EightEdgeComparison.edgeMover (d := d) a (q.walk.getVert 1))
    {delta : Vertex d.radical}
    (hdelta : Adjacent d.radical delta (q.walk.getVert 1))
    (hequalDelta : EightEdgeComparison.edgeMover (d := d) delta (q.walk.getVert 1) =
      EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1))
    (hstrictDelta : 2 <
      (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical delta)) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hXall := eight_small_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent d.radical c (q.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a (q.walk.getVert 1) := by
    simpa only [hq2] using adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp
        (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hcolA : color d.radical a = false := p.start_color
  have hfirst := eight_equal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2 hcolA hat hct hequal
      hXall hstrict
  have hcolC : color d.radical c = false := q.start_color
  have hsecond := eight_equal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2 hcolC hct hdelta
      hequalDelta hXall hstrictDelta
  have hAc : Z d.radical a ⊓ Z d.radical c ≤ Z d.radical delta := by
    rw [hfirst]
    rw [← hequal, ← hsecond]
    exact inf_le_right
  have hback := eight_equal_compatible_backward_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2
      (EightBaumann.three_duad_mover_knownSimple
        (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2)
      q (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
      hXall hdelta hequalDelta hstrictDelta
  rw [show q.walk.length - 2 = 2 by omega, hq2] at hback
  obtain ⟨k, hk, hct', hbt', heq', htriple, hstrictB, hgenB, r, hr1, hover⟩ := hback
  let b := act d.radical k delta
  have hr2 : r.walk.getVert 2 = c := by
    simpa only [Nat.zero_add, SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
  have htriple' : Z d.radical b ⊓ Z d.radical c ⊓ Z d.radical a ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply htriple
    exact ⟨⟨hAc ⟨hx.2,hx.1.2⟩,hx.1.2⟩,hx.1.1⟩
  have hnorm : Z d.radical (p.walk.getVert 2) ≤ normalizer
      (((Z d.radical b ⊓ Q d.radical a) ⊔ Z d.radical c :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hbad
    have hca : (cosetGraph d.radical).dist b c ≤ 2 := by
      simpa only [hr2] using (r.dist_start (i := 2) (by omega)).le
    have seeds := small_backward_kernel_nonnormal_three_seed_line
      s hc hb q (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
      r.start_color hca
    rw [hq2] at seeds
    have hseeds := (seeds hbad).2.2
    have hmove : ⁅Z d.radical b, Q d.radical c⁆ ≤ Z d.radical c := by
      have hcontrol := EightEqual.equal_mover_omega_control_knownSimple
        (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2
        hcolC hct' hbt' heq' (hXall c hcolC)
      have hQJ := (EightMovers.edge_small_mover_knownSimple
        (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2
        hcolC hct').2.2.1
      exact (commutator_mono le_rfl hQJ).trans
        (hcontrol.2.trans (hcontrol.1.le.trans inf_le_left))
    have hHmove : ⁅Z d.radical b ⊓ Q d.radical a,
        Z d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆ ≤ Z d.radical c :=
      (commutator_mono inf_le_left inf_le_right).trans hmove
    have hline : ⁅Z d.radical b ⊓ Q d.radical a,
        Z d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆ ≤
        centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) :=
      (le_inf (le_inf (hseeds.trans (inf_le_left.trans inf_le_left)) hHmove)
        (hseeds.trans (inf_le_left.trans inf_le_right))).trans htriple'
    have norm := small_backward_kernel_normalized_of_future_line_fixed
      (y := z)
      s hc hb q (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
      r.start_color hca
    rw [hq2] at norm
    exact hbad (norm p rfl hgen g hg hgc hline)
  have hZva : Z d.radical (p.walk.getVert 2) ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).exists_critical (p.walk.getVert 2) q.end_color)
    rw [(replacementGeometry h d).distance_constant _ q.end_color,
      SimpleGraph.dist_comm, p.dist_start (by omega)]
    exact hb2
  have hfix : ⁅Z d.radical b,Z d.radical a⁆ ≤
      centralizer (Z d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a)).trans
      ((commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a hcolA)).trans (centralizer_le hZva))
  exact strict_small_normalized_actor_false s hc hb r
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r)
    (Z d.radical (p.walk.getVert 2))
    (by simpa only [hr1,hr2] using hgenB)
    (by simpa only [hr2] using hstrictB)
    (by simpa only [hr2] using hnorm) hfix

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
