module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenUnequalSeedCentrality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenUnequalSmallFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer

/-!
# The second unequal failure line lies in the original edge seed

The first backward commutator is central at the original starting vertex.
The aligned second failure line is contained in that commutator times the
central attachment at the forward midpoint. Both groups lie in the original
edge omega center, so the entire failure line lies there. This is the edge
placement in MS93 (5.12)(1), printed p.925; no reverse slice is used.
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
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

include h in
private theorem central_seed_le_edge {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  intro x hx
  have hZX : Z d.radical a ≤ X d.radical a := by
    apply (replacementGeometry h d).omega_bound a ha
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hZX hx.1)
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical ht hat hxQ,hx2,
    fun y hy => hx.2 y (hy.2 a (adjacent_symm d.radical hat))⟩

include e hz hn in
/-- The actual second kernel failure has the original edge placement from
source (5.12)(1), including the full central attachment. -/
theorem sixteen_unequal_second_failure_line_edge_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z c b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hne : edgeMover c (q.walk.getVert 1) ≠ edgeMover a (q.walk.getVert 1))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (r : CriticalPath d.radical (replacementGeometry h d) b a)
    (hr2 : r.walk.getVert 2 = c)
    (hbad : ¬ Z d.radical (p.walk.getVert 2) ≤ normalizer
      (((Z d.radical b ⊓ Q d.radical a) ⊔ Z d.radical c :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical b ⊓ Q d.radical a,
      Z d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆ ≤
      Z d.radical (p.walk.getVert 1) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
  have hbc : (cosetGraph d.radical).dist b c ≤ 2 := by
    rw [←hr2,r.dist_start (by omega)]
  have aligned := small_backward_kernel_nonnormal_line s hc hb q
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
    r.start_color hbc
  rw [hq2] at aligned
  have hbound := (aligned hbad).2.2
  have hab : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvb : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hcentral := sixteen_unequal_backward_commutator_central_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb p q hq2 hne hgen hstrict
  have hlineZ : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ Z d.radical a := by
    have hXZ := SylowPairedFixer.central_generation_eq_seed (h := h)
      p.start_color hab (sixteen_small_omega_centrally_generated_knownSimple
        (e := e) (hz := hz) (hn := hn) hcard hb a p.start_color)
    rw [←hXZ]
    have hqdist : (cosetGraph d.radical).dist c a ≤ 2 := by
      rw [←hq2,q.dist_start (by omega : 2 ≤ q.walk.length)]
    have hcV : Z d.radical c ≤ V d.radical a :=
      le_iSup_of_le c (le_iSup_of_le hqdist le_rfl)
    have hvV : Z d.radical (p.walk.getVert 2) ≤ V d.radical a :=
      le_iSup_of_le (p.walk.getVert 2) (le_iSup_of_le
        (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl)
    exact (commutator_mono hcV hvV).trans
      (radius_bounds_general s hc hb2 p.start_color c (p.walk.getVert 2)).2.1
  apply hbound.trans
  exact sup_le ((le_inf hlineZ hcentral).trans (central_seed_le_edge (h := h) p.start_color hab))
    (central_seed_le_edge (h := h) q.end_color hvb)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

