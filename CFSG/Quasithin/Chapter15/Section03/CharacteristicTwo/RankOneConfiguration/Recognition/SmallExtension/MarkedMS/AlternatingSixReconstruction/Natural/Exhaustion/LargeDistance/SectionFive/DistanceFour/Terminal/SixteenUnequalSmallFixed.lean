module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmallKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelOppositeSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ResidualTerminal

/-!
# Unequal image-sixteen kernels with a small opposite slice

Failure of backward-kernel normalization forces full omega central generation.
The unequal mover then omits the midpoint core, so that mover and the endpoint
seed generate the midpoint residual. The restricted-kernel calculation makes
the failure line residual-fixed.

A small opposite Baumann slice fixes the same line at the forward midpoint.
The original edge and the residual generate the starting stabilizer, so the
line is fixed there too. The full-kernel normalization theorem and the strict
slice obstruction finish this branch, retaining both covers and full seeds.

Source: MS93 (5.5)(c), (5.12)(1), printed pp.915,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The literal unequal mover and endpoint seed fix the failure line under
all of the starting residual. No omega-center placement is assumed. -/
theorem sixteen_unequal_small_failure_line_residual_fixed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical (q.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (q.walk.getVert 1)) 4)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆ ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let t := q.walk.getVert 1
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let H := ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    rw [←hq2]
    exact adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨hXall,_,hHseeds⟩ := small_backward_kernel_nonnormal_three_seed_line
    s hc hb p hsmall q.start_color hca hbad
  have hnot : ¬ Q d.radical a ≤ E := fun hcore =>
    SixteenUnequal.sixteen_unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat hct hne hcore
        (hXall a p.start_color)
  have hres : Ltilde d.radical a ≤ E ⊔ Z d.radical z :=
    (SixteenUnequal.sixteen_opposite_residual_of_core_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat hct
        (Z d.radical z) hgen hnot).2
  have hHE : H ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hh := nonelementary_backward_kernel_mover_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb p q hq2
    rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard q.start_color hct] at hh
    exact hh
  have hHZ : H ≤ Z d.radical z := hHseeds.trans inf_le_right
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  have hHcentral : H ≤ centralizer ((E ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hHE) (le_centralizer_iff.mp
      (hHZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))
  exact hHcentral.trans (centralizer_le hres)

include e hz hn in
/-- The opposite-small image-sixteen unequal branch discharges full-kernel
normalization and contradicts the retained strict backward Baumann slice. -/
theorem sixteen_unequal_small_opposite_strict_false_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical (q.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (q.walk.getVert 1)) 4)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let v := p.walk.getVert 2
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical v) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hbad
    let K := Z d.radical c ⊓ Q d.radical v
    let F := Z d.radical z ⊓ Q d.radical a
    let H := ⁅K,F⁆
    have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
      rw [←hq2,q.dist_start (by omega)]
    obtain ⟨_,_,hHseeds⟩ := small_backward_kernel_nonnormal_three_seed_line
      s hc hb p hsmall q.start_color hca hbad
    have hHX : H ≤ X d.radical v := by
      apply (hHseeds.trans (inf_le_left.trans inf_le_right)).trans
      apply (replacementGeometry h d).omega_bound v hv
      rw [(replacementGeometry h d).distance_constant v hv]
      exact replacementDistance_pos h d
    have hHfixed : H ≤ fixedCore d.radical v := by
      rw [show H = ⁅F,K⁆ from commutator_comm _ _]
      exact (commutator_mono le_rfl inf_le_right).trans
        (small_predecessor_whole_core_fixed s hc hb p hopposite)
    have hcentv := (le_inf hHX hHfixed).trans
      (omega_fixed_central_of_small_critical s hc p hsmall v hv)
    have hres := sixteen_unequal_small_failure_line_residual_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) hcard hb p hsmall q hq2 hne hgen hbad
    have hab : Adjacent d.radical a (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    have hvb : Adjacent d.radical v (p.walk.getVert 1) :=
      adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
        (p.walk.adj_getVert_succ (i := 1) (by omega)))
    have hQbGv : Q d.radical (p.walk.getVert 1) ≤ stabilizer d.radical v :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hvb)
    have hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
      apply le_centralizer_iff.mpr
      rw [←residual_edge_generation (h := h) p.start_color hab]
      exact sup_le (le_centralizer_iff.mp hres)
        (hQbGv.trans (le_centralizer_iff.mp hcentv))
    exact hbad (small_backward_kernel_normalized_of_opposite_slice_line_fixed s hc hb p hsmall
      q hq2 hqsmall g hg hgc hopposite hcenta)
  have hZzQ : Z d.radical z ≤ Q d.radical v := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hfix : ⁅Z d.radical c,Z d.radical v⁆ ≤
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ hv)).trans (centralizer_le hZzQ))
  exact strict_small_normalized_actor_false s hc hb q hqsmall (Z d.radical z)
    (by simpa only [hq2] using hgen) (by simpa only [hq2] using hstrict)
    (by simpa only [hq2] using hnorm) hfix

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
