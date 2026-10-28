module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationOriginalSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalSmallFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelOppositeSlice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.LargeImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightInitialSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual

/-!
# Strict opposite slices in the nonelementary image-eight branch

An actual strict backward selection forces central generation of the full
omega layer. For equal movers, the failure commutator lies in the compatible
backward triple, so a small opposite slice would normalize the full backward
kernel join. The normalized-actor obstruction excludes this possibility.
The unequal-mover fixed-line theorem handles the other case.

Thus every strict forward critical slice has a strict opposite slice, for
both moving covers and all full central attachments of the original graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
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
/-- At distance four, an actual strict backward selection forces central
omega generation at every component vertex in the nonelementary image-eight family. -/
theorem eight_small_omega_centrally_generated_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4) :
    ∀ v : Vertex d.radical, color d.radical v = false →
      X d.radical v = U d.radical v ⊔
        (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) := by
  obtain ⟨z,p,_,hstrict⟩ := EightInitialSelection.initial_selection_all_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq1,hq2,hq3,hout⟩ :=
    eight_strict_backward_large_or_central_generation_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
      hdelta hstrict
  exact hout.resolve_left (not_le_of_gt
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q))

include e hz hn in
/-- A compatible equal-mover backward triple excludes a small opposite slice.
Its full commutator line lies in the triple and hence is fixed by the starting stabilizer. -/
theorem eight_equal_small_opposite_strict_false_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hequal : EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1) =
      EightEdgeComparison.edgeMover (d := d) a (q.walk.getVert 1))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hbackward : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  have hqsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hct : Adjacent d.radical c (q.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a (q.walk.getVert 1) := by
    simpa only [hq2] using adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hXall := eight_small_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb
  have hcontrol := EightEqual.equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb2 p.start_color hat hct hequal (hXall a p.start_color)
  have hQJ := (EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb2 p.start_color hat).2.2.1
  have hmove : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a :=
    (commutator_mono le_rfl hQJ).trans
      (hcontrol.2.trans (hcontrol.1.le.trans inf_le_left))
  have hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hbad
    have hnear : (cosetGraph d.radical).dist c a ≤ 2 := by
      simpa only [hq2] using (q.dist_start (i := 2) (by omega)).le
    have hHseeds := (small_backward_kernel_nonnormal_three_seed_line
      s hc hb p hsmall q.start_color hnear hbad).2.2
    have hHa : ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),
        Z d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical a := by
      exact (commutator_mono (H₁ := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2))
        (H₂ := Z d.radical z ⊓ Q d.radical a)
        (K₁ := Z d.radical c) (K₂ := Q d.radical a)
        inf_le_left inf_le_right).trans hmove
    have hline := (le_inf (le_inf (hHseeds.trans (inf_le_left.trans inf_le_left)) hHa)
      (hHseeds.trans (inf_le_left.trans inf_le_right))).trans hbackward
    exact hbad (small_backward_kernel_normalized_of_opposite_slice_line_fixed
      s hc hb p hsmall q hq2 hqsmall g hg hgc hopposite hline)
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

include e hz hn in
/-- A strict forward slice forces a strict opposite slice in every
nonelementary image-eight configuration. Both mover comparisons are discharged. -/
theorem eight_small_strict_opposite_slice_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  by_contra! hopposite
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  by_cases hequal : EightEdgeComparison.edgeMover (d := d) (p.walk.getVert 2) (p.walk.getVert 1) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (p.walk.getVert 1)
  · have hback := eight_equal_compatible_backward_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb2
      (EightBaumann.three_duad_mover_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard hb2)
      p hsmall (eight_small_omega_centrally_generated_knownSimple
        (e := e) (hz := hz) (hn := hn) hne hcard hb) hdelta hequal hstrict
    rw [show p.walk.length-2=2 by omega] at hback
    obtain ⟨g,hg,hat,hct,heq,htriple,hi,hgen,q,hq1,hover⟩ := hback
    have hq2 : q.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
    have htriple' : Z d.radical (act d.radical g (p.walk.getVert 2)) ⊓
        Z d.radical (alpha d.radical) ⊓
        Z d.radical (p.walk.getVert 2) ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
      intro x hx
      apply htriple
      exact ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩
    exact eight_equal_small_opposite_strict_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p q hq2
      (by simpa only [hq1] using heq) (by simpa only [hq1] using hgen) hi g hg rfl
      htriple' hopposite
  · obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq1,hq2,hq3,_⟩ :=
      eight_strict_backward_kernel_obstruction_knownSimple
        (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hdelta hstrict
    have moverAct (v w : Vertex d.radical) :
        EightEdgeComparison.edgeMover (d := d) (act d.radical g v) (act d.radical g w) =
          (EightEdgeComparison.edgeMover (d := d) v w).map (MulAut.conj g⁻¹).toMonoidHom := by
      dsimp only [EightEdgeComparison.edgeMover]
      rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,U_act,Q_act,Q_act]
    have hEqBase := moverAct (alpha d.radical) (p.walk.getVert 1)
    rw [show act d.radical g (alpha d.radical) = alpha d.radical from hg,hgt] at hEqBase
    have hneq : EightEdgeComparison.edgeMover (d := d)
        (act d.radical g (p.walk.getVert 2)) (q.walk.getVert 1) ≠
        EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (q.walk.getVert 1) := by
      rw [hq1,←hgt,moverAct,hgt,hEqBase]
      intro hh
      exact hequal (Subgroup.map_injective (MulAut.conj g⁻¹).injective hh)
    exact eight_unequal_small_opposite_strict_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall q hq2
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
      hneq (by simpa only [hq1] using hgen) hi g hg rfl hopposite

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
