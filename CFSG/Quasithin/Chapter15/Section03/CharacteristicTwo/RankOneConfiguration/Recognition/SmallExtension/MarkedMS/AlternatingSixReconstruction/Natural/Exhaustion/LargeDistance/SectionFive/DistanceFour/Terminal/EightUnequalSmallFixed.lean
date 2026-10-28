module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalSmallAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelOppositeSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer

/-!
# Fixedness of the image-eight unequal failure line

The omitted midpoint core makes the selected edge fix the backward critical
line. Its order-eight permutation action is then abelian, so the edge
normalizes the failure line. That line has order two and is therefore fixed.
The literal edge and endpoint seed generate the midpoint stabilizer, giving
centrality there. Full omega central generation places it in the midpoint seed.

Source: MS93 (5.12)(1), printed p.925.
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

/-- On the literal unequal edge, failure of full-kernel normalization
produces a line fixed by the whole midpoint stabilizer. -/
theorem eight_unequal_small_failure_line_fixed_knownSimple
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hne : EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1) ≠
      EightEdgeComparison.edgeMover (d := d) a (q.walk.getVert 1))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let H := ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆
    H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      H ≤ Z d.radical a := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let t := q.walk.getVert 1
  let T := Q d.radical t
  let K := Z d.radical c ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical a
  let H := ⁅K,F⁆
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    rw [←hq2]
    exact adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  obtain ⟨hXall,hHcard,hHseeds⟩ := small_backward_kernel_nonnormal_three_seed_line
    s hc hb p hsmall q.start_color hca hbad
  change Nat.card H = 2 at hHcard
  change H ≤ Z d.radical c ⊓ Z d.radical v ⊓ Z d.radical z at hHseeds
  have hnot := (eight_unequal_residual_of_central_generation_knownSimple hne₀ hcard hb
    p.start_color hat hct hne (Z d.radical z) hgen (hXall a p.start_color)).1
  have hfix := eight_omitted_midpoint_core_fixes_critical_line_knownSimple hne₀ hcard hb
    q hqsmall (by rwa [hq2])
  have hderived := eight_small_edge_fixed_line_abelian_knownSimple s hc hne₀ hcard hb2 q hqsmall hfix
  have hTGc : T ≤ stabilizer d.radical c := fun _ hx => hx.2 c (adjacent_symm d.radical hct)
  have hTNK : T ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    have hh := le_inf hTGc hfix
    rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc q hqsmall] at hh
    exact hh.trans inf_le_right
  have hQaT : Q d.radical a ≤ T := Q_le_adjacent_h d.radical ht hat
  have hFT : F ≤ T := inf_le_right.trans hQaT
  have hTNH : T ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    dsimp only [H]
    rw [commutator_comm K F]
    exact SylowNormalizer.fixed_mod_central_normalizes F K T (hFT.trans hTNK) hTNK
      ((commutator_mono le_rfl hFT).trans (hderived.trans (centralizer_le inf_le_left)))
  have hTCH : T ≤ centralizer (H : Set (FreeAmalgam d.radical)) :=
    hTNH.trans (normalizer_le_centralizer_of_card_two H hHcard)
  have hHZ : H ≤ Z d.radical z := hHseeds.trans inf_le_right
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  have hcentral : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le hTCH (le_centralizer_iff.mp
      (hHZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))
  refine ⟨hcentral,?_⟩
  have hHQa : H ≤ Q d.radical a := by
    apply (hHseeds.trans (inf_le_left.trans inf_le_left)).trans
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.start_color)
    rw [(replacementGeometry h d).distance_constant c q.start_color]
    exact hca.trans_lt hb2
  have hHX : H ≤ X d.radical a := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQa hx,
      elemPow_eq_one_of_isElementaryAbelian _ (hHZ hx),
      fun y hy => hcentral hx y hy.1⟩
  exact hHX.trans_eq (SylowPairedFixer.central_generation_eq_seed
    (h := h) p.start_color hat (hXall a p.start_color))


include e hz hn in
/-- The opposite-small image-eight branch reaches the strict-slice
contradiction. The literal unequal edge fixes the failure line, which yields
full-kernel normalization; the existing strict obstruction then applies. -/
theorem eight_unequal_small_opposite_strict_false_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
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
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hbad
    have hline := eight_unequal_small_failure_line_fixed_knownSimple s hc hne₀ hcard hb p hsmall
      q hq2 hqsmall hne hgen hbad
    exact hbad (small_backward_kernel_normalized_of_opposite_slice_line_fixed s hc hb p hsmall
      q hq2 hqsmall g hg hgc hopposite hline.1)
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



include e hz hn in
/-- In the unequal image-eight branch, forward triple centrality fixes the
failure line at the midpoint. This supplies the normalization bridge without
a backward triple premise or an opposite-slice bound. -/
theorem eight_unequal_small_normalized_of_forward_line_fixed_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hne : EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1) ≠
      EightEdgeComparison.edgeMover (d := d) a (q.walk.getVert 1))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  exfalso
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hline := eight_unequal_small_failure_line_fixed_knownSimple s hc hne₀ hcard hb p hsmall
    q hq2 hqsmall hne hgen hbad
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let K := Z d.radical c ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical a
  let H := ⁅K,F⁆
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  obtain ⟨_,hHcard,hHseeds⟩ :=
    small_backward_kernel_nonnormal_three_seed_line s hc hb p hsmall q.start_color hca hbad
  change Nat.card H = 2 at hHcard
  change H ≤ Z d.radical c ⊓ Z d.radical v ⊓ Z d.radical z at hHseeds
  have hHa : H ≤ Z d.radical a := hline.2
  have hHI : H ≤ Z d.radical a ⊓ Z d.radical v ⊓ Z d.radical z :=
    le_inf (le_inf hHa (hHseeds.trans (inf_le_left.trans inf_le_right)))
      (hHseeds.trans inf_le_right)
  have hcentv := hHI.trans hforward
  have hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := hline.1
  have hHc : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    rw [←hgc,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcentv).trans
      (map_centralizer_le_centralizer_image _ _)
    have hf : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hcenta ((stabilizer d.radical a).inv_mem hg)))
    rwa [hf] at hh
  let qr : CriticalPath d.radical (replacementGeometry h d) v c := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hqrsmall : (Q d.radical c).relIndex (Z d.radical v) < 4 := by
    rw [(small_critical_indices s hc q hqsmall).2]
    decide
  have hpre : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hFQ : F ≤ Q d.radical v := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant z p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hFpre : F ≤ Q d.radical (qr.walk.getVert (qr.walk.length-2)) := by
    rw [hpre]
    exact inf_le_right
  have hnon : H ≠ ⊥ := by intro he; rw [he,card_bot] at hHcard; omega
  exact critical_predecessor_kernel_noncentral s hc hb2 qr hqrsmall F hFQ hFpre hnon hHc

include e hz hn in
/-- The generic compatible unequal image-eight route closes the strict slice
once the two literal triple-seed centrality premises are available. -/
theorem eight_unequal_small_triple_strict_false_knownSimple
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hmove : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
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
  have hnorm := small_backward_kernel_normalized_of_triple_central s hc hb p hsmall q hq2
    hqsmall hmove g hg hgc hforward hbackward
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


include e hz hn in
/-- The unequal image-eight strict slice needs only the forward compatible
triple centrality. Failure of the full-kernel normalizer is discharged by the
literal abelian edge action and predecessor contradiction. -/
theorem eight_unequal_small_forward_strict_false_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
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
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_cases hh : Z d.radical z ≤ normalizer
        (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
          Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
    · exact hh
    · exact eight_unequal_small_normalized_of_forward_line_fixed_knownSimple
        (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall q hq2 hqsmall hne hgen
        g hg hgc hforward hh
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
