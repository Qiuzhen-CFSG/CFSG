module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalLines
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.PredecessorResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalFixed

/-!
# Backward-kernel normalization with a small opposite slice

The full backward kernel can be normalized without assuming forward
triple-seed centrality when the original path has a small opposite Baumann
slice. A hypothetical failure gives the actual order-two line
[Z_c intersect Q_v, Z_z intersect Q_a]. It lies in the whole-core
commutator of the opposite kernel. The small opposite slice makes that
commutator residual-fixed at v. Its seed placement then makes the failure
line central in the full stabilizer at v.

The retained backward triple centrality fixes the line under the literal
transporter from v to c. Centrality therefore transfers to c, contradicting
noncentrality of a nonzero reverse critical-kernel commutator. Both full-seed
covers and their central attachments are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(1), printed pp.924--925, with the small-slice residual control.
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
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
/-- A small opposite slice and fixedness of the literal kernel-commutator
line normalize the full backward-kernel join. -/
theorem small_backward_kernel_normalized_of_opposite_slice_line_fixed
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hlinefixed : ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),
      Z d.radical z ⊓ Q d.radical a⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_contra hbad
  have hb2 : 2 < replacementDistance h d := by omega
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
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
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
  have hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    hlinefixed
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


include s in
/-- A small opposite slice supplies the forward fixedness needed to
normalize the full backward-kernel join. Only the backward compatible
triple intersection remains explicit. -/
theorem small_backward_kernel_normalized_of_opposite_slice
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hmove : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hbackward : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_cases hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
  · exact hnorm
  apply small_backward_kernel_normalized_of_opposite_slice_line_fixed
    s hc hb p hsmall q hq2 hqsmall g hg hgc hopposite
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by have hl := q.length_eq_b.trans hb; omega)]
  obtain ⟨_,_,hHseeds⟩ := small_backward_kernel_nonnormal_three_seed_line
    s hc hb p hsmall q.start_color hca hnorm
  have hHa : ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),
      Z d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical a :=
    (commutator_mono inf_le_left inf_le_right).trans hmove
  exact (le_inf (le_inf (hHseeds.trans (inf_le_left.trans inf_le_left)) hHa)
    (hHseeds.trans (inf_le_left.trans inf_le_right))).trans hbackward

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
