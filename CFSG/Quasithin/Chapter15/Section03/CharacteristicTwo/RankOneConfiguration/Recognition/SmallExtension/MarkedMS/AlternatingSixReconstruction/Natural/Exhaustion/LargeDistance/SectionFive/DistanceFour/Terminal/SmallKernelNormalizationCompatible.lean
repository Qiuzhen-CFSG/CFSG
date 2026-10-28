module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalLines
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual

/-!
# Normalization from the two compatible triple-seed intersections

The failure line for a small critical pair lies in the backward, midpoint
and endpoint seeds. A bound on the backward core movement places it in the
remaining starting seed. The two overlapping compatible triple intersections
then make the line central at the two middle component stabilizers.
The same literal transporter sends that centrality to the backward endpoint,
contradicting noncentrality of a nonzero reverse critical-kernel commutator.

The equal image-eight mover application supplies the movement bound from
full omega central generation forced by a normalization failure. The two
triple-centrality premises are the exact remaining source-(5.6)(b) compatible
selection contracts; they are not asserted for arbitrary backward paths.

Source: MS93 (5.12)(1), equal-mover case, printed pp.924--925.
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
/-- Compatible triple-seed centrality transfers
the failure line to the backward endpoint, contradicting the literal reverse
critical-kernel noncentrality. -/
theorem small_backward_kernel_normalized_of_triple_central
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
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hbackward : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
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
  have hHa : H ≤ Z d.radical a :=
    (commutator_mono inf_le_left inf_le_right).trans hmove
  have hcentv := (le_inf (le_inf hHa (hHseeds.trans (inf_le_left.trans inf_le_right)))
    (hHseeds.trans inf_le_right)).trans hforward
  have hcenta := (le_inf (le_inf (hHseeds.trans (inf_le_left.trans inf_le_left)) hHa)
    (hHseeds.trans (inf_le_left.trans inf_le_right))).trans hbackward
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
/-- The equal-mover source branch: compatible triple-seed centrality transfers
the failure line to the backward endpoint, contradicting the literal reverse
critical-kernel noncentrality. -/
theorem small_backward_kernel_normalized_of_equal_triple_central
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : EightEdgeComparison.edgeMover (d := d) c t =
      EightEdgeComparison.edgeMover (d := d) a t)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hbackward : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_cases hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
  · exact hnorm
  have hb2 : 2 < replacementDistance h d := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hgen := (small_backward_kernel_normalized_or_centrally_generated s hc hb p hsmall
    q.start_color hca).resolve_left hnorm
  have hcontrol := EightEqual.equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb2 p.start_color hat hct hequal (hgen a p.start_color)
  have hQJ := (EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb2 p.start_color hat).2.2.1
  have hmove : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a :=
    (commutator_mono le_rfl hQJ).trans
      (hcontrol.2.trans (hcontrol.1.le.trans inf_le_left))
  exact small_backward_kernel_normalized_of_triple_central s hc hb p hsmall q hq2 hqsmall
    hmove g hg hgc hforward hbackward

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
