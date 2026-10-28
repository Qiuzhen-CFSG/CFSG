module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointSmallOpposite
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer

/-!
# A central forward triple excludes the full point-core branch

If a backward kernel join is not normalized, its failure commutator is an
order-two subgroup and all full omega layers are centrally generated.
Fixedness of that actual line by the starting stabilizer places it in the
starting full seed. A central forward triple then fixes it at the midpoint;
the selected conjugator transfers fixedness to the backward endpoint,
contradicting critical-kernel noncentrality.

In the full point-core branch the literal backward selector supplies the
required line fixedness. The strict-slice theorem and elementary radical
bound therefore exclude any critical path with a central forward triple,
retaining both moving covers and every central attachment.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(1),(3), pp.924--927.
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


/-- Fixedness of the actual backward failure line, together with forward
triple centrality, normalizes the full kernel join. No whole-seed commutator
containment in the starting seed is required. -/
theorem small_backward_kernel_normalized_of_forward_triple_and_line_fixed
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
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
    simpa only [hq2] using (q.dist_start (i := 2) (by omega)).le
  obtain ⟨hXall,hHcard,hHseeds⟩ :=
    small_backward_kernel_nonnormal_three_seed_line s hc hb p hsmall q.start_color hca hbad
  change Nat.card H = 2 at hHcard
  change H ≤ Z d.radical c ⊓ Z d.radical v ⊓ Z d.radical z at hHseeds
  have hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    hlinefixed
  have hHQa : H ≤ Q d.radical a := by
    apply (hHseeds.trans (inf_le_left.trans inf_le_left)).trans
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.start_color)
    rw [(replacementGeometry h d).distance_constant c q.start_color]
    exact hca.trans_lt hb2
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  have hHX : H ≤ X d.radical a := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQa hx,
      elemPow_eq_one_of_isElementaryAbelian _ ((hHseeds.trans inf_le_right) hx),
      fun y hy => hcenta hx y hy.1⟩
  have hat : Adjacent d.radical a (q.walk.getVert 1) := by
    simpa only [hq2] using adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hHa : H ≤ Z d.radical a := hHX.trans_eq
    (SylowPairedFixer.central_generation_eq_seed (h := h) p.start_color hat (hXall a p.start_color))
  have hcentv := (le_inf (le_inf hHa (hHseeds.trans (inf_le_left.trans inf_le_right)))
    (hHseeds.trans inf_le_right)).trans hforward
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
/-- A forward compatible triple excludes full point-core distance four. The
literal backward selector fixes the actual failure line and retains its strict slice. -/
theorem full_point_forward_triple_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hforward : Z d.radical (alpha d.radical) ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) : False := by
  have hstrict := (full_point_all_slices_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull p).1
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,g,hg,hgt,q,hq1,hover,hlargeq⟩ :=
    full_point_backward_shift_knownSimple hb2 u hfull p hdelta hstrict
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.start_color
    walk := q.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
    critical := by simpa only [he] using q.critical }
  have hq1' : q'.walk.getVert 1 = t := by
    change (q.walk.copy rfl he).getVert 1 = t
    rwa [SimpleGraph.Walk.getVert_copy]
  have hq2' : q'.walk.getVert 2 = alpha d.radical := by
    change (q.walk.copy rfl he).getVert 2 = _
    rw [SimpleGraph.Walk.getVert_copy]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(full_point_four_critical_indices_two_knownSimple hb u hfull p).1]
    decide
  have hqsmall : (Q d.radical (p.walk.getVert 2)).relIndex
      (Z d.radical (act d.radical g (p.walk.getVert 2))) < 4 := by
    rw [(full_point_four_critical_indices_two_at_knownSimple hb u hfull q').1]
    decide
  have hline := (backward_kernel_attachment s hc hb u hf p q' hat hq1' hq2'
    hgen hlargeq).2.2.1
  have hnorm := small_backward_kernel_normalized_of_forward_triple_and_line_fixed
    s hc hb p hsmall q' hq2' hqsmall g hg rfl hforward hline
  have hel : IsElementaryAbelian 2 (d.radical.map s.projection) := by
    let := pointCore_elementary
    rw [hf]
    exact IsElementaryAbelian.map _
  have hres : Ltilde d.radical (q'.walk.getVert 2) ≤
      Q d.radical (q'.walk.getVert 1) ⊔ Z d.radical z := by
    rw [hq1',hq2',hgen]
    exact Ltilde_le_stabilizer _
  have hi := elementary_small_normalized_slice_le_two s hc hb hel q' hqsmall
    (Z d.radical z) hres (by simpa only [hq2'] using hnorm)
  rw [hq2'] at hi
  exact (not_le_of_gt hlargeq) hi

include e hz hn in
/-- Forward compatible triple centrality excludes the full point-core branch
at every component vertex of the original graph. -/
theorem full_point_forward_triple_false_at_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hforward : Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) : False := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_forward_triple_false_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  apply base (p.act g⁻¹)
  have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hforward).trans
    (map_centralizer_le_centralizer_image _ _)
  have heq : (MulAut.conj (g⁻¹)⁻¹).toMonoidHom = (MulAut.conj g).toMonoidHom := by rw [inv_inv]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←heq,
    ←Z_act,←Z_act,←Z_act,←Subgroup.coe_map,←stabilizer_act] at hh
  simpa only [CriticalPath.act,actWalk_getVert] using hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
