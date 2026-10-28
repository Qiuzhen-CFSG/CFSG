module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelOppositeSlice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelEdges

/-!
# The mixed backward failure line and its two transporters

Failure of full backward-kernel normalization gives an order-two line in
the backward, midpoint and endpoint seeds. Mixed radius movement puts it
in the common starting seed. The two strict slices therefore place it in
the selected edge seed and fix it under the starting stabilizer.

The retained holomorph agreement makes the edge transporter preserve any
such fixed line. Together with the local transporter this carries
midpoint centrality to the backward vertex. In particular, a small
opposite Baumann slice forces normalization of the full backward kernel.
No equality of the two relative normalizers is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The local and edge actors preserve a starting-fixed subgroup of the
selected edge kernel, so centrality passes to the backward vertex. -/
theorem MixedBackwardShift.centrality_transfer {a z : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a z}
    (q : MixedBackwardShift (h := h) p) (H : Subgroup (FreeAmalgam d.radical))
    (hHQ : H ≤ Q d.radical q.edge)
    (hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hcentv : H ≤ centralizer
      (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) :
    H ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  have hk : H.map (MulAut.conj q.edgeActor⁻¹).toMonoidHom = H :=
    (Escape.Propagation.Backward.Products.map_conj_eq_of_agree hHQ q.agreement).trans
      (mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hcenta q.original_mem)))
  have hx : H.map (MulAut.conj q.localActor⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcenta ((stabilizer d.radical a).inv_mem q.local_mem)))
  have hh := (map_mono (f := (MulAut.conj q.localActor⁻¹).toMonoidHom) hcentv).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj q.localActor⁻¹).toMonoidHom ≤
    centralizer ((stabilizer d.radical (p.walk.getVert 2)).map
      (MulAut.conj q.localActor⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
  rw [hx,←stabilizer_act] at hh
  have hh' := (map_mono (f := (MulAut.conj q.edgeActor⁻¹).toMonoidHom) hh).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj q.edgeActor⁻¹).toMonoidHom ≤
    centralizer ((stabilizer d.radical (act d.radical q.localActor (p.walk.getVert 2))).map
      (MulAut.conj q.edgeActor⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh'
  rwa [hk,←stabilizer_act,q.start_eq] at hh'

/-- The actual failed-normalization line is fixed at the shared vertex
and lies in the selected edge seed, with its full order and seed placement. -/
theorem mixed_backward_failure_line_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let H := ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
      Z d.radical z ⊓ Q d.radical a⁆
    Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧
      H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      H ≤ Z d.radical q.start ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hqa : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hca : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    simpa only [hqa] using (q.path.dist_start (i := 2) (by omega)).le
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom :=
    hf ▸ map_mono plus_le_D
  let H := ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
    Z d.radical z ⊓ Q d.radical a⁆
  obtain ⟨_,hHcard,hHseeds⟩ := small_backward_kernel_nonnormal_three_seed_line s hc hb p
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
    q.path.start_color hca hbad
  have hZcV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hca)
  have hHa : H ≤ Z d.radical a :=
    (commutator_mono (inf_le_left.trans hZcV) inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb2 u hR a p.start_color)
  have hi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by rwa [q.index_eq]
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have htriple := mixed_strict_compatible_triple_central s hb2 u hf p.start_color
    q.adjacent_start q.adjacent_shift hat hvt hi hstrict q.generation
  have he := mixed_strict_seed_intersection_eq_edge s hb2 u hf p.start_color
    q.adjacent_start q.adjacent_shift hi
  refine ⟨hHcard,?_,?_,hHseeds⟩
  · exact (le_inf hHa (hHseeds.trans (inf_le_left.trans inf_le_left))).trans he.le
  · exact (le_inf (le_inf (hHseeds.trans (inf_le_left.trans inf_le_left)) hHa)
      (hHseeds.trans (inf_le_left.trans inf_le_right))).trans htriple

/-- In the mixed branch a small opposite slice normalizes the full
kernel of the compatible backward seed, with both actors retained. -/
theorem mixed_small_backward_kernel_normalized_of_opposite_slice_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_contra hbad
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let v := p.walk.getVert 2
  let K := Z d.radical q.start ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical a
  let H := ⁅K,F⁆
  obtain ⟨hHcard,hHedge,hcenta,hHseeds⟩ :=
    mixed_backward_failure_line_knownSimple hb u him p q hstrict hbad
  change Nat.card H = 2 at hHcard
  change H ≤ Z d.radical q.edge at hHedge
  change H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) at hcenta
  change H ≤ Z d.radical q.start ⊓ Z d.radical v ⊓ Z d.radical z at hHseeds
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
  have hHQ : H ≤ Q d.radical q.edge := by
    intro x hx
    have hh := hHedge hx
    rw [Z,if_neg (by simp [q.edge_color])] at hh
    exact (mem_omegaCenter_iff.mp hh).1
  have hHc := q.centrality_transfer H hHQ hcenta hcentv
  let qr : CriticalPath d.radical (replacementGeometry h d)
      (p.walk.getVert (p.walk.length-2)) q.start := {
    start_color := q.path.end_color
    walk := q.path.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q.path }
  have hqrsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb qr
  have hpre : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.path.walk.reverse.getVert (q.path.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hFQ : F ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [hl]
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant z p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hFpre : F ≤ Q d.radical (qr.walk.getVert (qr.walk.length-2)) := by
    rw [hpre]
    exact inf_le_right
  have hnon : H ≠ ⊥ := by intro he; rw [he,card_bot] at hHcard; omega
  exact critical_predecessor_kernel_noncentral s hc hb2 qr hqrsmall F hFQ hFpre
    (by simpa only [hl] using hnon) (by simpa only [hl] using hHc)
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
