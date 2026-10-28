module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusAction

/-!
# Intermediate noncentrality and the source radius comparison

For two successive paired backward shifts, assume the second critical line
is central at the intervening stabilizer. Its literal transporter fixes it
and carries its critical starting vertex to the original vertex. The line
therefore lies in the original seed and remains noncentral there. Neighbor
transitivity also puts it in the first backward edge seed.

At critical distance six, the opposite end-edge of the second shifted path
is the original first edge. The critical line lies in that seed as well.
The two original edge kernels generate the original stabilizer, a
contradiction. This proves the required intermediate noncentrality for both
R₄ and R₆ at distance six. Applied to the already constructed three-shift
chain and its same-radius action estimates, it forces the actual endpoint
radius index to equal four. Thus the remaining strict-radius theorem will
exclude this distance without another intermediate-centrality premise.

Above distance six, the same transported noncentral line centralizes both
V_(a′−2) and V_a′ intersect Q_(a+2). Both lie in the original first-edge
kernel. The large-actor fixed-space comparison bounds their joined image
by two; radius escape on the reversed shifted path makes the index exactly
two. This is the displayed radius comparison in the centrality assumption
of MS93 (5.11), not the final contradiction for distances above six.

All shifts, end-edge identifications, radii and quotient indices are in the
original minimum characteristic replacement graph. The original radical
need not be Sylow. Both moved covers of orders sixteen and thirty-two and
their full central attachments are retained. The strict radius bound,
greater-than-six noncentrality, Sylow branches and distance-four exclusion
remain with the large-distance assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.11)(2), printed p.924, using the simultaneous choices of (5.6)
and the strict escape of (5.8)--(5.9), pp.917--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

private theorem central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

private theorem central_line_le_neighbor {c v w : Vertex d.radical}
    (hv : Adjacent d.radical c v) (hw : Adjacent d.radical c w)
    (H : Subgroup (FreeAmalgam d.radical))
    (hH : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)))
    (hHv : H ≤ Z d.radical v) : H ≤ Z d.radical w := by
  obtain ⟨g,hg,hgw⟩ := stabilizer_transitive_neighbors d.radical c hv hw
  rw [←hgw,Z_act,←central_fixed_map H (stabilizer d.radical c) hH
    ((stabilizer d.radical c).inv_mem hg)]
  exact map_mono hHv

include e hz hn in
/-- If the second shifted line were central at the intervening vertex, the
literal transporter would put it in the original seed, noncentrally, and
in the first backward edge seed. -/
theorem nonsylow_edge_paired_intermediate_central_transport_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) :
    let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
    H ≤ Z d.radical a ∧ H ≤ Z d.radical q.edge ∧
      ¬ H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
  have hline := nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hns q.path r.toPairedBackwardShift
  have hstart : act d.radical r.transporter a = r.start := by
    have hqa : q.path.walk.getVert 2=a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
    simpa only [hqa] using r.start_eq
  have hfixed : H.map (MulAut.conj r.transporter⁻¹).toMonoidHom = H :=
    central_fixed_map H (stabilizer d.radical q.start) hcentral
      ((stabilizer d.radical q.start).inv_mem r.transporter_mem)
  have hHZ : H ≤ Z d.radical a := by
    have hh : H ≤ Z d.radical r.start :=
      ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    rw [←hstart,Z_act,←hfixed] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj r.transporter⁻¹).injective).mp hh
  refine ⟨hHZ,central_line_le_neighbor r.adjacent_start q.adjacent_shift H hcentral hline.2.1,?_⟩
  intro hHa
  apply hline.2.2.2.2.2
  have hh := (map_mono (f := (MulAut.conj r.transporter⁻¹).toMonoidHom) hHa).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [hfixed] at hh
  change H ≤ centralizer ((stabilizer d.radical a).map
    (MulAut.conj r.transporter⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
  rwa [←stabilizer_act,hstart] at hh

include e hz hn in
/-- At distance six the same critical line is noncentral at the required
intermediate stabilizer, not just at its own critical start. -/
theorem nonsylow_edge_paired_intermediate_noncentral_six_knownSimple
    (hb : replacementDistance h d = 6)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path) :
    ¬ ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  obtain ⟨hHZ,hHedge,hnon⟩ := nonsylow_edge_paired_intermediate_central_transport_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega) hns p q r hcentral
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  let rev : CriticalPath d.radical (replacementGeometry h d)
      (q.path.walk.getVert (q.path.walk.length-2)) r.start :=
    ⟨r.path.end_color,r.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,r.path.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc r.path⟩
  have hlast := cube_critical_commutator_le_first_seed s hc u hR rev
  change ⁅Z d.radical (q.path.walk.getVert (q.path.walk.length-2)),Z d.radical r.start⁆ ≤
    Z d.radical (r.path.walk.reverse.getVert 1) at hlast
  rw [commutator_comm,SimpleGraph.Walk.getVert_reverse] at hlast
  have hlp : p.walk.length=6 := p.length_eq_b.trans hb
  have hlq : q.path.walk.length=6 := q.path.length_eq_b.trans hb
  have hlr : r.path.walk.length=6 := r.path.length_eq_b.trans hb
  have he : r.path.walk.getVert (r.path.walk.length-1)=p.walk.getVert 1 := by
    rw [hlr,show 6-1=3+2 from rfl,r.overlap 3 (by omega),
      show 3=1+2 from rfl,q.overlap 1 (by omega)]
  rw [he] at hlast
  exact hnon ((le_inf hlast hHedge).trans q.edge_seed_intersection_central)

include e hz hn in
/-- Above distance six, intermediate centrality would force the exact
source-(5.11) two-element image of the two indicated radius actors at the
original vertex. The endpoint radius and its next-core intersection are
kept in the same graph and the same join. -/
theorem nonsylow_edge_paired_intermediate_central_radius_index_knownSimple
    (hb : 6 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) :
    (Q d.radical a).relIndex (V d.radical (p.walk.getVert (p.walk.length-2)) ⊔
      (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2))) = 2 := by
  let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
  let z₂ := p.walk.getVert (p.walk.length-2)
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let A := V d.radical z₂ ⊔ (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2))
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨hHZ,hHedge,hnon⟩ := nonsylow_edge_paired_intermediate_central_transport_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p q r hcentral
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hlp : p.walk.length=replacementDistance h d := p.length_eq_b
  have hlq : q.path.walk.length=replacementDistance h d := q.path.length_eq_b
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (by omega)
  have hpt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hVedge : V d.radical z₂ ≤ Q d.radical (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) q.path.end_color
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert,show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph d.radical).dist z₂ (p.walk.getVert 1)+2 < replacementDistance h d
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  have hA : A ≤ Q d.radical (p.walk.getVert 1) :=
    sup_le hVedge (inf_le_right.trans (Q_le_adjacent_h d.radical ht hpt))
  have hHe : H ≤ Z d.radical z₄ :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hd₂ : (cosetGraph d.radical).dist z₂ z₄ = 2 := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) _ = 2
    rw [q.path.dist_end]
    omega
  have hd₀ : (cosetGraph d.radical).dist a' z₂ = 2 := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) _ = 2
    rw [p.dist_end]
    omega
  have hd₄ : (cosetGraph d.radical).dist a' z₄ ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := a') (v := z₂) (w := z₄)
    omega
  have hV₂ : V d.radical z₂ ≤ Q d.radical z₄ := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) q.path.end_color
    change (cosetGraph d.radical).dist z₂ z₄+2 < replacementDistance h d
    omega
  have hV₀ : V d.radical a' ≤ Q d.radical z₄ := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    change (cosetGraph d.radical).dist a' z₄+2 < replacementDistance h d
    omega
  have hHA : H ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z₄ r.path.end_color))).trans
        (centralizer_le (sup_le hV₂ (inf_le_left.trans hV₀)))
  have hupper : (Q d.radical a).relIndex A ≤ 2 := by
    by_contra! hlarge
    exact hnon ((le_inf ((le_inf hHZ hHA).trans
      (cube_edge_large_fixed_le_seed s hc u hR p.start_color hat A hA hlarge)) hHedge).trans
        q.edge_seed_intersection_central)
  let rev : CriticalPath d.radical (replacementGeometry h d) z₂ q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q.path⟩
  have hescape := nonsylow_radius_escape_at_knownSimple (e := e) (hz := hz) (hn := hn)
    hb4 hns rev
  have hqa : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  change ¬ V d.radical z₂ ≤ Q d.radical
    (q.path.walk.reverse.getVert (q.path.walk.reverse.length-2)) at hescape
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show q.path.walk.length-(q.path.walk.length-2)=2 by omega,hqa] at hescape
  have hne : (Q d.radical a).relIndex A ≠ 1 := fun hh =>
    hescape (le_sup_left.trans (relIndex_eq_one.mp hh))
  let := finite_stabilizer d.radical (p.walk.getVert 1)
  let : Finite A := Finite.of_injective
    (inclusion (hA.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hpos : 0 < (Q d.radical a).relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
  change (Q d.radical a).relIndex A=2
  omega

include e hz hn in
/-- In the literal three-shift chain at distance six, both terminal lines
are noncentral at the intervening stabilizers. The existing same-radius
action implications force the opposite radius index to equal four. -/
theorem nonsylow_edge_paired_terminal_six_knownSimple
    (hb : replacementDistance h d = 6)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      ∃ r : EdgePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam d.radical)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z d.radical r.start ⊓
            centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) ∧
          (¬ R₄ ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
          (¬ R₆ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) ∧
          (Q d.radical r.start).relIndex (V d.radical z₄) = 4 := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨q,r,t,hdis,hcard,hplane,hact₄,hact₆⟩ := nonsylow_edge_paired_terminal_radius_actions_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p
  have hn₄ := nonsylow_edge_paired_intermediate_noncentral_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q r
  have hn₆ := nonsylow_edge_paired_intermediate_noncentral_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns q.path r t
  refine ⟨q,r,t,hdis,hcard,hplane,hn₄,hn₆,?_⟩
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  have hi₄ : (Q d.radical q.start).relIndex (V d.radical z₄) ≤ 2 := by
    by_contra! hh
    exact hn₄ (hact₄ hh)
  have hi₆ : (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) ≤ 2 := by
    by_contra! hh
    exact hn₆ (hact₆ hh)
  have hVQ : V d.radical z₄ ≤ Q d.radical z₄ :=
    V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
      (by change 2 < replacementDistance h d; omega)
  let := finite_stabilizer d.radical z₄
  let : Finite (V d.radical z₄) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have htower := relIndex_inf_mul_relIndex (Q d.radical r.start) (Q d.radical q.start) (V d.radical z₄)
  rw [inf_comm (Q d.radical q.start)] at htower
  have hmono : (Q d.radical r.start).relIndex (V d.radical z₄) ≤
      (Q d.radical r.start ⊓ Q d.radical q.start).relIndex (V d.radical z₄) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hupper : (Q d.radical r.start).relIndex (V d.radical z₄) ≤ 4 := by
    rw [←htower] at hmono
    exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
  exact (small_opposite_radius_eq_four_knownSimple (e := e) (hz := hz) (hn := hn)
    (by omega) r.path hupper).2.2

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
