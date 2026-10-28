module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeLargeShift

/-!
# Excluding large critical images in the original nonsylow branch

Above distance four, a critical pair with image at least four selects a
backward critical path through any eligible neighbor of its first edge.
The actual edge radical and old endpoint generate the old stabilizer.
The chosen backward pair must have image two: otherwise its own generating
shift has a critical line central at its previous start by the three-pair
quadratic action, but noncentral there by the old generation equation and
its retained transporter. This argument needs only the first path's
overlap, not a transporter from its prescribed second vertex.

Consequently every moving-cover slice on the first edge has index at most
two. The already proved strict-slice theorem applies to the small critical
path just constructed. Vertex transitivity moves its start to the original
start; neighbor transitivity moves its first edge to the original first
edge. The Baumann subgroup is normalized by that stabilizer, so its strict
index is preserved. This contradicts the bound for that very neighbor and
excludes the large critical image.

The consumers give both critical images and the full commutator order two,
the strict forward slice, and a backward critical path at every original
component vertex without a critical-image premise. Both covers of orders
sixteen and thirty-two, their central attachments, the original nonsylow
radical, and the actual quotient and graph actions are retained.

The new backward-path consumer does not assert edge-plus-endpoint
generation in the remaining small-image branch. Its terminal contradiction,
the original Sylow branch, distance four, and the unconditional replacement
distance-two application remain with this owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.11), printed pp.919--924. The proof uses the controlled
large-image shift, the strict small-image slice, and the two-generator
transport argument on the same natural minimum characteristic replacement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include e hz hn in
private theorem generating_overlap_small
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c
      (p.walk.getVert (p.walk.length-2)))
    (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a)
    (hq2 : q.walk.getVert 2 = a) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4 := by
  by_contra! hlarge
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨r,_,_,_⟩ := nonsylow_large_backward_small_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns q hlarge
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hlenP : p.walk.length = replacementDistance h d := p.length_eq_b
  have hlenQ : q.walk.length = replacementDistance h d := q.length_eq_b
  have hdist1 : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.dist_end]
    omega
  have hdist2 : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := q.walk.getVert (q.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  let H := ⁅Z d.radical r.start,Z d.radical (q.walk.getVert (q.walk.length-2))⁆
  have hHe : H ≤ Z d.radical (q.walk.getVert (q.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hHend : H ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color]
    change (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) a' < replacementDistance h d
    omega
  have hnc := critical_commutator_not_central_at_shift_vertex s hc r.path
    c t a a' (by rw [r.first]; exact r.adjacent_start) hct hgen hHend
    r.transporter r.transporter_mem (by simpa only [hq2] using r.start_eq)
  exact hnc (cube_backward_commutator_central s hc hb2 u hR q r)

include e hz hn in
private theorem large_first_edge_slice_bound
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1)) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≤ 2 := by
  by_cases hel : U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)
  · rw [relIndex_eq_one.mpr hel]
    decide
  obtain ⟨t,_,hgen,g,_,hgt,q,_,hover,hsmall⟩ :=
    nonsylow_large_image_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      (by omega) hns p hlarge hdelta hel
  have hct : Adjacent d.radical (act d.radical g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  exact (hsmall (generating_overlap_small (e := e) (hz := hz) (hn := hn)
    hb hns p q hct hgen hq2)).le

include e hz hn in
private theorem large_critical_image_false_base
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨q,hi,_,_⟩ := nonsylow_large_backward_small_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color d.radical q.path.start_color
  have hbase : act d.radical g⁻¹ q.start = alpha d.radical := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have q₀ := q.path.act g⁻¹
  rw [hbase] at q₀
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ (p.walk.getVert (p.walk.length-2)))).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    have hZ : Z d.radical (alpha d.radical) =
        (Z d.radical q.start).map (MulAut.conj g).toMonoidHom := by
      calc
        Z d.radical (alpha d.radical) = Z d.radical (act d.radical g⁻¹ q.start) :=
          congrArg (Z d.radical) hbase.symm
        _ = _ := by rw [Z_act,inv_inv]
    rw [hZ,Q_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hi]
    decide
  have hstrict := nonsylow_small_forward_slice_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns q₀ hsmall₀
  have hlp : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hlq : 2 < q₀.walk.length := q₀.length_eq_b ▸ hb2
  have hatp : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hatq : Adjacent d.radical (alpha d.radical) (q₀.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q₀.walk.adj_getVert_succ (i := 0) (by omega)
  have hδq : Adjacent d.radical (q₀.walk.getVert 2) (q₀.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q₀.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hatq hatp
  have hδ : Adjacent d.radical (act d.radical x (q₀.walk.getVert 2)) (p.walk.getVert 1) := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hδq
  have hbound := large_first_edge_slice_bound (e := e) (hz := hz) (hn := hn) hb hns p hlarge hδ
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hbound
  omega

include e hz hn in
/-- Large critical images are impossible above distance four for the original
nonsylow radical. The controlled shift accepts every eligible first-edge
neighbor; its small critical image bounds all these slices by two. Transport
of the resulting small path supplies a strict slice on that very edge. -/
theorem nonsylow_large_critical_image_false_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) : False := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_critical_image_false_base (e := e) (hz := hz) (hn := hn)
    hb hns (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  apply base (p.act g⁻¹)
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hlarge

include e hz hn in
/-- Every critical pair above distance four has both critical images and its
full critical commutator of order two in the original nonsylow branch. -/
theorem nonsylow_critical_indices_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
      Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    by_contra! hlarge
    exact nonsylow_large_critical_image_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := small_critical_indices s hc p hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc p hsmall⟩

include e hz hn in
/-- The strict forward-slice conclusion now holds for every critical path
above distance four in the original nonsylow branch. -/
theorem nonsylow_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  apply nonsylow_small_forward_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p
  rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).1]
  decide

include e hz hn in
/-- The source backward-path consumer has its critical-image and strict-slice
premises discharged. It retains the prescribed transporter and every overlap;
no edge-plus-endpoint generation equation is asserted for this path. -/
theorem nonsylow_backward_path_of_four_lt_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g (p.walk.getVert 2))) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1=t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2)=p.walk.getVert i := by
  apply nonsylow_small_backward_path_of_four_lt_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p
  rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).1]
  decide

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
