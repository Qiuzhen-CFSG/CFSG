module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.RadiusReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage.Boundary

/-!
# The distance-eight radius boundary from endpoint control

The actor in the small-displacement calculation is retained as a Z-layer
exactly b-2 steps from the radius center. If an individual displacement were
not in the fixed core, that actor would force escape of the local span.
Critical-prefix control therefore supplies the covering clause. The natural
summand has order eight, whereas the displacement has order at most four,
so such coverage is impossible.

A residual turn then fixes the displacement and moves its Z-layer to the
next vertex, giving the boundary normalization required by the large-image
reduction. No local control on arbitrary ordered pairs is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.5), printed pp.894--895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.RadiusBoundary
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open PathCentrality.FinalCalculation PathCentrality.FinalCalculation.RadiusImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem small_not_cover_natural
    (common : CommonFacts R source geometry) {c : Vertex R} (hc : color R c = false)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4) :
    ¬ Z R c ≤ K ⊔ fixedCore R c := by
  let S := stabilizer R c
  let D := (fixedCore R c).subgroupOf S
  let U₀ := (U R c).subgroupOf S
  let K₀ := K.subgroupOf S
  let := finite_stabilizer R c
  let : D.Normal := fixedCore_normal R c
  have hUS : U R c ≤ S := (MS93.U_le_Z _).trans (Z_le_stabilizer R c)
  have hDS : fixedCore R c ≤ S := fun _ hx => hx.1.1
  have hUD : U₀ ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    exact (Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc).le
      ⟨hx.1, hx.2.2⟩
  have hUcard : Nat.card U₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv).trans
      (common.natural.card_at c hc)
  have hKcard : Nat.card K₀ ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv]
    exact hcard
  have hindex : D.relIndex U₀ = 8 := by
    rw [← inf_relIndex_left, hUD, relIndex_bot_left, hUcard]
  intro h
  have hle : U₀ ≤ K₀ ⊔ D := by
    rw [← subgroupOf_sup hK hDS]
    exact comap_mono ((MS93.U_le_Z _).trans h)
  have hh := relIndex_le_of_le_right hle
    (show D.relIndex (K₀ ⊔ D) ≠ 0 from index_ne_zero_of_finite)
  rw [hindex, relIndex_sup_right] at hh
  have hsmall := Nat.le_of_dvd (show 0 < Nat.card K₀ from Nat.card_pos)
    (relIndex_dvd_card D K₀)
  omega

private theorem small_radius_displacement_le_fixed
    (common : CommonFacts R source geometry) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (hb : 4 < geometry.b R)
    {c f : Vertex R} (hc : color R c = false) (hf : color R f = false)
    (hcf : (cosetGraph R).dist c f + 2 = geometry.b R)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c) (hAZ : A ≤ Z R f)
    (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ ≤ fixedCore R c := by
  have hQn : Q R c ≤ normalizer (fixedCore R c : Set (FreeAmalgam R)) :=
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)
  suffices hV : V R c ≤ commutatorPreimage (Q R c) A (fixedCore R c) from
    (commutator_mono hV le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQn)
  apply (V_le_iff R hc _).mpr
  intro d hd hdist
  have hdQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    exact lt_of_le_of_lt hdist common.large_distance
  apply le_commutatorPreimage hdQ
  by_cases hdc : d = c
  · subst d
    exact (commutator_mono le_rfl hA).trans_eq (geometry.centralizes c hc) |>.trans bot_le
  have hdist2 : (cosetGraph R).dist d c = 2 := by
    have hpos := (cosetGraph_connected R).pos_dist_of_ne hdc
    have hnot1 : (cosetGraph R).dist d c ≠ 1 := by
      intro h1
      have hadj := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact adjacent_color_ne R hadj (hd.trans hc.symm)
    omega
  by_cases hinit : ⁅Z R d, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl hA).trans hinit
  apply commutator_le.mpr
  intro z hz x hx
  have hs : ⁅localZSpan R d c, zpowers x⁆ ≤ fixedCore R c := by
    by_contra hn
    have hh := LocalCommutator.endpoint_covers_Z_of_criticalPrefix hb hprefix
      hd hc hdist2 hf hcf (hA hx) (hAZ hx) hn
    apply small_not_cover_natural common hc hK hcard
    apply hh.trans
    apply sup_le_sup_right
    rw [commutator_comm]
    exact (commutator_mono (localZSpan_le_V R hdist2.le) (zpowers_le.mpr hx)).trans hbound
  exact hs (commutator_mem_commutator (Z_le_localZSpan R d c hz) (mem_zpowers x))


variable {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a)

/-- The small displacement lies in the fixed core at the radius center. -/
theorem displacement_le_radius_fixed (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
    displacement e ≤ fixedCore R (e.walk.getVert (2 + geometry.b R)) := by
  have hc := (e.window 2 (by decide) (by decide)).end_color
  have hA : Z R (e.walk.getVert 4) ≤ Q R (e.walk.getVert (2 + geometry.b R)) := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _
      (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)))
    rw [geometry.distance_constant _
      (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)),
      ExtendedPath.distance e (by omega) (by omega)]
    change 2 + geometry.b R - 4 < geometry.b R
    omega
  have hPS : displacement e ≤ stabilizer R (e.walk.getVert (2 + geometry.b R)) :=
    (displacement_le_radius e hb).trans
      ((geometry.V_le_Q (by omega) _ hc).trans (fun _ hx => hx.1))
  have hPE := displacement_le_forward_edge e hb
  let E := edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)
  have hadj : Adjacent R (e.walk.getVert 4) (e.walk.getVert 5) :=
    (cosetGraph_adj R _ _).mp (e.walk.adj_getVert_succ (e.length_eq ▸ (by omega)))
  have hEcard : Nat.card E ≤ 4 := Escape.EdgeTransfer.edge_displacement_card_le_four
    common.large_distance (moduleFacts common) _ _
    (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)) hadj
  let := finite_stabilizer R (e.walk.getVert 4)
  let : Finite E := Finite.of_injective (inclusion
    ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _
      (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)) hadj).trans
      ((U_le_Z R _).trans (Z_le_stabilizer R _)))) (inclusion_injective _)
  have hcard : Nat.card (displacement e) ≤ 4 := (card_le_of_le hPE).trans hEcard
  have hcf : (cosetGraph R).dist (e.walk.getVert (2 + geometry.b R))
      (e.walk.getVert 4) + 2 = geometry.b R := by
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  have hh := small_radius_displacement_le_fixed common hprefix (by omega) hc
    (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)) hcf hA le_rfl hPS hcard
    (show ⁅V R (e.walk.getVert (2 + geometry.b R)), Z R (e.walk.getVert 4)⁆ ≤
      displacement e by rw [commutator_comm])
  simpa only [commutator_comm] using hh

/-- The full-edge branch is centralized at the boundary b=8. -/
theorem boundaryNormalization (common : CommonFacts R source geometry)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry) : BoundaryNormalization e := by
  intro hb8 _hfour hE
  have hb : 6 < geometry.b R := by omega
  have hE' := RadiusReduction.displacement_eq_later_edge (source := source) e hb hprefix hE
  have hPZ8 : displacement e ≤ Z R (e.walk.getVert 8) := by
    rw [hE']
    apply (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _
      (ExtendedPath.vertex_color e (i := 8) (by decide) (by omega))
      (adjacent_symm R ((cosetGraph_adj R _ _).mp
        (e.walk.adj_getVert_succ (e.length_eq ▸ (by omega : 7 < geometry.b R + 8)))))).trans
      (U_le_Z R _)
  have hPfixed : displacement e ≤ fixedCore R (e.walk.getVert 10) := by
    simpa only [hb8, Nat.reduceAdd] using displacement_le_radius_fixed e common hb hprefix
  obtain ⟨g, hg, ht⟩ := e.turns 10 (by decide) (by decide) (by omega)
  have ht' : act R g⁻¹ (e.walk.getVert 8) = e.walk.getVert 12 := by
    have hh := congrArg (act R g⁻¹) ht
    simpa only [Nat.reduceAdd, Nat.reduceSub, ← act_mul, mul_inv_cancel, act_one] using hh.symm
  have hd : (cosetGraph R).dist (e.walk.getVert 10) (e.walk.getVert 12) = 2 := by
    rw [ExtendedPath.distance e (by decide) (by omega)]
  obtain ⟨l, hl, ht⟩ := exists_residual_turn source
    (ExtendedPath.vertex_color e (i := 10) (by decide) (by omega)) hd
    ((stabilizer R _).inv_mem hg) ht'
  have hPZ12 : displacement e ≤ Z R (e.walk.getVert 12) := by
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hPZ8
    rwa [Iteration.map_eq_self_of_le_fixed hPfixed hl, ← Z_act, ht] at hh
  have hQ : Z R (e.walk.getVert 12) ≤ Q R (e.walk.getVert (8 + geometry.b R)) := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _
      (ExtendedPath.vertex_color e (i := 12) (by decide) (by omega)))
    rw [geometry.distance_constant _
      (ExtendedPath.vertex_color e (i := 12) (by decide) (by omega)),
      ExtendedPath.distance e (by omega) (by omega)]
    change 8 + geometry.b R - 12 < geometry.b R
    omega
  have hC : displacement e ≤ centralizer
      (Z R (e.walk.getVert (8 + geometry.b R)) : Set (FreeAmalgam R)) :=
    (hPZ12.trans hQ).trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes _ (e.window 8 (by decide) (by decide)).end_color)))
  have hN := (le_centralizer_iff.mp hC).trans (Subgroup.centralizer_le_normalizer _)
  simpa only [hE'] using hN

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.RadiusBoundary
