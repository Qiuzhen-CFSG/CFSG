module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.LocalBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.NaturalFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Transport

/-!
# The large radius-image reduction in MS93 (4.4.5)

The literal image of B = V_(alpha'-2) in G_alpha/Q_alpha has order two or
four. In the order-four case, the earlier critical commutator
R4 = [Z_(alpha-4), Z_(alpha'-4)] lies in D_(alpha-2). A residual turn
puts R4 in the backward edge at alpha, and the marked natural action puts
its B-fixed vectors inside P = [Z_alpha,B]. If P is a proper subgroup of
the forward edge, cardinality forces P = R4. This makes the critical
endpoint normalize the backward edge, contrary to the chosen path.

If P fills the forward edge, a second residual turn identifies it with
the backward edge at alpha+4. For b>8 it centralizes Z_(alpha'+4), again
contradicting the chosen path. Thus a large image forces exactly b=8 and
the two literal edge equalities. The remaining b=8 normalization is kept
as an explicit proof obligation; radius-two containment alone does not
settle the boundary 6+2=b.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the first paragraph of (4.4.5), printed p.894. The earlier
LocalCommutatorControl is retained, with D equal to fixedCore. This module
does not assert the completed first calculation of (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage
open RegularPaths RegularPaths.CommutatorPropagation
open RegularPaths.OrbitEscape.CommutatorContradiction
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a : Vertex R}
  (e : RegularPaths.ExtendedPath geometry a)

/-- The actual source radius B = V_(alpha'-2). -/
noncomputable abbrev radius : Subgroup (FreeAmalgam R) :=
  V R (e.walk.getVert (2 + geometry.b R))
/-- The source displacement P = [Z_alpha,B]. -/
noncomputable abbrev displacement : Subgroup (FreeAmalgam R) :=
  ⁅Z R (e.walk.getVert 4), radius e⁆
/-- The earlier critical commutator R4; index zero is alpha-4. -/
noncomputable abbrev earlierCritical : Subgroup (FreeAmalgam R) :=
  ⁅Z R (e.walk.getVert 0), Z R (e.walk.getVert (geometry.b R))⁆

omit [Finite M] in
private theorem adjacent (i : ℕ) (hi : i < geometry.b R + 8) :
    Adjacent R (e.walk.getVert i) (e.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (e.walk.adj_getVert_succ (e.length_eq ▸ hi))

omit [Finite M] in
private theorem odd_color (i : ℕ) (hi : Even i) (hib : i + 1 < geometry.b R + 8) :
    color R (e.walk.getVert (i + 1)) = true := by
  have hn := adjacent_color_ne R (adjacent e i (by omega))
  have hc := ExtendedPath.vertex_color e hi (by omega)
  cases ht : color R (e.walk.getVert (i + 1)) <;> simp_all

omit [Finite M] in
/-- The radius lies in Q_(alpha+2) by the strict critical-distance bound. -/
theorem radius_le_six_kernel (hb : 6 < geometry.b R) :
    radius e ≤ Q R (e.walk.getVert 6) := by
  apply V_le_Q_of_dist_add_two_lt R (e.window 2 (by decide) (by decide)).end_color
  rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
  omega

/-- Place the literal radius in G_alpha, where the quotient is formed. -/
theorem radius_le_center_stabilizer (hb : 6 < geometry.b R) :
    radius e ≤ stabilizer R (e.walk.getVert 4) :=
  (radius_le_six_kernel e hb).trans (Q_le_stabilizer_of_dist_two R _ _
    (ExtendedPath.vertex_color e (i := 6) (by decide) (by omega))
    (by rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by decide) (by omega)]))

/-- The actual quotient image has order two or four. -/
theorem image_two_or_four (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) :
    (Q R (e.walk.getVert 4)).relIndex (radius e) = 2 ∨
      (Q R (e.walk.getVert 4)).relIndex (radius e) = 4 := by
  let := V_elementary_of_four_lt R (e.window 2 (by decide) (by decide)).end_color (by omega : 4 < geometry.b R)
  let := quotientImage_elementary _ (radius e) (radius_le_center_stabilizer e hb)
  have hsmall := quotientImage_card_le_four source _
    (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)) (radius e)
    (radius_le_center_stabilizer e hb)
  have hdiv := (IsElementaryAbelian.isPGroup 2
    (quotientImage (e.walk.getVert 4) (radius e))).card_eq_or_dvd
  rw [quotientImage_card _ _ (radius_le_center_stabilizer e hb)] at hsmall hdiv
  have hpos := ExtendedPath.two_le_source_image e common
  change 2 ≤ (Q R (e.walk.getVert 4)).relIndex (radius e) at hpos
  omega

/-- The displacement lies in the forward incident edge at alpha. -/
theorem displacement_le_forward_edge (hb : 6 < geometry.b R) :
    displacement e ≤ edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5) := by
  apply commutator_mono le_rfl
  exact (radius_le_six_kernel e hb).trans
    (Q_le_adjacent_h R (odd_color e 4 (by decide) (by omega))
      (adjacent_symm R (adjacent e 5 (by omega))))

omit [Finite M] in
/-- Z_alpha normalizes the terminal radius, so its displacement stays there. -/
theorem displacement_le_radius (hb : 6 < geometry.b R) : displacement e ≤ radius e := by
  have hc := ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)
  have hQ : Z R (e.walk.getVert 4) ≤ Q R (e.walk.getVert (2 + geometry.b R)) := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc, ExtendedPath.distance e (by omega) (by omega)]
    change 2 + geometry.b R - 4 < geometry.b R
    omega
  exact le_normalizer_iff_commutator_le_right.mp
    (hQ.trans ((show Q R (e.walk.getVert (2 + geometry.b R)) ≤ stabilizer R _
      from fun _ hx => hx.1).trans (DistanceEight.V_normalized R _)))

omit [Finite M] in
private theorem backward_span (i : ℕ) (hi : Even i) (hib : i ≤ geometry.b R) :
    Z R (e.walk.getVert i) ≤ localZSpan R (e.walk.getVert (i + 4)) (e.walk.getVert (i + 2)) := by
  obtain ⟨g, hg, ht⟩ := e.turns (i + 2) (hi.add (by decide)) (by omega) (by omega)
  have hh := le_iSup (fun k : stabilizer R (e.walk.getVert (i + 2)) =>
    Z R (act R k (e.walk.getVert (i + 4)))) ⟨g, hg⟩
  have ht' : act R g (e.walk.getVert (i + 4)) = e.walk.getVert i := by
    simpa only [show i + 2 + 2 = i + 4 by omega, Nat.add_sub_cancel] using ht
  simpa only [localZSpan, ht'] using hh

include source in
private theorem forward_residual_turn (i : ℕ) (hi : Even i) (hib : i ≤ geometry.b R) :
    ∃ l ∈ Ltilde R (e.walk.getVert (i + 2)),
      act R l (e.walk.getVert i) = e.walk.getVert (i + 4) ∧
      act R l (e.walk.getVert (i + 1)) = e.walk.getVert (i + 3) := by
  obtain ⟨g, hg, ht⟩ := e.turns (i + 2) (hi.add (by decide)) (by omega) (by omega)
  have ht' : act R g⁻¹ (e.walk.getVert i) = e.walk.getVert (i + 4) := by
    have hh := congrArg (act R g⁻¹) ht
    simpa only [show i + 2 + 2 = i + 4 by omega, Nat.add_sub_cancel,
      ← act_mul, mul_inv_cancel, act_one] using hh.symm
  have hd : (cosetGraph R).dist (e.walk.getVert (i + 2)) (e.walk.getVert (i + 4)) = 2 := by
    rw [ExtendedPath.distance e (by omega) (by omega)]
    omega
  obtain ⟨l, hl, ht⟩ := exists_residual_turn source
    (ExtendedPath.vertex_color e (hi.add (by decide)) (by omega)) hd
    ((stabilizer R _).inv_mem hg) ht'
  refine ⟨l, hl, ht, ?_⟩
  apply Iteration.turn_middle (geometry := geometry) hd
    (adjacent_symm R (by simpa only [show i + 1 + 1 = i + 2 by omega] using adjacent e (i + 1) (by omega)))
    (adjacent_symm R (adjacent e i (by omega)))
    (by simpa only [show i + 2 + 1 = i + 3 by omega] using adjacent e (i + 2) (by omega))
    (by simpa only [show i + 3 + 1 = i + 4 by omega] using adjacent e (i + 3) (by omega))
    (Ltilde_le_stabilizer _ hl) ht

include source in
/-- A residual turn transports an edge containment while fixing K pointwise. -/
theorem transport_containment (i : ℕ) (hi : Even i) (hib : i ≤ geometry.b R)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ fixedCore R (e.walk.getVert (i + 2)))
    (hE : K ≤ edgeCommutator R (e.walk.getVert i) (e.walk.getVert (i + 1))) :
    K ≤ edgeCommutator R (e.walk.getVert (i + 4)) (e.walk.getVert (i + 3)) := by
  obtain ⟨l, hl, ht, hm⟩ := forward_residual_turn (source := source) e i hi hib
  have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hE
  rwa [Iteration.map_eq_self_of_le_fixed hK hl, ← edgeCommutator_act, ht, hm] at hh

include source in
/-- The same residual turn preserves an exact edge equality. -/
theorem transport_equality (i : ℕ) (hi : Even i) (hib : i ≤ geometry.b R)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ fixedCore R (e.walk.getVert (i + 2)))
    (hE : K = edgeCommutator R (e.walk.getVert i) (e.walk.getVert (i + 1))) :
    K = edgeCommutator R (e.walk.getVert (i + 4)) (e.walk.getVert (i + 3)) := by
  obtain ⟨l, hl, ht, hm⟩ := forward_residual_turn (source := source) e i hi hib
  have hh := congrArg (Subgroup.map (MulAut.conj l⁻¹).toMonoidHom) hE
  rwa [Iteration.map_eq_self_of_le_fixed hK hl, ← edgeCommutator_act, ht, hm] at hh

omit [Finite M] in
/-- Apply (4.4.1)(i) to the earlier critical commutator at alpha-2. -/
theorem earlierCritical_le_fixed (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) :
    earlierCritical e ≤ fixedCore R (e.walk.getVert 2) := by
  have hQ (i : ℕ) (hi : i = 2 ∨ i = 4) :
      Z R (e.walk.getVert (geometry.b R)) ≤ Q R (e.walk.getVert i) := by
    have hv : color R (e.walk.getVert (geometry.b R)) = false := by
      simpa only [Nat.zero_add] using (e.window 0 (by decide) (by decide)).end_color
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hv)
    rw [geometry.distance_constant _ hv, SimpleGraph.dist_comm,
      ExtendedPath.distance e (by rcases hi with rfl | rfl <;> omega) (by omega)]
    change geometry.b R - i < geometry.b R
    rcases hi with rfl | rfl <;> omega
  exact (commutator_mono (backward_span e 0 (by decide) (by omega))
    (le_inf (hQ 4 (Or.inr rfl)) (hQ 2 (Or.inl rfl)))).trans
    (span_kernel_intersection_le_fixed (by omega) hlocal
      (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega))
      (ExtendedPath.vertex_color e (i := 2) (by decide) (by omega))
      (by rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by decide) (by omega)]))

include source in
/-- Transport R4 into the backward edge at alpha. -/
theorem earlierCritical_le_backward_edge (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) :
    earlierCritical e ≤ edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 3) := by
  apply transport_containment (source := source) e 0 (by decide) (by omega)
    (earlierCritical_le_fixed e hb hlocal)
  apply commutator_mono le_rfl
  apply le_trans _ (Q_le_adjacent_h R (odd_color e 0 (by decide) (by omega))
    (adjacent_symm R (adjacent e 1 (by omega))))
  have hv : color R (e.walk.getVert (geometry.b R)) = false := by
    simpa only [Nat.zero_add] using (e.window 0 (by decide) (by decide)).end_color
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hv)
  rw [geometry.distance_constant _ hv, SimpleGraph.dist_comm,
    ExtendedPath.distance e (by omega) (by omega)]
  change geometry.b R - 2 < geometry.b R
  omega

omit [Finite M] in
/-- R4 lies in Z_(alpha'-4), hence in the actual terminal radius. -/
theorem earlierCritical_le_radius (common : CommonFacts R source geometry) :
    earlierCritical e ≤ radius e := by
  have hp := (e.window 0 (by decide) (by decide)).reverse common
  have hZS := hp.endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)
  have hZ : earlierCritical e ≤ Z R (e.walk.getVert (geometry.b R)) := by
    apply le_normalizer_iff_commutator_le_right.mp
    apply le_trans _ (Z_normalized R _)
    simpa only [Nat.zero_add] using hZS
  apply hZ.trans
  apply le_iSup_of_le (e.walk.getVert (geometry.b R))
  apply le_iSup_of_le (show (cosetGraph R).dist (e.walk.getVert (geometry.b R))
    (e.walk.getVert (2 + geometry.b R)) ≤ 2 by
      rw [ExtendedPath.distance e (by omega) (by omega)]; omega)
  exact le_rfl

/-- The marked natural action puts the B-fixed R4 inside [Z_alpha,B]. -/
theorem earlierCritical_le_displacement (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (hfour : (Q R (e.walk.getVert 4)).relIndex (radius e) = 4) :
    earlierCritical e ≤ displacement e := by
  have hU := (earlierCritical_le_backward_edge (source := source) e hb hlocal).trans
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (RegularPaths.moduleFacts common) _ _
      (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega))
      (adjacent_symm R (adjacent e 3 (by omega))))
  let := V_elementary_of_four_lt R (e.window 2 (by decide) (by decide)).end_color (by omega : 4 < geometry.b R)
  have hC := (earlierCritical_le_radius e common).trans
    (le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R
      (e.window 2 (by decide) (by decide)).end_color (by omega : 4 < geometry.b R)))
  obtain ⟨model⟩ := localModel_nonempty source (RegularPaths.moduleFacts common)
    (e.walk.getVert 4) (ExtendedPath.vertex_color e (i := 4) (by decide) (by omega))
  exact (le_inf hU hC).trans
    (natural_fixed_le_commutator model (radius e) (radius_le_center_stabilizer e hb) hfour)

omit [Finite M] in
/-- The turn at alpha+2 and (4.4.1)(i) put P in D_(alpha+2). -/
theorem displacement_le_fixed (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) :
    displacement e ≤ fixedCore R (e.walk.getVert 6) := by
  have hQ8 : radius e ≤ Q R (e.walk.getVert 8) := by
    apply V_le_Q_of_dist_add_two_lt R (e.window 2 (by decide) (by decide)).end_color
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  exact (commutator_mono (backward_span e 4 (by decide) (by omega))
    (le_inf hQ8 (radius_le_six_kernel e hb))).trans
    (span_kernel_intersection_le_fixed (by omega) hlocal
      (ExtendedPath.vertex_color e (i := 8) (by decide) (by omega))
      (ExtendedPath.vertex_color e (i := 6) (by decide) (by omega))
      (by rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by decide) (by omega)]))

include source in
/-- A residual turn identifies a full P with the backward edge at alpha+4. -/
theorem displacement_eq_later_edge (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (hE : displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)) :
    displacement e = edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) :=
  transport_equality (source := source) e 4 (by decide) (by omega)
    (displacement_le_fixed e hb hlocal) hE

/-- A proper P is the nonzero R4 line, forcing the forbidden normalization at alpha. -/
theorem false_of_proper_edge (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (hfour : (Q R (e.walk.getVert 4)).relIndex (radius e) = 4)
    (hne : displacement e ≠ edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)) :
    False := by
  let P := displacement e
  let E := edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)
  let C := earlierCritical e
  have hc := ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)
  have hPE : P ≤ E := displacement_le_forward_edge e hb
  have hEU : E ≤ U R (e.walk.getVert 4) :=
    Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (RegularPaths.moduleFacts common) _ _ hc (adjacent e 4 (by omega))
  have hcard : Nat.card E ≤ 4 :=
    Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (RegularPaths.moduleFacts common) _ _ hc (adjacent e 4 (by omega))
  let := finite_stabilizer R (e.walk.getVert 4)
  let : Finite E := Finite.of_injective
    (inclusion (hEU.trans ((U_le_Z R _).trans (Z_le_stabilizer R _)))) (inclusion_injective _)
  let : Finite P := Finite.of_injective (inclusion hPE) (inclusion_injective _)
  have hCP : C ≤ P := earlierCritical_le_displacement e common hb hlocal hfour
  let : Finite C := Finite.of_injective (inclusion hCP) (inclusion_injective _)
  have hCpos : 1 < Nat.card C := by
    apply (one_lt_card_iff_ne_bot C).mpr
    have hh := common.critical_noncommutation _ (e.window 0 (by decide) (by decide)).start_color
      _ (e.window 0 (by decide) (by decide)).critical
    simpa only [Nat.zero_add] using hh
  have hlt : Nat.card P < Nat.card E := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hPE h)
  obtain ⟨k, hk⟩ := card_dvd_of_le hPE
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  have hPsmall : Nat.card P ≤ 2 := by nlinarith
  have hPC : P = C := (eq_of_le_of_card_ge hCP (by omega)).symm
  have hback : P ≤ edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 3) :=
    hPC ▸ earlierCritical_le_backward_edge (source := source) e hb hlocal
  have hZB : Z R (e.walk.getVert (4 + geometry.b R)) ≤ radius e := by
    apply le_iSup_of_le (e.walk.getVert (4 + geometry.b R))
    apply le_iSup_of_le (show (cosetGraph R).dist (e.walk.getVert (4 + geometry.b R))
      (e.walk.getVert (2 + geometry.b R)) ≤ 2 by
        rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]; omega)
    exact le_rfl
  apply e.nonnormalization 4 (by decide) (by decide) (by decide)
  refine le_inf ((e.window 4 (by decide) (by decide)).endpoint_Z_le_start_stabilizer (by omega)) ?_
  apply le_normalizer_iff_commutator_le_left.mpr
  have hEZ : edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 3) ≤ Z R (e.walk.getVert 4) :=
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (RegularPaths.moduleFacts common) _ _ hc (adjacent_symm R (adjacent e 3 (by omega)))).trans (U_le_Z R _)
  exact (commutator_mono hEZ hZB).trans hback

omit [Finite M] in
/-- The radius-two estimate centralizes Z_(alpha'+4) when b is strictly above eight. -/
theorem radius_centralizes_terminal_Z (hb : 8 < geometry.b R) :
    radius e ≤ centralizer (Z R (e.walk.getVert (8 + geometry.b R)) : Set (FreeAmalgam R)) := by
  apply (V_le_iff R (e.window 2 (by decide) (by decide)).end_color _).mpr
  intro d hd hdist
  have hZ : Z R d ≤ Q R (e.walk.getVert (8 + geometry.b R)) := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d (e.walk.getVert (8 + geometry.b R)) < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle (u := d)
      (v := e.walk.getVert (2 + geometry.b R)) (w := e.walk.getVert (8 + geometry.b R))
    rw [ExtendedPath.distance e (by omega) (by omega)] at htri
    omega
  exact hZ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes _ (e.window 8 (by decide) (by decide)).end_color)))

include source in
theorem false_of_full_edge_of_eight_lt
    (hb : 8 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (hE : displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)) :
    False := by
  have hE' := displacement_eq_later_edge (source := source) e (by omega) hlocal hE
  have hC := (displacement_le_radius e (by omega)).trans (radius_centralizes_terminal_Z e hb)
  apply e.nonnormalization 8 (by decide) (by decide) (by decide)
  refine le_inf ((e.window 8 (by decide) (by decide)).endpoint_Z_le_start_stabilizer (by omega)) ?_
  have hN := (le_centralizer_iff.mp hC).trans (Subgroup.centralizer_le_normalizer _)
  simpa only [hE'] using hN

/-- Every remaining large image has b=8 and the two specified edge equalities. -/
theorem large_image_reduction (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (hlarge : ¬ (Q R (e.walk.getVert 4)).relIndex (radius e) ≤ 2) :
    geometry.b R = 8 ∧
      (Q R (e.walk.getVert 4)).relIndex (radius e) = 4 ∧
      displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5) ∧
      displacement e = edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) := by
  have hfour : (Q R (e.walk.getVert 4)).relIndex (radius e) = 4 := by
    rcases image_two_or_four e common hb with h | h
    · exact (hlarge h.le).elim
    · exact h
  have hE : displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5) := by
    by_contra hn
    exact false_of_proper_edge e common hb hlocal hfour hn
  have hbeven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hble : geometry.b R ≤ 8 := by
    by_contra! hn
    exact false_of_full_edge_of_eight_lt (source := source) e hn hlocal hE
  have hb8 : geometry.b R = 8 := by rw [Nat.even_iff] at hbeven; omega
  exact ⟨hb8, hfour, hE, displacement_eq_later_edge (source := source) e hb hlocal hE⟩

/-- The first image estimate is proved for the strict b>8 branch. -/
theorem source_image_le_two_of_eight_lt (common : CommonFacts R source geometry)
    (hb : 8 < geometry.b R) (hlocal : LocalCommutatorControl R) :
    (Q R (e.walk.getVert 4)).relIndex (radius e) ≤ 2 := by
  by_contra hn
  have hh := (large_image_reduction e common (by omega) hlocal hn).1
  omega

/-- The outstanding full-edge boundary calculation. This is a proof target,
not an asserted source theorem. The large-image reduction supplies each
premise. Its proof must retain the source hypotheses and the actual path. -/
@[expose] def BoundaryNormalization : Prop :=
  geometry.b R = 8 →
    (Q R (e.walk.getVert 4)).relIndex (radius e) = 4 →
    displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5) →
    Z R (e.walk.getVert (8 + geometry.b R)) ≤
      normalizer (edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) :
        Set (FreeAmalgam R))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage
