module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Controls
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage.Reduction

/-!
# The source radius-image reduction with critical-prefix control

Each local span used by the large-image reduction has an explicit escape
witness on the actual extended path: the retained turn puts the earlier
critical Z-layer inside that span. Thus the two fixed-core estimates follow
from critical-prefix control, without a statement about arbitrary ordered
pairs. The existing edge transport and natural-action calculation then reduce
an image larger than two to the exact full-edge case at distance eight.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.5), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.RadiusReduction
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
open Escape.Propagation.Backward.Products.Selection.Choices
open PathCentrality.FinalCalculation PathCentrality.FinalCalculation.RadiusImage
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a : Vertex R}
  (e : PathCentrality.RegularPaths.ExtendedPath geometry a)

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
private theorem backward_span (i : ℕ) (hi : Even i) (hib : i ≤ geometry.b R) :
    Z R (e.walk.getVert i) ≤ localZSpan R (e.walk.getVert (i + 4)) (e.walk.getVert (i + 2)) := by
  obtain ⟨g, hg, ht⟩ := e.turns (i + 2) (hi.add (by decide)) (by omega) (by omega)
  have hh := le_iSup (fun k : stabilizer R (e.walk.getVert (i + 2)) =>
    Z R (act R k (e.walk.getVert (i + 4)))) ⟨g, hg⟩
  have ht' : act R g (e.walk.getVert (i + 4)) = e.walk.getVert i := by
    simpa only [show i + 2 + 2 = i + 4 by omega, Nat.add_sub_cancel] using ht
  simpa only [localZSpan, ht'] using hh


omit [Finite M] in
private theorem path_control (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (i : ℕ) (hi : Even i) (hi8 : i ≤ 4) :
    LocalCommutator.LocalControlAt R (e.walk.getVert (i + 4)) (e.walk.getVert (i + 2)) := by
  apply LocalCommutator.localControl_of_spanEscape_of_criticalPrefix (by omega) hprefix
    (ExtendedPath.vertex_color e (hi.add (by decide)) (by omega))
    (ExtendedPath.vertex_color e (hi.add (by decide)) (by omega))
    (by rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]; omega)
  refine ⟨e.walk.getVert (i + geometry.b R), ?_, ?_⟩
  · rw [ExtendedPath.distance e (by omega) (by omega)]
    omega
  · intro h
    exact (e.window i hi (by omega)).critical.2
      ((backward_span e i hi (by omega)).trans h)

omit [Finite M] in
/-- Apply (4.4.1)(i) to the earlier critical commutator at alpha-2. -/
theorem earlierCritical_le_fixed (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
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
    (path_control e hb hprefix 0 (by decide) (by omega)).1

include source in
/-- Transport R4 into the backward edge at alpha. -/
theorem earlierCritical_le_backward_edge (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
    earlierCritical e ≤ edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 3) := by
  apply transport_containment (source := source) e 0 (by decide) (by omega)
    (earlierCritical_le_fixed e hb hprefix)
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


/-- The marked natural action puts the B-fixed R4 inside [Z_alpha,B]. -/
theorem earlierCritical_le_displacement (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (hfour : (Q R (e.walk.getVert 4)).relIndex (radius e) = 4) :
    earlierCritical e ≤ displacement e := by
  have hU := (earlierCritical_le_backward_edge (source := source) e hb hprefix).trans
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
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
    displacement e ≤ fixedCore R (e.walk.getVert 6) := by
  have hQ8 : radius e ≤ Q R (e.walk.getVert 8) := by
    apply V_le_Q_of_dist_add_two_lt R (e.window 2 (by decide) (by decide)).end_color
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  exact (commutator_mono (backward_span e 4 (by decide) (by omega))
    (le_inf hQ8 (radius_le_six_kernel e hb))).trans
    (path_control e hb hprefix 4 (by decide) (by omega)).1

include source in
/-- A residual turn identifies a full P with the backward edge at alpha+4. -/
theorem displacement_eq_later_edge (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (hE : displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)) :
    displacement e = edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) :=
  transport_equality (source := source) e 4 (by decide) (by omega)
    (displacement_le_fixed e hb hprefix) hE

/-- A proper P is the nonzero R4 line, forcing the forbidden normalization at alpha. -/
theorem false_of_proper_edge (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
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
  have hCP : C ≤ P := earlierCritical_le_displacement e common hb hprefix hfour
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
    hPC ▸ earlierCritical_le_backward_edge (source := source) e hb hprefix
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


include source in
theorem false_of_full_edge_of_eight_lt
    (hb : 8 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (hE : displacement e = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5)) :
    False := by
  have hE' := displacement_eq_later_edge (source := source) e (by omega) hprefix hE
  have hC := (displacement_le_radius e (by omega)).trans (radius_centralizes_terminal_Z e hb)
  apply e.nonnormalization 8 (by decide) (by decide) (by decide)
  refine le_inf ((e.window 8 (by decide) (by decide)).endpoint_Z_le_start_stabilizer (by omega)) ?_
  have hN := (le_centralizer_iff.mp hC).trans (Subgroup.centralizer_le_normalizer _)
  simpa only [hE'] using hN

/-- Every remaining large image has b=8 and the two specified edge equalities. -/
theorem large_image_reduction (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
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
    exact false_of_proper_edge e common hb hprefix hfour hn
  have hbeven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hble : geometry.b R ≤ 8 := by
    by_contra! hn
    exact false_of_full_edge_of_eight_lt (source := source) e hn hprefix hE
  have hb8 : geometry.b R = 8 := by rw [Nat.even_iff] at hbeven; omega
  exact ⟨hb8, hfour, hE, displacement_eq_later_edge (source := source) e hb hprefix hE⟩


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.RadiusReduction
