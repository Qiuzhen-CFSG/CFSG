module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SymmetricSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource

/-!
# The concluding MS93 calculation from the actual product estimates

Let K = [Z_(alpha'-4), V_alpha^(4)]. Its order four identifies it with the
backward incident edge at alpha'-4. Its fixed-core bound at alpha'-6 and
the preceding full natural sections then give the symmetric moving-edge
fixation, true local centrality, both source edge indices and the H bound.
If b>8, the additional source equality with the first edge lets a residual
turn transport K to the backward edge at alpha+4. Its support in Z_(alpha'-4)
contradicts the prescribed nonnormalization at alpha+4, giving b=8.

Every product input below is a literal cardinality, fixed-core containment
or conditional first-edge equality. The correct predecessor identity is
proved by ProductSource.terminalProduct_eq_backward_edge_of_card. No witness
of the legacy successor-indexed ProductCalculation is constructed or used.
The old conditional APIs remain available unchanged.

The selected-product owner qt-c01-ms93-conclusion-selected-product must
construct these three estimates from the actual selected critical pairs.
The preceding full natural sections come from the completed (4.4.5) image
and recognition argument. Their final discharge stays with
qt-c01-ms93-final-calculation-conclusion and its PathCentrality parent.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), printed p.895 after (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates
open SymmetricSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Order four identifies the literal product with displacement toward the center. -/
theorem product_eq_displacement (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4) :
    terminalProduct e = ⁅Z R (e.walk.getVert (geometry.b R)),
      Q R (e.walk.getVert (geometry.b R - 2))⁆ := by
  have hd := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hdist : (cosetGraph R).dist (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 2)) = 2 := by
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  let : Finite (U R (e.walk.getVert (geometry.b R))) :=
    Nat.finite_of_card_ne_zero (by rw [common.natural.card_at _ hd]; decide)
  let : Finite (⁅Z R (e.walk.getVert (geometry.b R)),
      Q R (e.walk.getVert (geometry.b R - 2))⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (LocalCommutator.displacement_le_U common hd hdist))
      (inclusion_injective _)
  exact eq_of_le_of_card_ge (commutator_mono le_rfl (actor_le_kernel hb e))
    ((LocalCommutator.displacement_card_le_four common hd hdist).trans_eq hcard.symm)

/-- The two literal product estimates give radius fixation and the order-four lower
bound on H at every M-vertex, with the actual inverse-conjugation action. -/
theorem fixed_and_H_lower (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2))) :
    (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤ fixedCore R c) ∧
      ∀ c, color R c = false → 4 ≤ Nat.card (H R c) := by
  let v := e.walk.getVert (geometry.b R - 2)
  have heven : Even (geometry.b R - 2) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hv : color R v = false := ExtendedPath.vertex_color e heven (by omega)
  obtain ⟨sv⟩ := sections v hv
  have hdis : ⁅Z R (e.walk.getVert (geometry.b R)), Q R v⁆ ≤ fixedCore R v := by
    rw [← product_eq_displacement common hb e hcard]
    exact hKfixed
  have hfixed : ⁅V R v, Q R v⁆ ≤ fixedCore R v :=
    radius_fixed_of_moving common hv sv (opposite_moving common hb e) hdis
  let := finite_stabilizer R v
  let : Finite (H R v) := Finite.of_injective
    (inclusion (((H_le_commutator R v).trans hfixed).trans
      (inf_le_left.trans (show Q R v ≤ stabilizer R v from fun _ hx => hx.1))))
    (inclusion_injective _)
  have hHcard : 4 ≤ Nat.card (H R v) := by
    simpa only [hcard] using card_le_of_le (product_le_H common hb e)
  constructor
  · intro c hc
    obtain ⟨u, hu⟩ := exists_mVertex_of_color R hv
    obtain ⟨w, hw⟩ := exists_mVertex_of_color R hc
    let g := u⁻¹ * w
    have hg : act R g v = c := by rw [hu, act_mVertex, mul_inv_cancel_left, ← hw]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfixed
    rwa [map_commutator, ← V_act, ← Q_act, ← Escape.EdgeTransfer.fixedCore_act, hg] at hh
  · intro c hc
    rwa [Escape.Initial.H_card_eq_base v hv, ← Escape.Initial.H_card_eq_base c hc] at hHcard

/-- Every moving incident edge equals H at its center: natural-section
generation supplies containment and the two order bounds force equality. -/
theorem moving_edge_eq_H (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)))
    {c t d : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) (hdt : Adjacent R d t)
    (hd : d ∈ Escape.movingNeighbors geometry c) : edgeCommutator R d t = H R c := by
  obtain ⟨hfixed, hlower⟩ := fixed_and_H_lower common hb sections e hcard hKfixed
  have hdc := Escape.EdgeTransfer.neighbor_color c t d hc hct hdt
  have hZV : Z R d ≤ V R c := le_iSup_of_le d
    (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd.1]) le_rfl)
  obtain ⟨s⟩ := sections c hc
  have hHC := H_le_moving_displacement common hc s hd
    ((commutator_mono hZV le_rfl).trans (hfixed c hc))
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    cases h : color R t <;> simp_all
  have hHE : H R c ≤ edgeCommutator R d t := hHC.trans
    (commutator_mono le_rfl (Q_le_adjacent_h R ht hct))
  let : Finite (U R d) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at d hdc]; decide)
  let : Finite (edgeCommutator R d t) := Finite.of_injective
    (inclusion (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) d t hdc hdt)) (inclusion_injective _)
  exact (eq_of_le_of_card_ge hHE
    ((Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (LocalCommutator.moduleFacts common) d t hdc hdt).trans (hlower c hc))).symm

/-- The symmetric assertion on p.895, from the two independent literal
product estimates and the preceding full natural sections. -/
theorem movingEdgeFixed (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2))) :
    MovingEdgeFixed geometry := by
  intro c t d hc hct hdt hd
  rw [moving_edge_eq_H common hb sections e hcard hKfixed hc hct hdt hd]
  exact (H_le_commutator R c).trans
    ((fixed_and_H_lower common hb sections e hcard hKfixed).1 c hc)

/-- Apply the existing (4.2)(i) and (iii) transfers to obtain centrality in
the whole stabilizer. The two product estimates remain with final source assembly. -/
theorem local_centrality (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)))
    {c : Vertex R} (hc : color R c = false) :
    ⁅V R c, Q R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype :=
  centrality_at_all common (movingEdgeFixed common hb sections e hcard hKfixed) sections e hc

/-- The numerical fixed-factor bound at every M-vertex, with source centrality
and moving-span generation derived from the same two product estimates. -/
theorem H_card_le_four (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)))
    {c : Vertex R} (hc : color R c = false) : Nat.card (H R c) ≤ 4 := by
  have ha := ExtendedPath.center_color e
  obtain ⟨sa⟩ := sections a ha
  have h := Conclusion.H_card_le_four common
    (movingEdgeFixed common hb sections e hcard hKfixed) e sa
  rwa [Escape.Initial.H_card_eq_base a ha, ← Escape.Initial.H_card_eq_base c hc] at h

omit [Finite M] in
private theorem predecessor_adjacent (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
  have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
  simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h

/-- The final source contradiction for b>8. A residual turn transports the
fixed plane from alpha to alpha+4, while its correct predecessor-edge description puts
it in Z_(alpha'-4). Distance eight then makes it centralize Z_(alpha'+4),
contradicting the retained nonnormalization at alpha+4. -/
theorem distance_eq_eight (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)))
    (hfirstEdge : 8 < geometry.b R →
      terminalProduct e = edgeCommutator R a (e.walk.getVert 5)) : geometry.b R = 8 := by
  have hfixed := movingEdgeFixed common hb sections e hcard hKfixed
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  rw [Nat.even_iff] at heven
  suffices hle : geometry.b R ≤ 8 by omega
  by_contra! hlarge
  let K := terminalProduct e
  have hfirst : K = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5) := by
    simpa only [e.center_eq] using hfirstEdge hlarge
  have hKfixed : K ≤ fixedCore R (e.walk.getVert 6) := by
    rw [hfirst]
    exact hfixed _ _ _ (ExtendedPath.vertex_color e (by decide) (by omega))
      (adjacent_symm R (path_adjacent e 5 (by omega))) (path_adjacent e 4 (by omega))
      (marked_moving common e (i := 4) (by decide) (by decide))
  obtain ⟨g, hg, ht⟩ := e.turns 6 (by decide) (by decide) (by omega)
  have ht' : act R g⁻¹ (e.walk.getVert 4) = e.walk.getVert 8 := by
    have hh := congrArg (act R g⁻¹) ht
    simpa only [Nat.reduceAdd, Nat.reduceSub, ← act_mul, mul_inv_cancel, act_one] using hh.symm
  have heq : K = edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) :=
    RegularPaths.CommutatorPropagation.Iteration.transport_edge_of_fixed
      (geometry := geometry) source
      (ExtendedPath.vertex_color e (by decide) (by omega))
      (show (cosetGraph R).dist (e.walk.getVert 6) (e.walk.getVert 8) = 2 from
        ExtendedPath.distance e (by decide) (by omega))
      (adjacent_symm R (path_adjacent e 5 (by omega)))
      (adjacent_symm R (path_adjacent e 4 (by omega)))
      (path_adjacent e 6 (by omega)) (path_adjacent e 7 (by omega))
      ((stabilizer R _).inv_mem hg) ht' hfirst hKfixed
  have hsupport : K ≤ Z R (e.walk.getVert (geometry.b R)) := by
    rw [show K = _ from ProductSource.terminalProduct_eq_backward_edge_of_card common hb e hcard]
    exact (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) _ _
      (ExtendedPath.vertex_color e (i := geometry.b R) (geometry.even (alpha R) rfl) (by omega))
      (predecessor_adjacent hb e)).trans (U_le_Z R _)
  have hZQ : Z R (e.walk.getVert (geometry.b R)) ≤ Q R (e.walk.getVert (8 + geometry.b R)) := by
    have hc := ExtendedPath.vertex_color e (i := geometry.b R) (geometry.even (alpha R) rfl) (by omega)
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc, ExtendedPath.distance e (by omega) (by omega)]
    change 8 + geometry.b R - geometry.b R < geometry.b R
    omega
  have hcentral : K ≤ centralizer
      (Z R (e.walk.getVert (8 + geometry.b R)) : Set (FreeAmalgam R)) :=
    (hsupport.trans hZQ).trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes _ (e.window 8 (by decide) (by decide)).end_color)))
  apply e.nonnormalization 8 (by decide) (by decide) (by decide)
  apply le_inf ((e.window 8 (by decide) (by decide)).endpoint_Z_le_start_stabilizer (by omega))
  have hn := (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  simpa only [heq] using hn

/-- The actual final (4.4) consumer, using only the selected product's three
source estimates and the preceding full natural sections. The predecessor
edge supplies the order-four witness for both literal edge-index formulas. -/
theorem conclusions
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)))
    (hfirstEdge : 8 < geometry.b R →
      terminalProduct e = edgeCommutator R a (e.walk.getVert 5)) :
    geometry.b R = 8 ∧
      (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤
        (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
      (∀ c t, color R c = false → Adjacent R c t →
        (Z R t).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R t) = 4) := by
  have hfixed := movingEdgeFixed common hb sections e hcard hKfixed
  refine ⟨distance_eq_eight common hb sections e hcard hKfixed hfirstEdge,
    fun _ hc => centrality_at_all common hfixed sections e hc, ?_⟩
  have hc' := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hback := ProductSource.terminalProduct_eq_backward_edge_of_card common hb e hcard
  have hedge : Nat.card (edgeCommutator R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1))) = 4 := by
    rw [← hback]
    exact hcard
  intro c t hc hct
  exact edge_indices common hfixed hc' (predecessor_adjacent hb e) hedge hc hct

/-- The original alpha,beta application, retaining both source indices and
centrality in the actual alpha stabilizer. -/
theorem alpha_beta
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4)
    (hKfixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)))
    (hfirstEdge : 8 < geometry.b R →
      terminalProduct e = edgeCommutator R a (e.walk.getVert 5)) :
    geometry.b R = 8 ∧
      ⁅V R (alpha R), Q R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ∧
      (Z R (beta R)).relIndex (Z R (alpha R)) = 2 ∧
      (Q R (alpha R)).relIndex (Q R (beta R)) = 4 := by
  obtain ⟨hd, hc, hi⟩ := conclusions common hb sections e hcard hKfixed hfirstEdge
  exact ⟨hd, hc _ rfl, hi _ _ rfl (base_adjacent R)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates
