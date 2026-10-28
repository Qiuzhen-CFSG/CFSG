module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Distance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball

/-!
# The backward edge in the concluding MS93 product

The source terminal product is [Z_(alpha'-4), V_alpha^(4)]. Each generator
of the radius-four ball is less than b steps from alpha'-5. Hence this
commutator is contained in the actual backward edge U_(alpha'-5)^(alpha'-4).
The earlier natural-module bound puts that edge's order at most four;
therefore order four for the product identifies it with the whole edge.

The turn at alpha'-6 also gives the fixed-core bound directly from
(4.4.1)(i), before the selected pair is constructed.

These bounds do not assume distance eight, centrality or either source index.
The order-four premise in the equality remains to be supplied by the selected
Ri construction. The printed edge is the predecessor, not the successor.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), concluding proof of (4.4), printed p.895 after (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Every generator in the radius-four ball is less than b steps from the
predecessor of alpha'-4, so the whole ball lies in its actual kernel. -/
theorem radius_four_le_predecessor (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    VBall R a 4 ≤ Q R (e.walk.getVert (geometry.b R - 1)) := by
  apply (Escape.Propagation.RadiusFour.Forward.VBall_le_iff (ExtendedPath.center_color e) _).mpr
  intro d hd hda
  apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
  rw [geometry.distance_constant d hd]
  have hdist := ExtendedPath.distance e (i := 4) (j := geometry.b R - 1)
    (by omega) (by omega)
  rw [e.center_eq] at hdist
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a)
    (w := e.walk.getVert (geometry.b R - 1))
  rw [hdist] at htri
  change (cosetGraph R).dist d (e.walk.getVert (geometry.b R - 1)) < geometry.b R
  omega

/-- The terminal commutator lies in the printed backward edge plane.
Index b-1 is alpha'-5; index b is alpha'-4. -/
theorem terminalProduct_le_backward_edge (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e ≤
      edgeCommutator R (e.walk.getVert (geometry.b R))
        (e.walk.getVert (geometry.b R - 1)) :=
  commutator_mono le_rfl (radius_four_le_predecessor hb e)

/-- Order four fills the backward edge, whose order is at most four by
the earlier natural-module calculation. The selected product must still
supply the order-four premise. -/
theorem terminalProduct_eq_backward_edge_of_card [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (hcard : Nat.card (terminalProduct e) = 4) :
    terminalProduct e =
      edgeCommutator R (e.walk.getVert (geometry.b R))
        (e.walk.getVert (geometry.b R - 1)) := by
  have hc := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hadj : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h
  have hle := terminalProduct_le_backward_edge hb e
  have hU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) _ _ hc hadj
  let := finite_stabilizer R (e.walk.getVert (geometry.b R))
  let : Finite (edgeCommutator R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1))) := Finite.of_injective
    (inclusion (hU.trans ((U_le_Z R _).trans (Z_le_stabilizer R _))))
    (inclusion_injective _)
  apply eq_of_le_of_card_ge hle
  rw [hcard]
  exact Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
    (LocalCommutator.moduleFacts common) _ _ hc hadj

/-- The turn at alpha'-6 puts the terminal Z in the opposite local span.
The radius-four actor lies in both kernels, so (4.4.1)(i) proves the
fixed-core estimate without an order or product-identification premise. -/
theorem terminalProduct_le_fixed (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)) := by
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hb8 : 8 ≤ geometry.b R := by
    rw [Nat.even_iff] at heven
    omega
  have heven2 : Even (geometry.b R - 2) := by
    rw [Nat.even_iff] at heven ⊢
    omega
  have heven4 : Even (geometry.b R - 4) := by
    rw [Nat.even_iff] at heven ⊢
    omega
  have hc2 := ExtendedPath.vertex_color e heven2 (by omega)
  have hc4 := ExtendedPath.vertex_color e heven4 (by omega)
  have hQ (i : ℕ) (hi : i = geometry.b R - 2 ∨ i = geometry.b R - 4)
      (hc : color R (e.walk.getVert i) = false) :
      VBall R a 4 ≤ Q R (e.walk.getVert i) := by
    apply (Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le
      (e.walk.getVert i) a 4 i ?_).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q _ hc _ (by rcases hi with rfl | rfl <;> omega))
    have hd := ExtendedPath.distance e (i := 4) (j := i)
      (by rcases hi with rfl | rfl <;> omega) (by rcases hi with rfl | rfl <;> omega)
    rw [e.center_eq] at hd
    rw [hd]
    rcases hi with rfl | rfl <;> omega
  obtain ⟨g, hg, ht⟩ := e.turns (geometry.b R - 2) heven2 (by omega) (by omega)
  have ht' : act R g (e.walk.getVert (geometry.b R)) =
      e.walk.getVert (geometry.b R - 4) := by
    simpa only [show geometry.b R - 2 + 2 = geometry.b R by omega,
      show geometry.b R - 2 - 2 = geometry.b R - 4 by omega] using ht
  have hinv : act R g⁻¹ (e.walk.getVert (geometry.b R - 4)) =
      e.walk.getVert (geometry.b R) := by
    rw [← ht', ← act_mul, mul_inv_cancel, act_one]
  have hspan : Z R (e.walk.getVert (geometry.b R)) ≤
      localZSpan R (e.walk.getVert (geometry.b R - 4))
        (e.walk.getVert (geometry.b R - 2)) := by
    have hh := le_iSup (fun k : stabilizer R (e.walk.getVert (geometry.b R - 2)) =>
      Z R (act R k (e.walk.getVert (geometry.b R - 4))))
        ⟨g⁻¹, (stabilizer R _).inv_mem hg⟩
    simpa only [localZSpan, hinv] using hh
  exact (commutator_mono hspan
    (le_inf (hQ _ (Or.inr rfl) hc4) (hQ _ (Or.inl rfl) hc2))).trans
      (RegularPaths.CommutatorPropagation.span_kernel_intersection_le_fixed
        (by omega) hlocal hc4 hc2 (by
          rw [ExtendedPath.distance e (by omega) (by omega)]
          omega))

/-- The natural-module bound for the backward edge bounds the literal product. -/
theorem terminalProduct_card_le_four [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (terminalProduct e) ≤ 4 := by
  have hc := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hadj : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h
  have hU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) _ _ hc hadj
  let := finite_stabilizer R (e.walk.getVert (geometry.b R))
  let : Finite (edgeCommutator R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1))) := Finite.of_injective
    (inclusion (hU.trans ((U_le_Z R _).trans (Z_le_stabilizer R _))))
    (inclusion_injective _)
  exact (card_le_of_le (terminalProduct_le_backward_edge hb e)).trans
    (Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (LocalCommutator.moduleFacts common) _ _ hc hadj)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
