module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Transport

/-!
# The distance bound from the concluding MS93 product

The literal product R1 R2 on printed p.895 is
[Z_(alpha'-4), V_alpha^(4)]. Its natural intersection, edge description, image index and fixed-core
containment are retained as an intermediate output specification, still to
be constructed by the selected-commutator argument.

The forward-edge identity is required only under b>8, as in the source.
Given that calculation and the symmetric moving-edge bound, a residual turn
identifies the product with the backward edge plane at alpha+4. If b>8,
its containment in Z_(alpha'-4) makes it centralize Z_(alpha'+4), contradicting
the actual extended path's nonnormalization. Parity and b>6 give b=8.

These are conditional assembly results, not a proof that the product or
symmetric bounds follow from the preceding source. Source: original MS93
(4.4), printed p.895, immediately after (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The literal product R1 R2, identified on p.895 with this commutator.
Index b is alpha'-4 since the extended path starts at alpha-4. -/
noncomputable abbrev terminalProduct {a : Vertex R}
    (e : RegularPaths.ExtendedPath geometry a) : Subgroup (FreeAmalgam R) :=
  ⁅Z R (e.walk.getVert (geometry.b R)), VBall R a 4⁆

/-- Output specification for the selected Ri calculation on p.895.
It contains no distance-eight, local-centrality or index conclusion.
Existence from the earlier source controls is a separate proof obligation. -/
structure ProductCalculation {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) : Prop where
  natural_intersection : terminalProduct e = U R a ⊓ Q R (e.walk.getVert (4 + geometry.b R))
  image_index : (Q R (e.walk.getVert (geometry.b R))).relIndex (VBall R a 4) = 4
  /-- Only used in the source's b>8 contradiction, not asserted at b=8. -/
  first_edge : 8 < geometry.b R → terminalProduct e = edgeCommutator R a (e.walk.getVert 5)
  opposite_edge : terminalProduct e =
    edgeCommutator R (e.walk.getVert (geometry.b R)) (e.walk.getVert (geometry.b R + 1))
  card : Nat.card (terminalProduct e) = 4
  fixed : terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2))

/-- Consecutive marked vertices on the retained path are genuinely adjacent. -/
theorem path_adjacent {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (i : ℕ) (hi : i < geometry.b R + 8) :
    Adjacent R (e.walk.getVert i) (e.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (e.walk.adj_getVert_succ (e.length_eq ▸ hi))

/-- A critical window gives the genuine moving vertex two before any
permitted marked center. No backward-orbit label is substituted for movement. -/
theorem marked_moving [Finite M] (common : CommonFacts R source geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {i : ℕ} (hi : Even i) (hi8 : i ≤ 8) :
    e.walk.getVert i ∈ Escape.movingNeighbors geometry (e.walk.getVert (i + 2)) := by
  have hb := common.large_distance
  let p := e.window i hi hi8
  have hp := source.critical_reverse geometry _ p.start_color _ p.end_color p.critical
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance p.end_color hp
  constructor
  · rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  · have h₁ := ExtendedPath.distance e (i := i + 2) (j := i + geometry.b R)
      (by have := common.large_distance; omega) (by omega)
    have h₂ := ExtendedPath.distance e (i := i) (j := i + geometry.b R) (by omega) (by omega)
    rw [SimpleGraph.dist_comm (u := e.walk.getVert (i + geometry.b R)), h₁,
      SimpleGraph.dist_comm (v := e.walk.getVert i), h₂]
    have := common.large_distance
    omega

/-- The final source contradiction for b>8. A residual turn transports the
fixed plane from alpha to alpha+4, while its opposite edge description puts
it in Z_(alpha'-4). Distance eight then makes it centralize Z_(alpha'+4),
contradicting the retained nonnormalization at alpha+4. -/
theorem distance_eq_eight [Finite M] (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hfixed : MovingEdgeFixed geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) : geometry.b R = 8 := by
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  rw [Nat.even_iff] at heven
  suffices hle : geometry.b R ≤ 8 by omega
  by_contra! hlarge
  let K := terminalProduct e
  have hfirst : K = edgeCommutator R (e.walk.getVert 4) (e.walk.getVert 5) := by
    simpa only [e.center_eq] using product.first_edge hlarge
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
    rw [show K = _ from product.opposite_edge]
    exact (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) _ _
      (ExtendedPath.vertex_color e (i := geometry.b R) (geometry.even (alpha R) rfl) (by omega))
      (path_adjacent e (geometry.b R) (by omega))).trans (U_le_Z R _)
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

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
