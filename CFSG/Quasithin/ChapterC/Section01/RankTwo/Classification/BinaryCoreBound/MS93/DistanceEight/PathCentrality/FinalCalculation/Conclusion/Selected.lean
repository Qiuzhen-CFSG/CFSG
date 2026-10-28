module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Distance

/-!
# The selected commutators in the concluding MS93 calculation

The source Ri is [localZSpan(alpha,delta_i), Z_(alpha'-4)]. The literal
geodesic distances place its actor in Q_alpha intersect Q_delta_i, so
(4.4.1)(i) puts Ri in the source fixed core D_delta_i. The same actor
normalizes the span, proving containment in the actual radius at delta_i.

This application retains unrestricted LocalCommutatorControl: criticality
of (delta_i,alpha'-2) alone does not certify escape of the opposite span
localZSpan(alpha,delta_i). The choices, nontriviality and product equalities
remain the independent selected-product calculation.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual Ri, with the selected local span and alpha'-4 endpoint. -/
noncomputable abbrev selectedCommutator {a : Vertex R}
    (e : RegularPaths.ExtendedPath geometry a) (d : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅localZSpan R a d, Z R (e.walk.getVert (geometry.b R))⁆

/-- The local application of (4.4.1)(i) to a selected Ri. The original
unrestricted control is retained here: the prescribed replacement makes
(delta,alpha'-2) critical, which does not itself certify escape of the
opposite span localZSpan(alpha,delta). -/
theorem selectedCommutator_le_fixed (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) {d : Vertex R}
    (had : (cosetGraph R).dist a d = 2)
    (hterminal : (cosetGraph R).dist d (e.walk.getVert (geometry.b R)) + 2 = geometry.b R) :
    selectedCommutator e d ≤ fixedCore R d := by
  have ha := ExtendedPath.center_color e
  have hd : color R d = false :=
    (color_eq_of_dist_even R a d (by rw [had]; decide)).symm.trans ha
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hQa : Z R (e.walk.getVert (geometry.b R)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    have hdist := ExtendedPath.distance e (i := 4) (j := geometry.b R) (by omega) (by omega)
    rw [e.center_eq] at hdist
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm, hdist]
    change geometry.b R - 4 < geometry.b R
    omega
  have hQd : Z R (e.walk.getVert (geometry.b R)) ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm]
    change (cosetGraph R).dist d (e.walk.getVert (geometry.b R)) < geometry.b R
    omega
  exact (commutator_mono le_rfl (le_inf hQa hQd)).trans
    (RegularPaths.CommutatorPropagation.span_kernel_intersection_le_fixed
      common.large_distance hlocal ha hd had)

/-- Ri lies in the radius at delta, so its fixed-core containment is local
and the product with D_delta has the intended relative meaning. -/
theorem selectedCommutator_le_radius {a : Vertex R}
    (e : RegularPaths.ExtendedPath geometry a) {d : Vertex R}
    (had : (cosetGraph R).dist a d = 2)
    (hterminal : (cosetGraph R).dist d (e.walk.getVert (geometry.b R)) + 2 = geometry.b R) :
    selectedCommutator e d ≤ V R d := by
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hQd : Z R (e.walk.getVert (geometry.b R)) ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm]
    change (cosetGraph R).dist d (e.walk.getVert (geometry.b R)) < geometry.b R
    omega
  exact (le_normalizer_iff_commutator_le_left.mp
    ((hQd.trans (fun _ hx => hx.1)).trans (localZSpan_normalized R a d))).trans
      (localZSpan_le_V R had.le)

/-- Application to the actual selected critical pair (delta,alpha'-2).
The triangle inequalities force alpha'-4 to be exactly b-2 from delta;
thus the preceding local bounds have no extra geometric premise here. -/
theorem selectedCommutator_bounds_of_critical (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) {d : Vertex R}
    (had : (cosetGraph R).dist a d = 2)
    (p : CriticalPath R geometry d (e.walk.getVert (2 + geometry.b R))) :
    selectedCommutator e d ≤ V R d ⊓ fixedCore R d := by
  have hcenter := ExtendedPath.distance e (i := 4) (j := geometry.b R) (by omega) (by omega)
  rw [e.center_eq] at hcenter
  have hupper := (cosetGraph_connected R).dist_triangle (u := d) (v := a)
    (w := e.walk.getVert (geometry.b R))
  rw [SimpleGraph.dist_comm (u := d) (v := a), had, hcenter] at hupper
  have hnext : (cosetGraph R).dist (e.walk.getVert (geometry.b R))
      (e.walk.getVert (2 + geometry.b R)) = 2 := by
    rw [ExtendedPath.distance e (by omega) (by omega)]
    omega
  have hlower := (cosetGraph_connected R).dist_triangle (u := d)
    (v := e.walk.getVert (geometry.b R)) (w := e.walk.getVert (2 + geometry.b R))
  rw [p.shortest.symm.trans p.length_eq_b, hnext] at hlower
  have hterminal : (cosetGraph R).dist d (e.walk.getVert (geometry.b R)) + 2 =
      geometry.b R := by omega
  exact le_inf (selectedCommutator_le_radius e had hterminal)
    (selectedCommutator_le_fixed common hb hlocal e had hterminal)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
