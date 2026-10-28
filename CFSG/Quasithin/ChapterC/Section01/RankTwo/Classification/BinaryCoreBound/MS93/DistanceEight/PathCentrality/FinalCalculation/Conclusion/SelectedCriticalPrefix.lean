module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalPrefixControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Selected

/-!
# The selected Ri bound from critical-prefix local control

The actor Z at the original endpoint is b-2 steps from the selected center.
If Ri failed its fixed-core bound, this actor would force the opposite orbit
to escape. The critical-prefix control theorem then gives the required bound.
Thus the selected-commutator application needs no unrestricted local-control
or unconditional opposite-orbit escape assumption.

Source: Meierfrankenfeld--Stellmacher (1993), the concluding calculation of
(4.4.5), printed p.895. The critical-prefix input is owned by the preceding
(4.4.1) source proof.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The selected source Ri needs only critical-prefix local control. -/
theorem selectedCommutator_le_fixed_of_criticalPrefix
    (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
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
  exact LocalCommutator.endpoint_commutator_le_fixed_of_criticalPrefix (by omega)
    hprefix ha hd had ht hterminal (le_inf hQa hQd)

/-- Both source bounds at the actual selected critical pair, from the
restricted critical-prefix input. -/
theorem selectedCommutator_bounds_of_criticalPrefix (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
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
    (selectedCommutator_le_fixed_of_criticalPrefix hb hprefix e had hterminal)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
