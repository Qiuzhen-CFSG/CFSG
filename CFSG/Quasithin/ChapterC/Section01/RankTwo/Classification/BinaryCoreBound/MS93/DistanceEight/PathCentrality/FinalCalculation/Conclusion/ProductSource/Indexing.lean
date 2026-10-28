module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource

/-!
# The terminal-edge indexing obstruction

Printed p.895 identifies the selected product with
U_(alpha'-5)^(alpha'-4), at indices (b,b-1). The existing
ProductCalculation.opposite_edge instead specifies (b,b+1).
These edges cannot be interchanged: at b=8 the extended path's clause at
index eight distinguishes their normalization by Z_(alpha'+4).

The source backward containment and the existing order-four field make
ProductCalculation exclude b=8. Its actual downstream distance theorem,
applied with MovingEdgeFixed, gives b=8. Thus the two inputs requested by
that final consumer are incompatible. This diagnoses the local output
specification; it does not refute the printed MS93 theorem. The original
specification and its consumers are preserved here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), printed p.895,
and the extended-path nonnormalization on printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- At b=8 the last critical endpoint normalizes the forward edge, while
the retained nonnormalization clause excludes normalization of the backward
edge. Thus these two actual edge commutators differ. -/
theorem backward_edge_ne_forward_of_eight
    (hb : geometry.b R = 8) {a : Vertex R}
    (e : RegularPaths.ExtendedPath geometry a) :
    edgeCommutator R (e.walk.getVert (geometry.b R))
        (e.walk.getVert (geometry.b R - 1)) ≠
      edgeCommutator R (e.walk.getVert (geometry.b R))
        (e.walk.getVert (geometry.b R + 1)) := by
  intro heq
  have hlocal := (e.window 8 (by decide) (by decide)).endpoint_Z_le_start_stabilizer
    (by omega : 0 < geometry.b R)
  have hQ : Z R (e.walk.getVert (8 + geometry.b R)) ≤
      Q R (e.walk.getVert (geometry.b R + 1)) := by
    have hc := (e.window 8 (by decide) (by decide)).end_color
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc, SimpleGraph.dist_comm,
      ExtendedPath.distance e (by omega) (by omega)]
    change 8 + geometry.b R - (geometry.b R + 1) < geometry.b R
    omega
  have hnorm := hQ.trans (normalizer_commutator_ge_right
    (Z R (e.walk.getVert (geometry.b R))) (Q R (e.walk.getVert (geometry.b R + 1))))
  apply e.nonnormalization 8 (by decide) (by decide) (by decide)
  apply le_inf hlocal
  have heq' : edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) =
      edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 9) := by
    simpa only [hb, Nat.reduceSub, Nat.reduceAdd] using heq
  change Z R (e.walk.getVert (8 + geometry.b R)) ≤
    normalizer (edgeCommutator R (e.walk.getVert 8) (e.walk.getVert 7) : Set (FreeAmalgam R))
  rw [heq']
  simpa only [hb, Nat.reduceAdd, edgeCommutator] using hnorm

/-- The existing output specification uses the wrong terminal edge: its
order-four and forward-edge fields exclude the intended distance-eight case. -/
theorem productCalculation_distance_ne_eight [Finite M]
    (common : CommonFacts R source geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) : geometry.b R ≠ 8 := by
  intro hb
  have hback := terminalProduct_eq_backward_edge_of_card common (by omega) e product.card
  exact backward_edge_ne_forward_of_eight hb e (hback.symm.trans product.opposite_edge)

/-- Application to the literal final consumer: its two intermediate inputs
are incompatible with the existing successor-indexed product contract. This
is a contract obstruction, not a contradiction to the printed theorem. -/
theorem productCalculation_incompatible_with_movingEdgeFixed [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hfixed : MovingEdgeFixed geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    ¬ ProductCalculation e := by
  intro product
  exact productCalculation_distance_ne_eight common e product
    (distance_eq_eight common hb hfixed e product)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
