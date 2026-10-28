module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.MarkedPairing.FixedLine

/-!
# The critical pair selected in the terminal argument

Claim (3) and the source (2.1)(vi) obstruction force the selected lambda to
escape Q_c. Its distance from c is at most b along the retained predecessor,
so critical minimality and reversal prove the actual critical pair. The
original first neighbor beta remains a first neighbor toward lambda.

The marked pairing restricts both equal image indices to two or four. Their
order-four assertion remains a separate source step.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), p.892, the paragraph following claim (3).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace TerminalNeighbor
variable {a c : Vertex R} {w : BackwardWitness R geometry a c}

/-- The selected layer escapes the actual kernel at c. -/
theorem not_le_center_kernel (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    ¬ Z R n.vertex ≤ Q R c := by
  intro h
  apply n.triple_noncontainment common hb ha
  have hbound := n.intersection_bound common hb ha hd
  rw [inf_eq_left.mpr h] at hbound
  exact hbound.trans le_sup_right

omit [Finite M] in
/-- Its distance from c is at most the original critical distance. -/
theorem distance_center_le (hb : 2 ≤ geometry.b R) (n : TerminalNeighbor w) :
    (cosetGraph R).dist c n.vertex ≤ geometry.b R := by
  have ht : (cosetGraph R).dist c n.vertex ≤
      (cosetGraph R).dist c w.predecessor + (cosetGraph R).dist w.predecessor n.vertex :=
    (cosetGraph_connected R).dist_triangle
  have hcv : (cosetGraph R).dist c w.predecessor = w.path.walk.length - 2 :=
    w.path.dist_start (Nat.sub_le _ _)
  rw [hcv, n.distance, w.path.length_eq_b] at ht
  omega

/-- The chosen lambda and c form an actual critical pair. -/
theorem critical_from_center (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    CriticalPair R c n.vertex (geometry.exists_critical c w.path.start_color) := by
  have hn := n.not_le_center_kernel common hb ha hd
  have hmin := criticalDistance_le R n.vertex (geometry.exists_critical n.vertex n.color) hn
  rw [geometry.distance_constant n.vertex n.color, SimpleGraph.dist_comm] at hmin
  have hmax := n.distance_center_le (by omega)
  have hc : CriticalPair R n.vertex c (geometry.exists_critical n.vertex n.color) := by
    refine ⟨?_, hn⟩
    rw [geometry.distance_constant n.vertex n.color, SimpleGraph.dist_comm]
    exact le_antisymm hmax hmin
  exact common.critical_reverse n.vertex n.color c w.path.start_color hc

/-- Retain a shortest walk for the selected pair. -/
noncomputable def criticalPath (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    CriticalPath R geometry c n.vertex :=
  CriticalPath.ofPair w.path.start_color (n.critical_from_center common hb ha hd)

/-- The original first edge is also the first edge toward the selected lambda. -/
theorem first_neighbor_distance (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    (cosetGraph R).dist (w.path.walk.getVert 1) n.vertex + 1 =
      (cosetGraph R).dist c n.vertex := by
  have hlen := w.path.length_eq_b
  have hcn : (cosetGraph R).dist c n.vertex = geometry.b R :=
    (n.critical_from_center common hb ha hd).1.trans
      (geometry.distance_constant c w.path.start_color)
  have hfirst : (cosetGraph R).dist c (w.path.walk.getVert 1) = 1 :=
    w.path.dist_start (by omega)
  have hsegment : (cosetGraph R).dist (w.path.walk.getVert 1) w.predecessor ≤
      w.path.walk.length - 3 := by
    have h := SimpleGraph.dist_le ((w.path.walk.drop 1).take (w.path.walk.length - 3))
    rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.drop_getVert] at h
    have hstep : 1 + (w.path.walk.length - 3) = w.path.walk.length - 2 := by omega
    rw [hstep] at h
    exact h.trans (min_le_left _ _)
  have hupper : (cosetGraph R).dist (w.path.walk.getVert 1) n.vertex ≤
      (cosetGraph R).dist (w.path.walk.getVert 1) w.predecessor +
      (cosetGraph R).dist w.predecessor n.vertex := (cosetGraph_connected R).dist_triangle
  have hlower : (cosetGraph R).dist c n.vertex ≤
      (cosetGraph R).dist c (w.path.walk.getVert 1) +
      (cosetGraph R).dist (w.path.walk.getVert 1) n.vertex := (cosetGraph_connected R).dist_triangle
  rw [n.distance] at hupper
  omega

/-- Both selected image indices coincide and belong to {2,4}. -/
theorem image_indices (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    (Q R c).relIndex (Z R n.vertex) = (Q R n.vertex).relIndex (Z R c) ∧
    ((Q R c).relIndex (Z R n.vertex) = 2 ∨
      (Q R c).relIndex (Z R n.vertex) = 4) := by
  let p := n.criticalPath common hb ha hd
  exact ⟨(critical_Z_index_reciprocity common p).symm,
    critical_Z_index_two_or_four common (p.reverse common)⟩

end TerminalNeighbor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
