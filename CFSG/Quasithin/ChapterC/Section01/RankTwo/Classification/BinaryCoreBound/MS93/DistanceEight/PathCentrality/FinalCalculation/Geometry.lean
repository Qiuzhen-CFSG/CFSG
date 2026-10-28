module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reversal

/-!
# The marked vertices used in the final MS93 calculation

The actual extended path has index zero at alpha-4 and index four at alpha.
Tree uniqueness makes its subwalks geodesic. The critical window beginning
at index two, reversed, proves that alpha-2 is a genuine moving neighbor
of alpha. This supplies the orbit-span consumer of (4.4.5).

Source: MS93 (4.4.5), printed pp.894--895. Existence of the extended path
remains with the earlier regular-path argument.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
open RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

namespace ExtendedPath
variable {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)

/-- In the actual amalgam tree the retained simple walk is geodesic. -/
theorem shortest : e.walk.length = (cosetGraph R).dist e.first e.last := by
  obtain ⟨q, hq⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist e.first e.last
  have he := (geometry.tree.isAcyclic.subsingleton_path e.first e.last).elim
    ⟨e.walk, e.isPath⟩ ⟨q, q.isPath_of_length_eq_dist hq⟩
  exact (congrArg (fun p : (cosetGraph R).Path e.first e.last => p.val.length) he).trans hq

/-- Distances on the extended source path, with its literal zero-based indices. -/
theorem distance {i j : ℕ} (hij : i ≤ j) (hj : j ≤ geometry.b R + 8) :
    (cosetGraph R).dist (e.walk.getVert i) (e.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk (shortest e) (e.walk.isSubwalk_drop i))
    ((e.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ e.walk.length - i := by rw [e.length_eq]; omega
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

/-- Every even marked vertex has M-type. -/
theorem vertex_color {i : ℕ} (hi : Even i) (hib : i ≤ geometry.b R + 8) :
    color R (e.walk.getVert i) = false :=
  (walk_vertex_color e.start_color e.walk (e.length_eq ▸ hib)).mpr hi

include e in
/-- The chosen center really has the color needed by the local source APIs. -/
theorem center_color : color R a = false := by
  simpa only [e.center_eq] using vertex_color e (i := 4) (by decide) (by omega)

/-- The source alpha-2 is an actual distance-two vertex, not a radius witness. -/
theorem backward_distance : (cosetGraph R).dist (e.walk.getVert 2) a = 2 := by
  simpa only [e.center_eq] using distance e (i := 2) (j := 4) (by decide) (by omega)

/-- Reverse the critical window (alpha-2, alpha'-2). The vertex alpha
is two steps before its endpoint, so that endpoint moves modulo B_alpha. -/
theorem backward_moving [Finite M] (source : LocalSource L R)
    (hb : 2 < geometry.b R) :
    e.walk.getVert 2 ∈ Escape.movingNeighbors geometry a := by
  let p := e.window 2 (by decide) (by decide)
  have hp := source.critical_reverse geometry _ p.start_color _ p.end_color p.critical
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source hb p.end_color hp
  constructor
  · rw [SimpleGraph.dist_comm]
    exact backward_distance e
  · have h₁ := distance e (i := 4) (j := 2 + geometry.b R) (by omega) (by omega)
    have h₂ := distance e (i := 2) (j := 2 + geometry.b R) (by omega) (by omega)
    rw [e.center_eq] at h₁
    rw [SimpleGraph.dist_comm (u := e.walk.getVert (2 + geometry.b R)), h₁,
      SimpleGraph.dist_comm (v := e.walk.getVert 2), h₂]
    omega

end ExtendedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
