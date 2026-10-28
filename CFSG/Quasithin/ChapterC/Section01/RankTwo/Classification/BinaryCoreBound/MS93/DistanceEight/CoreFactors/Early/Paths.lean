module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Inputs

/-!
# Metric facts for the preceding extended critical path

The tree property makes the supplied simple walk geodesic. Taking and
dropping subwalks then gives exact distances between its indexed vertices.
These calculations retain the actual path from (4.4.5); they do not assert
existence of the further path chosen at the beginning of (4.5).

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.894--896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

/-- Every supplied extended path is a geodesic, since the amalgam graph is a tree. -/
theorem path_shortest {a : Vertex R} (e : ExtendedPath geometry a) :
    e.walk.length = (cosetGraph R).dist e.first e.last := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist e.first e.last
  have heq : e.walk = w := Subtype.mk.inj
    ((geometry.tree.isAcyclic.subsingleton_path e.first e.last).elim
      ⟨e.walk, e.isPath⟩ ⟨w, w.isPath_of_length_eq_dist hw⟩)
  rw [heq]
  exact hw

/-- Exact distances between ordered indices, retaining the original walk. -/
theorem segment_distance {a : Vertex R} (e : ExtendedPath geometry a)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ e.walk.length) :
    (cosetGraph R).dist (e.walk.getVert i) (e.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk (path_shortest e) (e.walk.isSubwalk_drop i))
    ((e.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ e.walk.length - i := Nat.sub_le_sub_right hj i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

/-- Even positions in the extended path are M-vertices. -/
theorem path_color {a : Vertex R} (e : ExtendedPath geometry a)
    {i : ℕ} (hi : Even i) (hi' : i ≤ e.walk.length) :
    color R (e.walk.getVert i) = false :=
  (walk_vertex_color e.start_color e.walk hi').mpr hi


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
