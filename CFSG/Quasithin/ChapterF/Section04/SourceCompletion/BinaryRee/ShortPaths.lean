module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.NinePath
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth

/-!
# Short geodesics before smallness in faithful binary Ree completions

The original local groups give thickness and nine-path transitivity. Changing
the last vertex of a short cycle excludes every cycle of length at most nine.
Hence every nonbacktracking walk of length at most four is a geodesic. This
supplies the four-step source transport in J.4.7 without using smallness or the
later recognition of the completion.

Source: Aschbacher–Smith F.4.6 and J.4.7, printed pp.276 and443–445.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (c : Completion G)

theorem cycle_length_gt_nine (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) :
    9<p.length := cycle_bound_of_root_transitivity c.graphAction c.thick c.nine_transitive v p hp

theorem short_nonbacktracking_isPath {n : ℕ} {v : c.Vertex}
    (p : BasedWalk c.graph n v) (hp : p.Nonbacktracking) (hn : n≤9) :
    p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound c.cycle_length_gt_nine p hp hn

theorem short_nonbacktracking_geodesic {n : ℕ} {v : c.Vertex}
    (p : BasedWalk c.graph n v) (hp : p.Nonbacktracking) (hn : n≤4) :
    c.graph.dist v p.endpoint=n :=
  geodesic_of_nonbacktracking_of_cycle_bound c.connected c.cycle_length_gt_nine p hp (by omega)

theorem four_path_geodesic {v : c.Vertex} (p : BasedWalk c.graph 4 v)
    (hp : p.Nonbacktracking) : c.graph.dist v p.endpoint=4 :=
  c.short_nonbacktracking_geodesic p hp le_rfl

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
