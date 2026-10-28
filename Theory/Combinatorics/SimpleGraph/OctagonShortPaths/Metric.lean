module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The unique predecessor in an octagonal graph

For a vertex at positive distance below eight, a shortest path supplies its
preceding neighbor. Two such choices give shortest paths of combined length
below sixteen, so the girth bound makes the paths and their first steps equal.
This is the metric fact used in the geodesic counts of Aschbacher–Smith J.5.9.
-/

public section
namespace SimpleGraph.OctagonShortPaths
variable {V : Type*} {G : SimpleGraph V}

theorem unique_predecessor (hc : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    (r v : V) (hpos : 0<G.dist v r) (hshort : G.dist v r<8) :
    ∃! w, G.Adj v w ∧ G.dist w r+1=G.dist v r := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => simp at hpos
  | @cons v w r hvw p =>
    have hd := G.dist_le p
    have ht := hc.dist_triangle (u:=v) (v:=w) (w:=r)
    rw [dist_eq_one_iff_adj.mpr hvw] at ht
    have hlen : p.length+1=G.dist v r := hp
    have he : G.dist w r+1=G.dist v r := by omega
    refine ⟨w,⟨hvw,he⟩,?_⟩
    rintro z ⟨hvz,hz⟩
    obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist z r
    have hq' : (Walk.cons hvz q).length=G.dist v r := by
      simpa only [Walk.length_cons,hq] using hz
    have heq := paths_eq hg
      ((Walk.cons hvz q).isPath_of_length_eq_dist hq')
      ((Walk.cons hvw p).isPath_of_length_eq_dist hp) (by rw [hq',hp]; omega)
    have hs := congrArg (fun a : G.Walk v r => a.getVert 1) heq
    simpa using hs

end SimpleGraph.OctagonShortPaths
