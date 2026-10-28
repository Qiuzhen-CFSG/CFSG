module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FiveGirth

/-!
# Four-walk geodesicity in a bipartite graph

This four-walk specialization preserves the bipartite interface used by the
unitary completion geometry. The general half-girth theorem proves it directly:
a shorter path would form a cycle of length less than eight.

Source: Aschbacher–Smith F.4.6(6–8), printed pp.276–278.
-/

public section
open SimpleGraph SimpleGraph.BasedWalk
namespace SimpleGraph.PathTransitivePolygon
variable {V : Type*} {G : SimpleGraph V}

/-- Girth at least eight makes every nonbacktracking four-walk geodesic. -/
theorem four_geodesic_of_cycle_bound
    (conn : G.Connected)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 8 ≤ c.length)
    {x : V} (p : BasedWalk G 4 x) (hp : p.Nonbacktracking) :
    G.dist x p.endpoint = 4 := by
  have _hcolor := @hcolor
  exact geodesic_of_nonbacktracking_of_double_le_girth conn hg p hp

end SimpleGraph.PathTransitivePolygon
