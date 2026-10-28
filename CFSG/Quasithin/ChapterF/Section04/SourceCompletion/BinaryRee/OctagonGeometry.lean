module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.NinePath
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.OctagonRecognition

/-!
# The original small binary Ree completion is an octagon

The source's two different eight-edge geodesics give an actual sixteen-cycle.
The proved nine-path transitivity at both vertex types and the original two
coset orbits force girth at least sixteen and diameter at most eight. The
local valences supply path extension. Every statement concerns the original
completion graph and its literal ambient action, with smallness as its only
remaining source hypothesis.

These are the geometric conclusions needed for the apartment reflections and
compatible reconstruction in F.4.8. No group recognition or polygon premise
is added to the faithful completion.

Source: Aschbacher–Smith F.4.7–8, printed pp.277–278, via F.3.5.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (c : Completion G)

/-- The source smallness hypothesis gives all three original octagon conclusions. -/
theorem octagon_geometry (hsmall : c.Small) :
    (∀ v (p : c.graph.Walk v v), p.IsCycle → 16 ≤ p.length) ∧
      (∀ v w : c.Vertex, c.graph.dist v w ≤ 8) ∧
      (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length = 16) := by
  have hdeg : BasedWalk.HasTwoNeighbors c.graph := by
    intro v w
    obtain ⟨z, hz, hzw, _⟩ := c.thick v w w
    exact ⟨z, hz, hzw⟩
  exact OctagonRecognition.octagon_of_small c.graphAction c.connected hdeg c.nine_transitive
    (fun v : c.Vertex => v.type) (fun h => h.1)
    (fun {v w} h => (Subgroup.CosetGeometry.RankTwo.same_orbit_iff c.family v w).mpr h) hsmall

/-- The original graph has no simple cycle shorter than sixteen. -/
theorem cycle_bound_of_small (hsmall : c.Small) (v : c.Vertex) (p : c.graph.Walk v v)
    (hp : p.IsCycle) : 16 ≤ p.length :=
  (c.octagon_geometry hsmall).1 v p hp

/-- Every two original vertices have distance at most eight. -/
theorem diameter_bound_of_small (hsmall : c.Small) (v w : c.Vertex) : c.graph.dist v w ≤ 8 :=
  (c.octagon_geometry hsmall).2.1 v w

/-- An actual sixteen-cycle exists in the original source graph. -/
theorem exists_sixteen_cycle_of_small (hsmall : c.Small) :
    ∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length = 16 :=
  (c.octagon_geometry hsmall).2.2

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
