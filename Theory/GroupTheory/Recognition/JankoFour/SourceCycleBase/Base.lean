module

public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Input
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleBase

/-!
# The actual local-orbit base consumer

AS91 (5.5) and the marked local-edge identity put every triangle in a
translate of the centralizer's edge orbit. This is the 77-point plane, not
the separate three-vertex `LocalTriangle` construction. Consequently the
remaining section 7 triangulability conclusion will give the base for this
very coset system through nonabelian normal walk closure.

Source: Aschbacher–Segev (1991), (5.5), (7.9), and the proof in §8.
This module does not yet prove triangulability.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

open GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

namespace Input
variable (d : Input h)

theorem trianglesInLocalOrbits : d.system.TrianglesInLocalOrbits := by
  intro a b c hab hbc hca
  have hab' := (d.system_adj_iff a b).mp hab
  have hbc' := (d.system_adj_iff b c).mp hbc
  have hca' := (d.system_adj_iff c a).mp hca
  obtain ⟨π, ha, hb, hc⟩ := d.triangles_in_plane a b c hab' hbc' hca'
  obtain ⟨g, rfl⟩ := Cosets.transitive (centralizer z) π
  have hplane {x : Point d.P} (hx : OnPlane d.P x (g • Cosets.vertex (centralizer z) 1)) :
      OnPlane d.P (g⁻¹ • x) (Cosets.vertex (centralizer z) 1) := by
    change Cosets.Incident d.P.M (centralizer z) (g⁻¹ • x)
      (Cosets.vertex (centralizer z) 1)
    simpa only [inv_smul_smul] using incident_smul g⁻¹ hx
  exact ⟨g,
    (d.system_local_edge _ _).mpr ⟨adj_smul g⁻¹ hab', hplane ha, hplane hb⟩,
    (d.system_local_edge _ _).mpr ⟨adj_smul g⁻¹ hbc', hplane hb, hplane hc⟩,
    (d.system_local_edge _ _).mpr ⟨adj_smul g⁻¹ hca', hplane hc, hplane ha⟩⟩

/-- Each actual ambient triangle is already a generator of the base family. -/
theorem triangle_mem_baseCycles (a : Point d.P) (p : d.system.graph.Walk a a)
    (hp : p.length = 3) : p ∈ d.system.baseCycles a :=
  d.system.triangle_mem_baseCycles d.trianglesInLocalOrbits a p hp

/-- The final conversion has no native-system base premise. The remaining
triangulability hypothesis is to be discharged by this family's section 7 proof. -/
theorem isBase_of_triangulable (htri : SimpleGraph.WalkClosure.Triangulable d.system.graph) :
    d.system.IsBase := by
  apply SimpleGraph.WalkClosure.isCycleBase_of_triangles htri
  intro a p hp
  exact .cycle p (d.triangle_mem_baseCycles a p hp)

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
