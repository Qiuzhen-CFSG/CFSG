module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.Systems
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Reversal
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Triangles
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Contraction.Normalized
public import Theory.GroupTheory.Amalgam.UniquenessSystem.Recognition
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2

/-!
# The general local-geometry recognition interface

This retains the universal conditional assembly theorem: equivalent local
systems and a triangle base identify the source with the chosen concrete
carrier. The unconditional J₂ specialization is exported by the parent module.

Source: Aschbacher–Smith I.4.7(1), p.418; Aschbacher, *Sporadic Groups*
(1994), §§37 and 47, especially 47.10, pp.266–267.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition

open Theory.GroupTheory.GraphUniquenessSystem

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The conditional assembly step, retaining every unproved local and geometric
premise and the actual ATLAS target. Simplicity is used on the source side. -/
theorem recognition_of_local_geometry (D : Seed G)
    (L : LocalData D) {W : Type*} [MulAction Sporadic.LeechRelated.J2.Carrier W]
    (M : System Sporadic.LeechRelated.J2.Carrier W)
    (s : Similarity L.simpleSystem M)
    (he : s.IsEquivalence)
    (hsc : D.graph.TriangleSimplyConnected)
    (htri : L.simpleSystem.TrianglesInLocalOrbits) :
    Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) := by
  exact ⟨s.recognitionEquivOfSourceBase he
    (L.simpleSystem.isBase_of_triangleSimplyConnected hsc htri)⟩

end CFSG.Quasithin.Janko23.J2Recognition
