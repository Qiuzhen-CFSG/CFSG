module

public import CFSG.Quasithin.ChapterF.Section05.TriangleOrbit
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.UniquenessSystem

/-!
# The concrete model in the F.5 completion argument

The uniqueness system is the actual action of the derived six-dimensional
orthogonal group on norm-minus-one projective points, with local group the
stabilizer of the standard triple. Its graph, local triangle, and triangle
orbit are now supplied outright. The ambient conclusion therefore needs only
the source system and its compatible local-group equivalence with this model.

Source: Aschbacher–Smith, F.5.7–F.5.8, pp.302–304.
-/

public section

namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition

open Theory.GroupTheory.GraphUniquenessSystem
open OmegaSixThree.OrthogonalityGraph

/-- The literal model triangle has the triangle-orbit property of F.5.8. -/
theorem model_triangle_orbit : modelLocalTriangle.IsTriangleOrbit :=
  triangleOrbit_of_standard_vertices modelSystem rfl modelLocalTriangle rfl

variable {G G0 : Type*} [Group G] [Group G0]

/-- F.5's ambient conclusion with every model-geometric premise discharged. -/
theorem source_ambient_of_model_equivalence
    (i : G0 →* G) (W : System G (G ⧸ i.range))
    (s : Similarity modelSystem W) (hs : s.IsEquivalence) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) :=
  source_ambient_of_geometric_equivalence i modelSystem rfl W s hs
    modelLocalTriangle model_triangle_orbit

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
