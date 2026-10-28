module

public import CFSG.Quasithin.ChapterF.Section05.CompletionModel
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.TriangleOrbit

/-!
# The triangle orbit in the F.5 completion argument

The literal derived orthogonal group is transitive on ordered triangles.
Consequently, a local triangle whose vertices are the three standard points
has the `IsTriangleOrbit` property needed by the geometric completion theorem.
This removes that independent geometric premise from the F.5 conclusion;
the model system and its local subgroup still supply the marking.

Source: Aschbacher–Smith, Lemma F.5.8(1),(3), pp.303–304.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Theory.GroupTheory Theory.GroupTheory.GraphUniquenessSystem
open GreenBook.LieModels.UnitaryFour
open OmegaSixThree.OrthogonalityGraph
local notation "hn" => Nat.le_refl 1
local notation "Model" => OmegaSixThree.omegaPlusSixThree
local notation "PSL" => Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)

/-- The source standard-triangle marking discharges the orbit premise in F.5.8. -/
theorem triangleOrbit_of_standard_vertices
    (U : System Model Point) (hgraph : U.graph = graph) (T : U.LocalTriangle)
    (hvertices : T.vertices = {standardFirst, standardSecond, standardThird}) :
    T.IsTriangleOrbit := by
  intro a b c hab hbc hca
  rw [hgraph] at hab hbc hca
  obtain ⟨g, ha, hb, hc⟩ := exists_triangle_transport a b c hab hbc hca
  refine ⟨g, ?_⟩
  rw [hvertices]
  simp only [Set.image_insert_eq, Set.image_singleton, ha, hb, hc]

variable {G G0 : Type*} [Group G] [Group G0]

/-- F.5 with the triangle-orbit hypothesis discharged by the literal standard
marking. The remaining inputs are the source completion and its model comparison. -/
theorem source_conclusion_of_standard_triangle
    (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
    (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (U : System Model Point) (hgraph : U.graph = graph)
    (W : System G (G ⧸ i.range)) (hx : W.x = QuotientGroup.mk (1 : G))
    (s : Similarity U W) (hs : s.IsEquivalence)
    (T : U.LocalTriangle)
    (hvertices : T.vertices = {standardFirst, standardSecond, standardThird})
    (eVertex : U.vertexGroup ≃* Extension.ProjectiveExtension 1 hn) :
    Nonempty (G ≃* PSL) ∧ Nonempty (G0 ≃* Extension.ProjectiveExtension 1 hn) :=
  source_conclusion_of_geometric_equivalence c i z h U hgraph W hx s hs T
    (triangleOrbit_of_standard_vertices U hgraph T hvertices) eVertex

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
