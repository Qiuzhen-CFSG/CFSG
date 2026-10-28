module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NormalCore
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Overgroup
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.System

/-!
# The complete source system inside the normalizer-generated subgroup

The local normal-core argument removes the need to assume the ambient group
simple when constructing its source system. Applied to the actual span of
the three source normalizers, the inherited fusion data and literal inclusion
maps discharge every system axiom. The native octad base then recognizes
this subgroup from a compatible similarity, retaining both prescribed maps.

The original fusion consumer uses exactly the marking and local data from
`SourceData.ofFusion`. This implements the induction-system step of
Aschbacher, *Sporadic Groups* (1994), 41.1 and 41.4–41.5, pp.219–222.
Construction of the native similarity and the 41.2 argument that this span
is the whole ambient group remain separate obligations of the source proof.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- The literal source system needs only global generation once local
faithfulness has been proved. In particular its ambient group need not be
assumed simple. -/
@[expose] def system_of_generation
    (hgenerate : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) : System G (Point F) where
  graph := graph F
  H := threeSpaceNormalizer F
  x := vertex (rowNormalizer F) 1
  y := vertex (rowNormalizer F) (lineSwap F D : G)
  adjacent := graph_adj_base F D
  preserves := graph_preserves F
  faithful := graph_faithful_of_localData F D
  vertex_transitive := graph_vertex_transitive F
  edge_transitive := graph_edge_transitive F D
  local_orbit := ⟨⟨planeSwap F D, planeSwap_mem F D⟩, by
    simpa only [smul_vertex, mul_one] using planeSwap_vertex F D⟩
  generate := by rwa [stabilizer_base]
  vertex_generate := by
    rw [← planeSwap_vertex F D]
    exact vertex_generate F D
  local_generate := by
    rw [← planeSwap_vertex F D]
    exact local_generate F D

/-- The stronger faithfulness proof preserves the previously exported source
system exactly when its original hypotheses are available. -/
theorem system_of_generation_eq_system (hG : IsSimpleGroup G) (hcore : PointCoreFusion z)
    (hgenerate : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) :
    system_of_generation F D hgenerate = system F D hG hcore hgenerate := by rfl

/-- The full uniqueness system in the actual normalizer-generated subgroup.
All system axioms, including generation and faithfulness, are discharged. -/
@[expose] def normalizerSpan_system :
    System (normalizerSpan F) (Point (normalizerSpanMarking F)) :=
  system_of_generation (normalizerSpanMarking F) (normalizerSpanLocalData F D)
    (normalizerSpan_pair_generate F D)

/-- The internal system retains the original coset collinearity and the exact
normalizers under the inclusion into G. -/
theorem normalizerSpan_system_geometry :
    (normalizerSpan_system F D).graph = graph (normalizerSpanMarking F) ∧
    ((normalizerSpan_system F D).vertexGroup).map (normalizerSpan F).subtype =
      rowNormalizer F ∧
    ((normalizerSpan_system F D).H).map (normalizerSpan F).subtype =
      threeSpaceNormalizer F := by
  refine ⟨rfl, ?_, (normalizerSpan_normalizers_map F).2.2⟩
  change (MulAction.stabilizer (normalizerSpan F)
    (vertex (rowNormalizer (normalizerSpanMarking F)) 1)).map _ = _
  rw [stabilizer_base]
  exact (normalizerSpan_normalizers_map F).1

/-- Native recognition in the generated subgroup: construction of a compatible
similarity is the remaining comparison input; no simplicity or generation
premise on that subgroup is hidden. -/
theorem normalizerSpan_existsUnique_mulEquiv_of_similarity
    (s : Similarity (normalizerSpan_system F D)
      Sporadic.Mathieu.M24LocalGeometry.OctadGraph.system) :
    ∃! e : normalizerSpan F ≃* Sporadic.Mathieu.M24,
      (∀ a : (normalizerSpan_system F D).vertexGroup,
        e a = (s.vertexIso a : Sporadic.Mathieu.M24)) ∧
      (∀ a : (normalizerSpan_system F D).H,
        e a = (s.localIso a : Sporadic.Mathieu.M24)) := by
  apply Sporadic.Mathieu.M24LocalGeometry.OctadGraph.existsUnique_mulEquiv_of_rigid s
  exact edge_plane_automorphismRigid (normalizerSpanMarking F) (normalizerSpanLocalData F D)

/-- Original-fusion application: the completed normalizer producer gives a
complete system in the correctly oriented source span, with no extra inputs. -/
def oriented_normalizerSpan_system (hfusion : F.MathieuFusion) :
    let E := SourceData.ofFusion F hfusion
    System (normalizerSpan E.oriented.marking)
      (Point (normalizerSpanMarking E.oriented.marking)) :=
  let E := SourceData.ofFusion F hfusion
  normalizerSpan_system E.oriented.marking E.localData

/-- The exact consumer of the local comparison in source 41.1, using the
same orientation and local data from the original fusion construction. -/
theorem oriented_normalizerSpan_recognition (hfusion : F.MathieuFusion)
    (s : Similarity (oriented_normalizerSpan_system F hfusion)
      Sporadic.Mathieu.M24LocalGeometry.OctadGraph.system) :
    Nonempty (normalizerSpan (SourceData.ofFusion F hfusion).oriented.marking ≃*
      Sporadic.Mathieu.M24) := by
  let E := SourceData.ofFusion F hfusion
  obtain ⟨e, _, _⟩ := normalizerSpan_existsUnique_mulEquiv_of_similarity
    E.oriented.marking E.localData s
  exact ⟨e⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
