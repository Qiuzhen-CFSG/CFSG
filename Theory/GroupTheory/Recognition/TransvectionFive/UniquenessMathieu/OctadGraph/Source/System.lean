module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgeRigidity
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneAction
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Recognition

/-!
# The literal Mathieu source system and its rigidity consumer

Use the original cosets G/N_G(U₁), source collinearity, and N_G(A₂) as
the local group. The local generation identities and the faithful action
supply a uniqueness system once global source generation is proved.
The actual edge-intersection rigidity discharges Theorem 37.9, so a
similarity with the native octad system suffices for unique recognition
with both prescribed local restrictions retained.

This is a conditional assembly for Aschbacher, *Sporadic Groups* (1994),
41.1–41.5, pp.219–222. The global-generation input and construction of the
similarity are still mathematical obligations; this module does not assert
the final source comparison or source uniqueness theorem.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- The source uniqueness system on the literal cosets G/N_G(U₁).
The global-generation premise is the still separate §41.1–41.2 obligation. -/
@[expose] def system (hG : IsSimpleGroup G) (hcore : PointCoreFusion z)
    (hgenerate : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤) : System G (Point F) where
  graph := graph F
  H := threeSpaceNormalizer F
  x := vertex (rowNormalizer F) 1
  y := vertex (rowNormalizer F) (lineSwap F D : G)
  adjacent := graph_adj_base F D
  preserves := graph_preserves F
  faithful := graph_faithful F hG hcore
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

variable (hG : IsSimpleGroup G) (hcore : PointCoreFusion z)
  (hgenerate : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤)

/-- The source system retains the literal point, line and plane marking. -/
theorem system_vertexGroup : (system F D hG hcore hgenerate).vertexGroup = rowNormalizer F :=
  stabilizer_base _

/-- Rigidity is proved for the actual local intersection of the source system. -/
theorem system_edge_rigid :
    AutomorphismRigid ((system F D hG hcore hgenerate).H.subgroupOf
      (system F D hG hcore hgenerate).edgeGroup) :=
  edge_plane_automorphismRigid F D

/-- A similarity of the literal source system with the native octad system
is an equivalence; no additional rigidity hypothesis is required. -/
theorem isEquivalence_of_similarity
    (s : Similarity (system F D hG hcore hgenerate)
      Sporadic.Mathieu.M24LocalGeometry.OctadGraph.system) : s.IsEquivalence :=
  s.isEquivalence_of_rigid (system_edge_rigid F D hG hcore hgenerate)

/-- The general recognition consumer, retaining both prescribed local maps.
Global source generation and construction of the similarity remain open inputs. -/
theorem existsUnique_mulEquiv_of_similarity
    (s : Similarity (system F D hG hcore hgenerate)
      Sporadic.Mathieu.M24LocalGeometry.OctadGraph.system) :
    ∃! e : G ≃* Sporadic.Mathieu.M24,
      (∀ a : (system F D hG hcore hgenerate).vertexGroup,
        e a = (s.vertexIso a : Sporadic.Mathieu.M24)) ∧
      (∀ a : (system F D hG hcore hgenerate).H,
        e a = (s.localIso a : Sporadic.Mathieu.M24)) :=
  Sporadic.Mathieu.M24LocalGeometry.OctadGraph.existsUnique_mulEquiv_of_equivalence s
    (isEquivalence_of_similarity F D hG hcore hgenerate s)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
