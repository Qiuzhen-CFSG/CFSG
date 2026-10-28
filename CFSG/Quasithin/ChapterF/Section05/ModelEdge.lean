module
public import CFSG.Quasithin.ChapterF.Section05.ModelLocal
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.EdgeMarks

/-!
# The concrete edge inputs for the F.5 similarity

The model edge fixer is the graph-involution centralizer within the first
vertex group. Its transport theorem retains the actual vertex isomorphism and
source centralizer, giving the model edge input for the amalgam comparison.
The fixed local reversal swaps the two endpoints and squares to the same graph
involution. It supplies the local-orbit choice used by `SourceSystemLocalOrbit`.

Source: Aschbacher--Smith F.5.7, printed p.303.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Theory.GroupTheory.GraphUniquenessSystem
open OmegaSixThree OrthogonalityGraph TriangleLocal SixTernaryCoordinates

/-- The model edge fixer is the graph-involution centralizer inside its vertex. -/
theorem modelEdge_eq_vertex_inf_graph_centralizer : modelSystem.edgeGroup =
    modelSystem.vertexGroup ⊓ Subgroup.centralizer ({vertexGraphInvolution} : Set omegaPlusSixThree) :=
  edgeFixer_eq_vertex_inf_graph_centralizer

/-- The source graph involution retains its literal vertex-subgroup embedding. -/
def modelGraphElement : modelSystem.vertexGroup := ⟨vertexGraphInvolution,by
  apply (point_eq_iff _ _ _ _).mpr
  exact Or.inr (by decide +kernel)⟩

theorem modelEdge_iff_commutes (a : modelSystem.vertexGroup) :
    (a : omegaPlusSixThree) ∈ modelSystem.edgeGroup ↔
      a * modelGraphElement = modelGraphElement * a := by
  rw [modelEdge_eq_vertex_inf_graph_centralizer]
  change (a.val ∈ modelSystem.vertexGroup ∧
    a.val ∈ Subgroup.centralizer ({vertexGraphInvolution} : Set omegaPlusSixThree)) ↔ _
  rw [and_iff_right a.property,Subgroup.mem_centralizer_singleton_iff]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

/-- A graph-marked vertex comparison transports the edge criterion to the
actual source graph-involution centralizer. No source coset action is required. -/
theorem modelEdge_iff_image_commutes {G : Type*} [Group G]
    (M : Subgroup G) (eV : modelSystem.vertexGroup ≃* M) (f : G)
    (hf : (eV modelGraphElement : G) = f) (a : modelSystem.vertexGroup) :
    (a : omegaPlusSixThree) ∈ modelSystem.edgeGroup ↔
      (eV a : G) * f = f * (eV a : G) := by
  rw [modelEdge_iff_commutes,←hf]
  constructor
  · intro h
    exact congrArg Subtype.val (by simpa only [map_mul] using congrArg eV h)
  · intro h
    apply eV.injective
    simpa only [map_mul] using (Subtype.ext h : eV a * eV modelGraphElement =
      eV modelGraphElement * eV a)

/-- When a source intersection is already marked, the same criterion supplies
its full edge-fixer field with the original vertex inclusions. -/
theorem modelEdge_iff_source_intersection {G : Type*} [Group G]
    (M B : Subgroup G) (eV : modelSystem.vertexGroup ≃* M) (f : G)
    (hf : (eV modelGraphElement : G) = f)
    (hB : B = M ⊓ Subgroup.centralizer ({f} : Set G))
    (a : modelSystem.vertexGroup) :
    (a : omegaPlusSixThree) ∈ modelSystem.edgeGroup ↔ (eV a : G) ∈ B := by
  rw [modelEdge_iff_image_commutes M eV f hf,hB]
  change _ ↔ (eV a).val ∈ M ∧ (eV a).val ∈ Subgroup.centralizer ({f} : Set G)
  rw [and_iff_right (eV a).property,Subgroup.mem_centralizer_singleton_iff]

noncomputable def modelEdgeReversal : modelSystem.H := edgeReversal

theorem modelEdgeReversal_first : (modelEdgeReversal : omegaPlusSixThree) • modelSystem.x =
    modelSystem.y := edgeReversal_first

theorem modelEdgeReversal_second : (modelEdgeReversal : omegaPlusSixThree) • modelSystem.y =
    modelSystem.x := edgeReversal_second

theorem modelEdgeReversal_square : (modelEdgeReversal : omegaPlusSixThree)^2 =
    vertexGraphInvolution := congrArg Subtype.val edgeReversal_sq

theorem modelEdgeReversal_image : productEquiv modelEdgeReversal =
    (reversalPermutation,1) := edgeReversal_image

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
