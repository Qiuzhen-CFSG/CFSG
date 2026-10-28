module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.EdgeMarks
public import Theory.SpecificGroups.OmegaSixThree.VertexCardinality
/-!
# The marked vertex graph centralizer has order1440

The coordinate point list has exactly36 neighbors of the standard vertex.
Ordered edge transitivity and orbit-stabilizer therefore give an edge fixer
of order1440. The literal graph-involution mark identifies this edge fixer
with its centralizer in the vertex group. In particular its two-part is32.

Source: Aschbacher--Smith F.5.1 and F.5.7, printed pp.300 and303.
-/

open Subgroup SixTernaryCoordinates
open Theory.GroupTheory.GraphUniquenessSystem
namespace OmegaSixThree
open OrthogonalityGraph
public noncomputable section
local notation "V" => MulAction.stabilizer omegaPlusSixThree standardFirst

theorem standardFirst_eq_coordinatePoint_zero : standardFirst = coordinatePoint 0 := by
  apply (point_eq_iff _ _ _ _).mpr
  left
  decide +kernel

def neighborCoordinateEquiv :
    {i : Fin 117 // (Certificate.rows 0).getLsbD i = true} ≃
      {a : Point // graph.Adj standardFirst a} :=
  Equiv.ofBijective (fun i => ⟨coordinatePoint i.val,by
    rw [standardFirst_eq_coordinatePoint_zero,adj_coordinatePoint_iff]
    exact i.property⟩) ⟨by
      intro i j he
      exact Subtype.ext (coordinatePoint_injective (congrArg Subtype.val he)),by
      intro a
      obtain ⟨i,hi⟩ := coordinatePoint_surjective a.val
      refine ⟨⟨i,?_⟩,Subtype.ext hi⟩
      rw [←adj_coordinatePoint_iff,←standardFirst_eq_coordinatePoint_zero,hi]
      exact a.property⟩

theorem card_standard_neighbors : Nat.card {a : Point // graph.Adj standardFirst a} = 36 := by
  rw [←Nat.card_congr neighborCoordinateEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def vertexOrbitNeighborEquiv : MulAction.orbit V standardSecond ≃
    {a : Point // graph.Adj standardFirst a} :=
  Equiv.ofBijective (fun a => ⟨a.val,by
    obtain ⟨g,hg⟩ := a.property
    have h := omega_preserves g.val standard_adjacent.1
    have hx : g.val • standardFirst = standardFirst := g.property
    change g.val • standardSecond = a.val at hg
    simpa only [hx,hg] using h⟩) ⟨by
      intro a b h
      exact Subtype.ext (congrArg (fun x : {a : Point // graph.Adj standardFirst a} => x.val) h),by
      intro a
      obtain ⟨g,hgx,hgy⟩ := ordered_edge_transitive standardFirst a.val a.property
      exact ⟨⟨a.val,⟨⟨g,hgx⟩,hgy⟩⟩,rfl⟩⟩

theorem card_vertex_second_stabilizer : Nat.card (MulAction.stabilizer V standardSecond) = 1440 := by
  have ho : Nat.card (MulAction.orbit V standardSecond)=36 :=
    (Nat.card_congr vertexOrbitNeighborEquiv).trans card_standard_neighbors
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup V standardSecond)
  rw [Nat.card_prod,ho,card_standard_vertex] at hh
  omega

@[expose] def vertexGraphElement : V := ⟨vertexGraphInvolution,by
  apply (point_eq_iff _ _ _ _).mpr
  right
  decide +kernel⟩

@[simp] theorem vertexGraphElement_val : vertexGraphElement.val = vertexGraphInvolution := rfl

theorem vertex_graph_centralizer_eq :
    centralizer ({vertexGraphElement} : Set V) = MulAction.stabilizer V standardSecond := by
  ext g
  rw [mem_centralizer_singleton_iff]
  change g*vertexGraphElement=vertexGraphElement*g ↔ g.val • standardSecond=standardSecond
  have he := TriangleLocal.edgeFixer_eq_vertex_inf_graph_centralizer
  constructor
  · intro hg
    have hm : g.val ∈ V ⊓ centralizer ({vertexGraphInvolution} : Set omegaPlusSixThree) :=
      ⟨g.property,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg)⟩
    rw [←he] at hm
    exact hm.2
  · intro hg
    have hm : g.val ∈ edgeFixer omegaPlusSixThree standardFirst standardSecond := ⟨g.property,hg⟩
    rw [he] at hm
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hm.2)

theorem card_vertex_graph_centralizer : Nat.card (centralizer ({vertexGraphElement} : Set V))=1440 := by
  rw [vertex_graph_centralizer_eq,card_vertex_second_stabilizer]
end
end OmegaSixThree
