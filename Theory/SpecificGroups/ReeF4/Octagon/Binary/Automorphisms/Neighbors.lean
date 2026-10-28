module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Neighbors.Checks
public import Mathlib.Data.List.Nodup

/-!
# Certified neighbor lists for the binary Ree incidence graph

The finite row certificate supplies the actual neighbor lists, without duplicates.
This identifies the arithmetic color signature with the graph-invariant signature
used in the rigidity argument for Aschbacher--Smith J.5.6.
-/

@[expose] public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteGraph
open SimpleGraph.ColorRefinement

def neighborVertices (i : Vertex) : List Vertex :=
  (adjacency i.val).attach.map (fun j => ⟨j.val, ((row_valid i).2 j.val j.property).1⟩)

theorem neighborVertices_nodup (i : Vertex) : (neighborVertices i).Nodup := by
  apply (row_valid i).1.attach.map
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun v : Vertex => v.val) hab

theorem mem_neighborVertices (i j : Vertex) :
    j ∈ neighborVertices i ↔ j.val ∈ adjacency i.val := by
  unfold neighborVertices
  rw [List.mem_map]
  constructor
  · rintro ⟨x,_,he⟩
    have hx : x.val=j.val := congrArg (fun v : Vertex => v.val) he
    exact hx ▸ x.property
  · intro hj
    exact ⟨⟨j.val,hj⟩, List.mem_attach _ _, Fin.ext rfl⟩

theorem mem_adjacency_iff_adj (i j : Vertex) :
    j.val ∈ adjacency i.val ↔ graph.Adj i j := by
  change _ ↔ ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _))
  constructor
  · intro h
    have hv := (row_valid i).2 j.val h
    rcases hv.2.1 with ht | ht
    · exact Or.inl ⟨ht.1,ht.2,hv.2.2⟩
    · exact Or.inr ⟨ht.1,ht.2,h⟩
  · intro h
    rcases h with h | h
    · exact ((row_valid j).2 i.val h.2.2).2.2
    · exact h.2.2

def neighborLists : NeighborLists graph where
  neighbors := neighborVertices
  nodup := neighborVertices_nodup
  mem_iff i j := (mem_neighborVertices i j).trans (mem_adjacency_iff_adj i j)

theorem rawSignature_eq_signature (c : ℕ → ℕ) (i : Vertex) :
    Refinement.rawSignature c i.val =
      signature neighborLists (fun v => c v.val) i := by
  unfold Refinement.rawSignature signature neighborLists neighborVertices
  simp only [List.map_map,Function.comp_def]
  exact congrArg (fun t : List ℕ => c i.val+1+8192*t.sum)
    (List.attach_map_val (l := adjacency i.val) (f := fun j => moment (c j))).symm
end ReeF4.Octagon.Binary.Automorphisms.FiniteGraph
