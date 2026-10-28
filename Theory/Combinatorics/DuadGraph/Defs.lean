module

public import Theory.Combinatorics.PairGraphLocalGeometry
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Group.End

/-!
# The disjoint-duad graph on six points

The vertices are the existing unordered pairs of Fin 6. Adjacency means
disjointness, giving the Kneser graph KG(6,2); this differs from the intersecting
pair graph. Point stars are the five duads through one point.

Source application: the SRG(15,6,1,3) action in the U₄(3) recognition argument.
-/

@[expose] public section
namespace Theory.Combinatorics.DuadGraph
abbrev Vertex := PairGraph.Vertex (Fin 6)

def graph : SimpleGraph Vertex where
  Adj s t := Disjoint s.val t.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro s h
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property]; decide)
    exact Finset.disjoint_left.mp h ha ha⟩

@[simp] theorem adj_iff (s t : Vertex) : graph.Adj s t ↔ Disjoint s.val t.val := Iff.rfl

abbrev Aut := graph ≃g graph

def star (a : Fin 6) : Finset Vertex := Finset.univ.filter (fun s => a ∈ s.val)

@[simp] theorem mem_star (a : Fin 6) (s : Vertex) : s ∈ star a ↔ a ∈ s.val := by
  simp [star]
end Theory.Combinatorics.DuadGraph
