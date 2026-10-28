module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Tree

/-!
# The graph argument for a multiplicity-one Brauer block

A connected graph with n+1 vertices described by n pairs of distinct endpoints
has exactly n edges. Thus the pairs are distinct and the graph is a tree.
This proves the graph step of Feit VII.6.4 without assuming away parallel
columns in the decomposition matrix. The application to the module-valued
incidence data is in `ModuleTree.Assembly`.
-/

public section

open scoped Classical
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree

/-- Connectedness and the vertex count force both edge injectivity and acyclicity. -/
theorem endpointGraph_tree_of_connected {V : Type*} [Fintype V] {n : ℕ}
    (left right : Fin n → V) (hne : ∀ e, left e ≠ right e)
    (hconnected : (endpointGraph left right).Connected)
    (hcard : Fintype.card V = n + 1) :
    Function.Injective (fun e => s(left e, right e)) ∧
      (endpointGraph left right).IsTree := by
  let H := endpointGraph left right
  let edge : Fin n → H.edgeSet := fun e =>
    ⟨s(left e, right e), by
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨⟨e, rfl⟩, hne e⟩⟩
  have hsurj : Function.Surjective edge := by
    rintro ⟨q, hq⟩
    change q ∈ (SimpleGraph.fromEdgeSet _).edgeSet at hq
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hq
    obtain ⟨e, rfl⟩ := hq.1
    exact ⟨e, rfl⟩
  have hle := Fintype.card_le_of_surjective edge hsurj
  have hge := hconnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard] at hge
  simp only [Fintype.card_fin] at hle
  change n + 1 ≤ Fintype.card H.edgeSet + 1 at hge
  have hsize : Fintype.card H.edgeSet = n := by omega
  have hinj : Function.Injective edge :=
    (Fintype.bijective_iff_injective_and_card _).mp ?_ |>.1
  · refine ⟨?_, SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconnected, ?_⟩⟩
    · intro e f hef
      apply hinj
      exact Subtype.ext hef
    · simp only [Nat.card_eq_fintype_card]
      change Fintype.card H.edgeSet + 1 = Fintype.card V
      rw [hsize, hcard]
  · exact (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨hsurj, by simpa using hsize.symm⟩

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
