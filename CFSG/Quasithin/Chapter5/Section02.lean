module

public import Theory.Combinatorics.PairGraphLocalGeometry

/-!
# Using weak BN-pairs and the Green Book

Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.2,
Theorems 5.2.9 and 5.2.10, printed pp.646--658 of the combined 1 March 2004
manuscript. Theorem 5.2.3 is stated here and completed in §5.3.

The graph used to recognize M23 has as vertices the unordered pairs of its
23-point permutation domain; two vertices are adjacent when they meet in one
point. The imported local geometry supplies the diameter, square, pentagon,
and triangle-support calculations at the end of the proof of Theorem 5.2.10.
The amalgam alternatives and the recognition theorem still require the
group-theoretic reductions and uniqueness-system argument.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter5.Section02

open Theory.Combinatorics.PairGraph

/-- The graph Γ on unordered pairs from the natural domain of M23. -/
abbrev recognitionGraph : SimpleGraph (Vertex (Fin 23)) := graph (Fin 23)

/-- The source definition of adjacency in Γ. -/
theorem recognitionGraph_adj_iff (s t : Vertex (Fin 23)) :
    recognitionGraph.Adj s t ↔ (s.val ∩ t.val).card = 1 :=
  adj_iff_card_inter s t

/-- The recognition graph is connected. -/
theorem recognitionGraph_connected : recognitionGraph.Connected where
  preconnected := preconnected
  nonempty := ⟨pair 0 1 (by decide)⟩

end CFSG.Quasithin.Chapter5.Section02
