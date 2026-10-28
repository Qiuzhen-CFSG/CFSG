/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Graphs/TransitiveStronglyRegular.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# CommonNeighborsEquiv

Common-neighbor sets transport along graph isomorphisms.
Restricting the vertex equivalence preserves both adjacency conditions.

Source: Gerald Höhn, ATLAS, `Atlas/Graphs/TransitiveStronglyRegular.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
namespace Atlas.Graphs

/-- Common-neighbor sets transport under the actual graph equivalence. -/
def commonNeighborsEquiv {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W}
    (e : A ≃g B) (x y : V) : A.commonNeighbors x y ≃ B.commonNeighbors (e x) (e y) :=
  e.toEquiv.subtypeEquiv (fun z => by
    change (A.Adj x z ∧ A.Adj y z) ↔ (B.Adj (e x) (e z) ∧ B.Adj (e y) (e z))
    exact and_congr e.map_adj_iff.symm e.map_adj_iff.symm)

end Atlas.Graphs
