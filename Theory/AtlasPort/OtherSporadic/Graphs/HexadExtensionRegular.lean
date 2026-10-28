/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Graphs/HexadExtensionRegular.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Graphs.HexadExtensionCounts
public import Theory.AtlasPort.OtherSporadic.Graphs.TransitiveStronglyRegular

/-!
# HexadExtensionRegular

The extension graph of a hexad design on 22 points is strongly regular with
parameters (100,22,0,6). The vertex, neighbor and common-neighbor counts supply
the four clauses of strong regularity directly.

Source: Gerald Höhn, ATLAS, `Atlas/Graphs/HexadExtensionRegular.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
The counting proofs are re-exported from `HexadExtensionCounts` so they remain
available independently of the strongly regular graph API.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Graphs
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem hexad_extension_strongly_regular (blocks : Finset (Finset V))
    (h : HexadDesignData blocks) (hv : Nat.card V = 22) :
    (hexadExtensionGraph blocks h).IsSRGWith 100 22 0 6 where
  card := by
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_unit,Fintype.card_coe,
      ← Nat.card_eq_fintype_card,hv,h.card]
  regular := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    exact hexad_extension_neighbor_card blocks h hv x
  of_adj := by
    intro x y hxy
    rw [← Nat.card_eq_fintype_card]
    exact (hexad_extension_common_card blocks h x y hxy.ne).trans (if_pos hxy)
  of_not_adj := by
    intro x y hne hxy
    rw [← Nat.card_eq_fintype_card]
    exact (hexad_extension_common_card blocks h x y hne).trans (if_neg hxy)

end Atlas.Graphs
