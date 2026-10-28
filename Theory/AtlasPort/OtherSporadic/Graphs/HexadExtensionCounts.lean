/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Graphs/HexadExtensionRegular.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Graphs.HexadExtensionGraph

/-!
# HexadExtensionCounts

A hexad extension has 100 vertices. Distinct vertices have no common
neighbors when adjacent and six when nonadjacent. The proof splits the
vertices into the base, point, and hexad cases and applies the corresponding
incidence counts from HexadExtensionGraph.

Source: Gerald Höhn, ATLAS, `Atlas/Graphs/HexadExtensionRegular.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
The common-neighbor count is split from the strongly regular wrapper so this
counting interface depends only on the graph construction. The vertex count
follows from the disjoint union of the base vertex, points, and hexads.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Graphs
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem hexad_extension_common_card (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (x y : HexadExtensionVertices blocks) (hxy : x ≠ y) :
    Nat.card {z // (hexadExtensionGraph blocks h).Adj x z ∧
      (hexadExtensionGraph blocks h).Adj y z} =
      if (hexadExtensionGraph blocks h).Adj x y then 0 else 6 := by
  have hs (x y : HexadExtensionVertices blocks) :
      Nat.card {z // (hexadExtensionGraph blocks h).Adj x z ∧
        (hexadExtensionGraph blocks h).Adj y z} =
      Nat.card {z // (hexadExtensionGraph blocks h).Adj y z ∧
        (hexadExtensionGraph blocks h).Adj x z} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  · exact False.elim (hxy rfl)
  · exact hexad_extension_base_common blocks h _ (by simp)
  · exact hexad_extension_base_common blocks h _ (by simp)
  · rw [hs]
    exact hexad_extension_base_common blocks h _ (by simp)
  · simpa only [hexadExtensionGraph,hexadExtensionAdj,if_false] using hexad_extension_points_common blocks h x y (fun he => hxy (congrArg (fun t => Sum.inr (Sum.inl t)) he))
  · convert hexad_extension_point_block_common blocks h x y using 1
    split_ifs <;> simp_all only [hexadExtensionGraph,hexadExtensionAdj,not_true_eq_false]
  · rw [hs]
    exact hexad_extension_base_common blocks h _ (by simp)
  · rw [hs]
    convert hexad_extension_point_block_common blocks h y x using 1
    split_ifs <;> simp_all only [hexadExtensionGraph,hexadExtensionAdj,not_true_eq_false]
  · convert hexad_extension_blocks_common blocks h x y (fun he => hxy (congrArg (fun t => Sum.inr (Sum.inr t)) he)) using 1
    split_ifs <;> simp_all only [hexadExtensionGraph,hexadExtensionAdj,not_true_eq_false]

/-- The extension has one base vertex, 22 points, and 77 hexads. -/
theorem hexad_extension_card (blocks : Finset (Finset V))
    (h : HexadDesignData blocks) (hv : Nat.card V = 22) :
    Nat.card (HexadExtensionVertices blocks) = 100 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_coe, ← Nat.card_eq_fintype_card, hv, h.card]

end Atlas.Graphs
