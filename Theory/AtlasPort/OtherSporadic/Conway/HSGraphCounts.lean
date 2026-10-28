/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSStronglyRegular.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSHexadComparison
public import Theory.AtlasPort.OtherSporadic.Graphs.HexadExtensionCounts
public import Theory.AtlasPort.OtherSporadic.Graphs.CommonNeighborsEquiv

/-!
The concrete neighbor counts of the Higman–Sims graph.
The explicit graph isomorphism transports the hexad design counts to the lattice graph.
This separates the counting proof from the strongly regular API wrapper.

Source: Gerald Höhn, `Atlas/Conway/HSStronglyRegular.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics Atlas.Graphs
attribute [local instance] Classical.propDecidable
local instance hsGraphCountsPointLabelsFintype : Fintype HSPointLabels := Fintype.ofFinite _
instance hsGraphPointsFintype : Fintype HSGraphPoints := Fintype.ofFinite _

def hsWittHexadVertexEquiv : HSWittVertices ≃
    HexadExtensionVertices (mathieu22Blocks co3MarkedCoordinate co3BasePoint) :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr (Equiv.refl HSPointLabels) hsHexadLabelEquiv)

set_option maxHeartbeats 1000000 in
-- Comparing the nested derived-design subtypes requires additional elaboration.
def hsWittHexadGraphEquiv : hsWittGraph ≃g
    hexadExtensionGraph (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data where
  toEquiv := hsWittHexadVertexEquiv
  map_rel_iff' := by
    intro x y
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · exact iff_of_false (by simp [hexadExtensionGraph,hsWittHexadVertexEquiv])
        (hsWittGraph.loopless.irrefl _)
    · exact iff_of_true trivial (hs_witt_base_point y)
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (hs_witt_base_hexad y)
    · exact iff_of_true trivial (hs_witt_base_point x).symm
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (hs_witt_points_nonadjacent x y)
    · exact (hs_hexad_mem y x).trans (hs_witt_point_hexad x y).symm
    · exact iff_of_false (by simp [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv])
        (fun ha => hs_witt_base_hexad x ha.symm)
    · exact (hs_hexad_mem x y).trans ((hs_witt_point_hexad y x).symm.trans (hsWittGraph.adj_comm _ _))
    · simp only [hexadExtensionGraph,hexadExtensionAdj,hsWittHexadVertexEquiv,
        Equiv.sumCongr_apply,Sum.map_inr]
      rw [hs_hexads_disjoint_adjacent]
      simp only [Finset.card_eq_zero,Finset.disjoint_iff_inter_eq_empty]
      apply Iff.of_eq
      congr 1
      ext j
      simp only [Finset.mem_inter]

def hsHexadGraphEquiv : hsGraph ≃g
    hexadExtensionGraph (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data :=
  hsWittGraphEquiv.symm.trans hsWittHexadGraphEquiv

theorem hs_graph_neighbor_card (x : HSGraphPoints) :
    Nat.card (hsGraph.neighborSet x) = 22 := by
  rw [Nat.card_congr (hsHexadGraphEquiv.mapNeighborSet x)]
  exact hexad_extension_neighbor_card _ hs_hexad_design_data hs_point_labels_card _

theorem hs_graph_common_card (x y : HSGraphPoints) (hne : x ≠ y) :
    Nat.card (hsGraph.commonNeighbors x y) = if hsGraph.Adj x y then 0 else 6 := by
  rw [Nat.card_congr (commonNeighborsEquiv hsHexadGraphEquiv x y)]
  let Γ := hexadExtensionGraph (mathieu22Blocks co3MarkedCoordinate co3BasePoint)
    hs_hexad_design_data
  let e : Γ.commonNeighbors (hsHexadGraphEquiv x) (hsHexadGraphEquiv y) ≃
      {z // Γ.Adj (hsHexadGraphEquiv x) z ∧ Γ.Adj (hsHexadGraphEquiv y) z} :=
    Equiv.subtypeEquivRight (fun _ => Γ.mem_commonNeighbors)
  rw [Nat.card_congr e]
  have h := hexad_extension_common_card _ hs_hexad_design_data
    (hsHexadGraphEquiv x) (hsHexadGraphEquiv y)
    (fun he => hne (hsHexadGraphEquiv.injective he))
  simpa only [hsHexadGraphEquiv.map_rel_iff] using h

end Atlas.Conway
