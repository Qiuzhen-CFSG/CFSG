/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSStronglyRegular.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSGraphCounts
public import Theory.AtlasPort.OtherSporadic.Graphs.HexadExtensionRegular

/-!
Strong regularity of the concrete Higman–Sims graph.
The graph isomorphism transports the hexad design counts to parameters (100,22,0,6).

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
theorem hs_graph_strongly_regular : hsGraph.IsSRGWith 100 22 0 6 := by
  have h := hexad_extension_strongly_regular
    (mathieu22Blocks co3MarkedCoordinate co3BasePoint) hs_hexad_design_data hs_point_labels_card
  refine ⟨?_,?_,?_,?_⟩
  · rw [← Nat.card_eq_fintype_card,hs_graph_card]
  · intro x
    rw [← hsHexadGraphEquiv.degree_eq x]
    exact h.regular _
  · intro x y hxy
    have he := Nat.card_congr (commonNeighborsEquiv hsHexadGraphEquiv x y)
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at he
    exact he.trans (h.of_adj _ _ (hsHexadGraphEquiv.map_rel_iff.mpr hxy))
  · intro x y hne hxy
    have he := Nat.card_congr (commonNeighborsEquiv hsHexadGraphEquiv x y)
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at he
    exact he.trans (h.of_not_adj (fun he => hne (hsHexadGraphEquiv.injective he))
      (fun ha => hxy (hsHexadGraphEquiv.map_rel_iff.mp ha)))

end Atlas.Conway
