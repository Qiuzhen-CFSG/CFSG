/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLStronglyRegular.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLCommonNeighbors
public import Theory.AtlasPort.OtherSporadic.Graphs.TransitiveStronglyRegular

/-!
Strong regularity of the McLaughlin graph with parameters (275,112,30,56).
The transitive isometry action transports the point-family neighbor and
common-neighbor counts to every vertex.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLStronglyRegular.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

instance mclGraphPointsFinite : Finite McLGraphPoints := Nat.finite_of_card_ne_zero (by rw [mcl_graph_card]; decide)
instance mclGraphPointsFintype : Fintype McLGraphPoints := Fintype.ofFinite _

def mclBaseGraphLabel : McLPointLabels := ⟨⟨((0,0),2),by change ((0,0),2) ≠ co3MarkedCoordinate; decide⟩,by decide⟩
def mclBaseGraphPoint : McLGraphPoints := mclWittVector (Sum.inl mclBaseGraphLabel)

theorem mcl_graph_strongly_regular : mclGraph.IsSRGWith 275 112 30 56 := by
  let := mcl_graph_transitive
  apply Atlas.Graphs.srg_of_transitive_base_counts (G := McLModel) mclGraph
    mcl_graph_action_preserves mclBaseGraphPoint 275 112 30 56 mcl_graph_card
  · have he := Nat.card_congr (mclWittGraphEquiv.mapNeighborSet (Sum.inl mclBaseGraphLabel))
    exact he.symm.trans (mcl_witt_point_neighbor_card _)
  · intro y hy
    obtain ⟨v,rfl⟩ := mclWittVector_surjective y
    have he := Nat.card_congr (Atlas.Graphs.commonNeighborsEquiv mclWittGraphEquiv
      (Sum.inl mclBaseGraphLabel) v)
    apply he.symm.trans
    change Nat.card {w : McLWittVertices // mclWittGraph.Adj (Sum.inl mclBaseGraphLabel) w ∧
      mclWittGraph.Adj v w} = _
    have ha : mclWittGraph.Adj (Sum.inl mclBaseGraphLabel) v := hy
    cases v with
    | inl c => exact False.elim (mcl_witt_points_nonadjacent _ _ ha)
    | inr D =>
      cases D with
      | inl D =>
        have hn := (mcl_witt_point_through _ _).mp ha
        simpa only [if_neg hn] using mcl_common_point_through mclBaseGraphLabel D
      | inr D =>
        have hn := (mcl_witt_point_avoiding _ _).mp ha
        simpa only [if_pos hn] using mcl_common_point_avoiding mclBaseGraphLabel D
  · intro y hne hy
    obtain ⟨v,rfl⟩ := mclWittVector_surjective y
    have he := Nat.card_congr (Atlas.Graphs.commonNeighborsEquiv mclWittGraphEquiv
      (Sum.inl mclBaseGraphLabel) v)
    apply he.symm.trans
    change Nat.card {w : McLWittVertices // mclWittGraph.Adj (Sum.inl mclBaseGraphLabel) w ∧
      mclWittGraph.Adj v w} = _
    have ha : ¬mclWittGraph.Adj (Sum.inl mclBaseGraphLabel) v := hy
    cases v with
    | inl c =>
      apply mcl_common_point_point
      intro h; exact hne (congrArg (fun c => mclWittVector (Sum.inl c)) h)
    | inr D =>
      cases D with
      | inl D =>
        have hn : mclBaseGraphLabel.val ∈ D.val.val := by
          by_contra hn; exact ha ((mcl_witt_point_through _ _).mpr hn)
        simpa only [if_pos hn] using mcl_common_point_through mclBaseGraphLabel D
      | inr D =>
        have hn : mclBaseGraphLabel.val ∉ D.val.val := fun hn => ha ((mcl_witt_point_avoiding _ _).mpr hn)
        simpa only [if_neg hn] using mcl_common_point_avoiding mclBaseGraphLabel D

end Atlas.Conway
