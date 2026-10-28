/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLGraphDistances.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLStronglyRegular

/-!
Distances and inner products in the 275-vertex Leech slice.
Transitivity reduces distinct-vector pairings to the Witt labels at a base
vertex; adjacency is equivalent to squared coordinate distance 48.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLGraphDistances.lean`, revision
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

theorem mcl_graph_base_dot_cases (w : McLWittVertices)
    (hne : mclBaseGraphPoint ≠ mclWittVector w) :
    integerDot mclBaseGraphPoint.val.val (mclWittVector w).val.val = 8 ∨
      integerDot mclBaseGraphPoint.val.val (mclWittVector w).val.val = 16 := by
  cases w with
  | inl c =>
    right
    apply co3_point_pair_dot _ _ _ mclBaseGraphLabel.val.prop c.val.prop
    intro h
    apply hne
    exact congrArg (fun c => mclWittVector (Sum.inl c)) (Subtype.ext (Subtype.ext h))
  | inr D =>
    cases D with
    | inl D =>
      change integerDot (minimumPairPlus _ _).val (co3HeptadEndpoint _ D.val).val = 8 ∨
        integerDot (minimumPairPlus co3MarkedCoordinate mclBaseGraphLabel.val.val).val (co3HeptadEndpoint _ D.val).val = 16
      rw [co3Point_heptad_dot]
      split_ifs <;> simp
    | inr D =>
      change integerDot (minimumPairPlus _ _).val (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ D.val).val = 8 ∨
        integerDot (minimumPairPlus co3MarkedCoordinate mclBaseGraphLabel.val.val).val (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ D.val).val = 16
      rw [co3Point_heptad_complement_dot]
      split_ifs <;> simp

theorem mcl_graph_dot_cases (y z : McLGraphPoints) (hne : y ≠ z) :
    integerDot y.val.val z.val.val = 8 ∨ integerDot y.val.val z.val.val = 16 := by
  let := mcl_graph_transitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq McLModel mclBaseGraphPoint y
  obtain ⟨w,hw⟩ := mclWittVector_surjective (g⁻¹ • z)
  have hgz : g • mclWittVector w = z := by rw [hw,smul_inv_smul]
  have hn : mclBaseGraphPoint ≠ mclWittVector w := by
    intro h
    exact hne (hg.symm.trans ((congrArg (fun v => g • v) h).trans hgz))
  have hd := g.val.val.prop mclBaseGraphPoint.val (mclWittVector w).val
  change integerDot (g • mclBaseGraphPoint).val.val (g • mclWittVector w).val.val = _ at hd
  rw [hg,hgz] at hd
  rw [hd]
  exact mcl_graph_base_dot_cases w hn

theorem mcl_graph_adj_distance (y z : McLGraphPoints) : mclGraph.Adj y z ↔
    integerDot (y.val-z.val).val (y.val-z.val).val = 48 := by
  rw [leech_norm_sub,y.prop.1,z.prop.1]
  change integerDot y.val.val z.val.val = 8 ↔ _
  omega

theorem mcl_graph_nonadjacent_dot (y z : McLGraphPoints) (hne : y ≠ z)
    (h : ¬mclGraph.Adj y z) : integerDot y.val.val z.val.val = 16 :=
  (mcl_graph_dot_cases y z hne).resolve_left h

end Atlas.Conway
