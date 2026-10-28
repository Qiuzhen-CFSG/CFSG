/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLGraph.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLWittVertices
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
The McLaughlin graph defined by inner product eight.
Its Witt-label presentation translates adjacency to membership and intersection
conditions on points and heptads; lattice isometries preserve adjacency.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLGraph.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- The graph uses the actual lattice inner product, scaled by eight. -/
def mclGraph : SimpleGraph McLGraphPoints where
  Adj y z := integerDot y.val.val z.val.val = 8
  symm := ⟨by intro y z h; rwa [integerDot_comm]⟩
  loopless := ⟨by intro y h; have hy := y.prop.1; omega⟩

def mclWittGraph : SimpleGraph McLWittVertices := mclGraph.comap mclWittVector

def mclWittGraphEquiv : mclWittGraph ≃g mclGraph where
  toEquiv := mclWittGraphVertexEquiv
  map_rel_iff' := Iff.rfl

theorem mcl_graph_action_preserves (g : McLModel) (y z : McLGraphPoints) :
    mclGraph.Adj (g • y) (g • z) ↔ mclGraph.Adj y z := by
  change integerDot (g.val.val.val y.val).val (g.val.val.val z.val).val = 8 ↔ _
  rw [g.val.val.prop]
  rfl

theorem mcl_witt_points_nonadjacent (c d : McLPointLabels) :
    ¬mclWittGraph.Adj (Sum.inl c) (Sum.inl d) := by
  by_cases he : c = d
  · subst d; exact mclWittGraph.loopless.irrefl _
  · change integerDot (minimumPairPlus co3MarkedCoordinate c.val.val).val
      (minimumPairPlus co3MarkedCoordinate d.val.val).val ≠ 8
    rw [co3_point_pair_dot _ _ _ c.val.prop d.val.prop (by
      intro h; exact he (Subtype.ext (Subtype.ext h)))]
    decide

theorem mcl_witt_point_through (c : McLPointLabels) (B : McLThroughLabels) :
    mclWittGraph.Adj (Sum.inl c) (Sum.inr (Sum.inl B)) ↔ c.val ∉ B.val.val := by
  change integerDot (minimumPairPlus co3MarkedCoordinate c.val.val).val
    (co3HeptadEndpoint _ B.val).val = 8 ↔ _
  rw [co3Point_heptad_dot]
  split_ifs <;> simp_all

theorem mcl_witt_point_avoiding (c : McLPointLabels) (B : McLAvoidingLabels) :
    mclWittGraph.Adj (Sum.inl c) (Sum.inr (Sum.inr B)) ↔ c.val ∈ B.val.val := by
  change integerDot (minimumPairPlus co3MarkedCoordinate c.val.val).val
    (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val).val = 8 ↔ _
  rw [co3Point_heptad_complement_dot]
  split_ifs <;> simp_all

theorem mcl_witt_through_through (B C : McLThroughLabels) :
    mclWittGraph.Adj (Sum.inr (Sum.inl B)) (Sum.inr (Sum.inl C)) ↔
      (B.val.val ∩ C.val.val).card = 1 := by
  change integerDot (co3HeptadEndpoint _ B.val).val (co3HeptadEndpoint _ C.val).val = 8 ↔ _
  rw [co3Heptad_dot]
  omega

theorem mcl_witt_through_avoiding (B : McLThroughLabels) (C : McLAvoidingLabels) :
    mclWittGraph.Adj (Sum.inr (Sum.inl B)) (Sum.inr (Sum.inr C)) ↔
      (B.val.val ∩ C.val.val).card = 3 := by
  change integerDot (co3HeptadEndpoint _ B.val).val
    (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ C.val).val = 8 ↔ _
  rw [integerDot_comm,co3Heptad_complement_dot,Finset.inter_comm]
  omega

theorem mcl_witt_avoiding_avoiding (B C : McLAvoidingLabels) :
    mclWittGraph.Adj (Sum.inr (Sum.inr B)) (Sum.inr (Sum.inr C)) ↔
      (B.val.val ∩ C.val.val).card = 1 := by
  change integerDot ((normSixVector co3MarkedCoordinate).val-(co3HeptadEndpoint _ B.val).val)
    ((normSixVector co3MarkedCoordinate).val-(co3HeptadEndpoint _ C.val).val) = 8 ↔ _
  rw [integerDot_sub_left,integerDot_sub_right,integerDot_sub_right,
    normSixVector_norm,co3NormSix_heptad_dot,integerDot_comm (co3HeptadEndpoint _ B.val).val,
    co3NormSix_heptad_dot,co3Heptad_dot]
  omega

end Atlas.Conway
