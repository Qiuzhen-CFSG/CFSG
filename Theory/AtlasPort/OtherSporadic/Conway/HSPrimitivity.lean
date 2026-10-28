/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSPrimitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSRankThree
public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity

/-!
Primitivity of the Higman–Sims graph action.
Block divisibility excludes every nontrivial sum of the subdegrees 1, 22, and 77.

Source: Gerald Höhn, `Atlas/Conway/HSPrimitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Only the singleton and whole set pass block divisibility among the local suborbit sums. -/
theorem hs_block_divisibility (T : Finset (Fin 3)) (h0 : 0 ∈ T)
    (hd : (∑ i ∈ T,hsSubdegree i) ∣ 100) :
    (∑ i ∈ T,hsSubdegree i) = 1 ∨ (∑ i ∈ T,hsSubdegree i) = 100 := by
  revert hd h0 T
  decide +kernel

theorem hs_graph_primitive : IsPreprimitive HSModel HSGraphPoints := by
  let := hs_graph_transitive
  apply Atlas.GroupTheory.primitive_of_suborbit_sums hsBaseGraphPoint hsLocalFamily
    hs_local_family_transitive hsSubdegree hs_local_fiber_card
  intro T ha hd
  have h0 : (0 : Fin 3) ∈ T := by
    change hsLocalFamily (hsWittGraphMap (Sum.inl ())) ∈ T at ha
    rwa [hs_local_family_witt] at ha
  rw [hs_graph_card] at hd ⊢
  exact hs_block_divisibility T h0 hd

end Atlas.Conway
