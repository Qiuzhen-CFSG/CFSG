/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Mathieu/HeptadTripleCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadPairCounts
public import Theory.AtlasPort.OtherSporadic.Combinatorics.SteinerTripleCount

/-!
The number of Mathieu23 heptads through three distinct points.
The Steiner triple-count identity specializes the established pair counts
and the design incidence parameters.

Source: Gerald Höhn, ATLAS, `Atlas/Mathieu/HeptadTripleCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable
local instance heptadTriplePointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem mathieu23Blocks_through_triple_card (a : Omega) (b c d : Mathieu23Points a)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ c ∈ B ∧ d ∈ B)).card = 5 := by
  have hv : Fintype.card (Mathieu23Points a) = 23 := by
    rw [← Nat.card_eq_fintype_card,mathieu23_degree]
  have hh := Atlas.Combinatorics.steiner_four_triple_count (mathieu23Blocks a)
    hv (mathieu23Blocks_size a) (mathieu23_steiner a) {b,c,d} (by simp [hbc,hbd,hcd])
  simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using hh

end Atlas.Codes
