/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolaySmallSetFixing

/-!
# GolayMarkedOctadTransitivity

Octads containing a fixed marked set of at most five points can be transported while
fixing that set pointwise. Extend the marked set to five points in each octad and use
the unique octad completion of a five-set.

Source: `Atlas/Mathieu/GolayMarkedOctadTransitivity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem mathieu24_marked_octad_transitive (A O P : Finset Omega)
    (hA : A.card ≤ 5) (hO : O ∈ octads) (hP : P ∈ octads)
    (hAO : A ⊆ O) (hAP : A ⊆ P) :
    ∃ g : Mathieu24CodeModel, (∀ a ∈ A, g.val a = a) ∧ permuteBlock g.val O = P := by
  have hnO : 5 - A.card ≤ (O \ A).card := by
    rw [Finset.card_sdiff_of_subset hAO,octad_size O hO]
    omega
  have hnP : 5 - A.card ≤ (P \ A).card := by
    rw [Finset.card_sdiff_of_subset hAP,octad_size P hP]
    omega
  obtain ⟨S,hSO,hS⟩ := Finset.exists_subset_card_eq hnO
  obtain ⟨T,hTP,hT⟩ := Finset.exists_subset_card_eq hnP
  have hAS : Disjoint A S := Finset.disjoint_left.mpr (fun a ha hs =>
    (Finset.mem_sdiff.mp (hSO hs)).2 ha)
  have hAT : Disjoint A T := Finset.disjoint_left.mpr (fun a ha ht =>
    (Finset.mem_sdiff.mp (hTP ht)).2 ha)
  obtain ⟨g,hgA,hg⟩ := mathieu24_fixing_small_set_transitive A S T (5-A.card)
    hAS hAT hS hT (by omega)
  refine ⟨g,hgA,?_⟩
  apply octad_unique_on_five (A ∪ T) _ P
  · rw [Finset.card_union_of_disjoint hAT,hT]
    omega
  · exact (codePreserving_octadPreserving g.val g.prop O).mp hO
  · exact hP
  · apply Finset.union_subset
    · intro a ha
      exact Finset.mem_image.mpr ⟨a,hAO ha,hgA a ha⟩
    · rw [← hg]
      exact Finset.image_subset_image (hSO.trans Finset.sdiff_subset)
  · exact Finset.union_subset hAP (hTP.trans Finset.sdiff_subset)

end Atlas.Codes
