/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24NotSixTransitive

/-!
# GolayOctadTransitivity

Five-transitivity on coordinates implies transitivity on five-sets and then on octads.
Matching five selected points matches their unique octad completions in the Witt design.

Source: `Atlas/Mathieu/GolayOctadTransitivity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

theorem mathieu24_five_set_transitive (S T : Finset Omega) (hS : S.card = 5) (hT : T.card = 5) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val S = T := by
  classical
  obtain ⟨g,hg⟩ := mathieu24_five_transitive_explicit
    (finiteSetEmbedding S hS) (finiteSetEmbedding T hT)
  refine ⟨g,?_⟩
  rw [← finiteSetEmbedding_image S hS,← finiteSetEmbedding_image T hT]
  change (univ.image (finiteSetEmbedding S hS)).image g.val = _
  rw [image_image]
  exact image_congr (fun i _ => hg i)

theorem mathieu24_octad_transitive (O P : Finset Omega) (hO : O ∈ octads) (hP : P ∈ octads) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P := by
  classical
  obtain ⟨S,hSO,hS⟩ := exists_subset_card_eq (s := O) (n := 5) (by rw [octad_size O hO]; decide)
  obtain ⟨T,hTP,hT⟩ := exists_subset_card_eq (s := P) (n := 5) (by rw [octad_size P hP]; decide)
  obtain ⟨g,hg⟩ := mathieu24_five_set_transitive S T hS hT
  refine ⟨g,octad_unique_on_five T _ P hT
    ((codePreserving_octadPreserving g.val g.prop O).mp hO) hP ?_ hTP⟩
  rw [← hg]
  exact image_subset_image hSO

end Atlas.Codes
