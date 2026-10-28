/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayAutomorphisms

/-!
# Dodecads

Dodecads are supports of weight-twelve Golay words. The weight distribution gives 2576
dodecads, while code addition constrains their intersections with octads; coordinate
automorphisms preserve this family.

Source: `Atlas/Codes/Dodecads.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open Finset

noncomputable def dodecads : Finset (Finset Omega) :=
  (univ.filter (fun w : golay => hammingNorm w.val = 12)).image (fun w => support w.val)

abbrev Dodecad := {D : Finset Omega // D ∈ dodecads}

theorem dodecads_mem (D : Finset Omega) : D ∈ dodecads ↔
    ∃ w : golay, hammingNorm w.val = 12 ∧ support w.val = D := by
  classical
  simp only [dodecads, mem_image, mem_filter, mem_univ, true_and]

theorem dodecads_card : dodecads.card = 2576 := by
  classical
  rw [dodecads, card_image_of_injective _ (fun _ _ h => Subtype.ext (support_injective h))]
  have h := golay_weight_distribution 12
  simpa [golayWeightCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem dodecad_size (D : Finset Omega) (hD : D ∈ dodecads) : D.card = 12 := by
  obtain ⟨w, hw, rfl⟩ := (dodecads_mem D).mp hD
  exact hw

theorem codePreserving_dodecad_forward (σ : Equiv.Perm Omega) (hσ : CodePreserving σ)
    (D : Finset Omega) (hD : D ∈ dodecads) : permuteBlock σ D ∈ dodecads := by
  obtain ⟨w, hw, rfl⟩ := (dodecads_mem D).mp hD
  exact (dodecads_mem _).mpr
    ⟨⟨coordinatePermutation σ w.val, (hσ w.val).mp w.prop⟩,
      (coordinatePermutation_weight σ w.val).trans hw, coordinatePermutation_support σ w.val⟩

theorem dodecad_octad_intersection (D O : Finset Omega)
    (hD : D ∈ dodecads) (hO : O ∈ octads) :
    (D ∩ O).card = 2 ∨ (D ∩ O).card = 4 ∨ (D ∩ O).card = 6 := by
  obtain ⟨u, hu, rfl⟩ := (dodecads_mem D).mp hD
  obtain ⟨v, hv, rfl⟩ := (octads_mem O).mp hO
  have he := binary_weight_add u.val v.val
  rw [hu, hv, overlap_inter] at he
  have hs := golay_weights ⟨u.val + v.val, golay.add_mem u.prop v.prop⟩
  change hammingNorm (u.val + v.val) = 0 ∨ hammingNorm (u.val + v.val) = 8 ∨
    hammingNorm (u.val + v.val) = 12 ∨ hammingNorm (u.val + v.val) = 16 ∨
    hammingNorm (u.val + v.val) = 24 at hs
  have hi : (support u.val ∩ support v.val).card ≤ 8 := by
    exact (card_le_card inter_subset_right).trans_eq hv
  rcases hs with hs | hs | hs | hs | hs <;> omega

theorem dodecad_not_two_tetrads (D : Finset Omega) (hD : D ∈ dodecads)
    (i j : HexIndex) (hij : i ≠ j) (hi : tetrad i ⊆ D) : ¬ tetrad j ⊆ D := by
  intro hj
  have h := dodecad_octad_intersection D (tetrad i ∪ tetrad j) hD (tetrad_pair_octad i j hij)
  rw [inter_eq_right.mpr (union_subset hi hj), card_union_of_disjoint (tetrads_disjoint i j hij),
    tetrad_card, tetrad_card] at h
  omega

end Atlas.Codes
