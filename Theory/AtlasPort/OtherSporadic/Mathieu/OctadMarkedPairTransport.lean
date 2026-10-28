/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayMarkedOctadTransitivity

/-!
# Transport of octads with marked interior pairs

An octad with two distinct interior points can be transported to any
other such configuration. First use two-transitivity to match the points,
then transport the octads while fixing the marked pair pointwise.

Source: `Atlas/Mathieu/OctadMarkedPairTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem mathieu24_ordered_pair_transport (a b c d : Omega) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Mathieu24CodeModel, g.val a = c ∧ g.val b = d := by
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 := by
    let := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by norm_num [Omega,HexIndex])
  exact (MulAction.is_two_pretransitive_iff.mp ht) hab hcd

theorem mathieu24_octad_marked_pair_transitive (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (a b c d : Omega)
    (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b)
    (hc : c ∈ P) (hd : d ∈ P) (hcd : c ≠ d) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P ∧ g.val a = c ∧ g.val b = d := by
  obtain ⟨g,hga,hgb⟩ := mathieu24_ordered_pair_transport a b c d hab hcd
  have hO' := (codePreserving_octadPreserving g.val g.prop O).mp hO
  have hcO : c ∈ permuteBlock g.val O := Finset.mem_image.mpr ⟨a,ha,hga⟩
  have hdO : d ∈ permuteBlock g.val O := Finset.mem_image.mpr ⟨b,hb,hgb⟩
  obtain ⟨h,hh,hhP⟩ := mathieu24_marked_octad_transitive {c,d} (permuteBlock g.val O) P
    (by simp [hcd]) hO' hP (Finset.insert_subset hcO (Finset.singleton_subset_iff.mpr hdO)) (Finset.insert_subset hc (Finset.singleton_subset_iff.mpr hd))
  refine ⟨h*g,?_,?_,?_⟩
  · change permuteBlock (h.val*g.val) O = P
    rw [permuteBlock_mul,hhP]
  · change h.val (g.val a) = c
    rw [hga,hh c (by simp)]
  · change h.val (g.val b) = d
    rw [hgb,hh d (by simp)]

end Atlas.Codes
