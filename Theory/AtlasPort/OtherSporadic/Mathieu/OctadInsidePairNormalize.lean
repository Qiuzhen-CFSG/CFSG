/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadPairNormalization

/-!
# OctadInsidePairNormalize

An octad with two distinct interior points and an exterior point can be normalized to
two tetrads with the interior points in separate columns. A suitable tetrad inside the
octad and sextet reconstruction give the coordinate permutation.

Source: `Atlas/Mathieu/OctadInsidePairNormalize.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octad_inside_pair_tetrad (O : Finset Omega) (hO : O ∈ octads)
    (a b : Omega) (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) :
    ∃ T : FourSet, T.val ⊆ O ∧ a ∈ T.val ∧ b ∉ T.val := by
  have hc : (O \ {a,b}).card = 6 := by
    rw [Finset.card_sdiff_of_subset (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)),octad_size O hO,Finset.card_pair hab]
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ (O \ {a,b}).card by omega)
  have haS : a ∉ S := fun h => (Finset.mem_sdiff.mp (hS h)).2 (by simp)
  have hbS : b ∉ S := fun h => (Finset.mem_sdiff.mp (hS h)).2 (by simp)
  refine ⟨⟨insert a S,by simp [haS,hcard]⟩,?_,by simp,by simp [Ne.symm hab,hbS]⟩
  exact Finset.insert_subset ha (fun i hi => (Finset.mem_sdiff.mp (hS hi)).1)

theorem octad_inside_pair_normalize (O : Finset Omega) (hO : O ∈ octads)
    (a b c : Omega) (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) (hc : c ∉ O) :
    ∃ g : Mathieu24CodeModel, ∃ i j : HexIndex,
      i ≠ j ∧ permuteBlock g.val O = tetrad i ∪ tetrad j ∧
      (g.val a).1 = i ∧ (g.val b).1 = j ∧ (g.val c).1 ≠ i ∧ (g.val c).1 ≠ j := by
  obtain ⟨T,hTO,haT,hbT⟩ := octad_inside_pair_tetrad O hO a b ha hb hab
  let S := sextetCompletion T
  have hTS : T.val ∈ S.val := tetrad_mem_completion T
  have hUS : O \ T.val ∈ S.val := by
    apply Finset.mem_insert_of_mem
    exact (companion_mem T _).mpr ⟨O,hO,hTO,rfl⟩
  obtain ⟨g,hg⟩ := sextet_equivalent_distinguished S
  obtain ⟨i,hi⟩ := sextet_image_part_tetrad S g hg T.val hTS
  obtain ⟨j,hj⟩ := sextet_image_part_tetrad S g hg (O \ T.val) hUS
  have he : permuteBlock g.val O = tetrad i ∪ tetrad j := by
    rw [← Finset.union_sdiff_of_subset hTO]
    change (T.val ∪ (O \ T.val)).image g.val = _
    rw [Finset.image_union]
    exact congrArg₂ (· ∪ ·) hi hj
  have hij : i ≠ j := by
    intro hh
    have hcard := permuteBlock_card g.val O
    rw [he,hh,Finset.union_self,tetrad_card,octad_size O hO] at hcard
    omega
  have hga : (g.val a).1 = i := (mem_tetrad _ _).mp (by
    rw [← hi]; exact Finset.mem_image.mpr ⟨a,haT,rfl⟩)
  have hgb : (g.val b).1 = j := (mem_tetrad _ _).mp (by
    rw [← hj]; exact Finset.mem_image.mpr ⟨b,Finset.mem_sdiff.mpr ⟨hb,hbT⟩,rfl⟩)
  have hgc : (g.val c).1 ≠ i ∧ (g.val c).1 ≠ j := by
    have hm : g.val c ∉ permuteBlock g.val O := by
      intro h
      obtain ⟨d,hd,he⟩ := Finset.mem_image.mp h
      exact hc (g.val.injective he ▸ hd)
    simpa [he] using hm
  exact ⟨g,i,j,hij,he,hga,hgb,hgc⟩

end Atlas.Codes
