/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayMarkedOctadTransitivity
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetCompletion

/-!
# OctadExteriorSeparation

An octad and two distinct exterior coordinates have a sextet decomposition placing those
coordinates in different exterior tetrads. Selecting a suitable tetrad and using unique
sextet completion gives the separation needed for pair transport.

Source: `Atlas/Mathieu/OctadExteriorSeparation.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octad_exterior_pair_separating_tetrad (O : Finset Omega) (hO : O ∈ octads)
    (a b : Omega) (ha : a ∉ O) (hb : b ∉ O) (hab : a ≠ b) :
    ∃ T : FourSet, T.val ⊆ O ∧
      ∀ B ∈ octads, T.val ⊆ B → a ∈ B → b ∈ B → False := by
  obtain ⟨S,hSO,hS⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ O.card by rw [octad_size O hO]; decide)
  have haS : a ∉ S := fun h => ha (hSO h)
  have hbS : b ∉ S := fun h => hb (hSO h)
  let F := insert a (insert b S)
  have hF : F.card = 5 := by simp [F,haS,hbS,hab,hS]
  obtain ⟨B,⟨hB,hFB⟩,_⟩ := octad_steiner F hF
  have hOB : ¬ O ⊆ B := by
    intro h
    have he : O = B := Finset.eq_of_subset_of_card_le h (by rw [octad_size O hO,octad_size B hB])
    exact ha (he ▸ hFB (by simp [F]))
  obtain ⟨d,hdO,hdB⟩ := Finset.not_subset.mp hOB
  have hdS : d ∉ S := fun h => hdB (hFB (by simp [F,h]))
  refine ⟨⟨insert d S,by simp [hdS,hS]⟩,Finset.insert_subset hdO hSO,?_⟩
  intro C hC hTC haC hbC
  have hFC : F ⊆ C := by
    apply Finset.insert_subset haC
    apply Finset.insert_subset hbC
    exact (Finset.subset_insert _ _).trans hTC
  have he := octad_unique_on_five F B C hF hB hC hFB hFC
  exact hdB (he ▸ hTC (Finset.mem_insert_self _ _))

theorem octad_exterior_pair_separating_sextet (O : Finset Omega) (hO : O ∈ octads)
    (a b : Omega) (ha : a ∉ O) (hb : b ∉ O) (hab : a ≠ b) :
    ∃ S : UnorderedSextet, ∃ T ∈ S.val, ∃ U ∈ S.val, T ∪ U = O ∧
      ∀ V ∈ S.val, a ∈ V → b ∉ V := by
  obtain ⟨T,hTO,hT⟩ := octad_exterior_pair_separating_tetrad O hO a b ha hb hab
  let S := sextetCompletion T
  have hTS : T.val ∈ S.val := tetrad_mem_completion T
  have hUS : O \ T.val ∈ S.val := by
    apply Finset.mem_insert_of_mem
    exact (companion_mem T _).mpr ⟨O,hO,hTO,rfl⟩
  refine ⟨S,T.val,hTS,O \ T.val,hUS,Finset.union_sdiff_of_subset hTO,?_⟩
  intro V hVS haV hbV
  have hne : T.val ≠ V := by
    intro he
    exact ha (hTO (he ▸ haV))
  exact hT (T.val ∪ V) (S.prop.pair_octads T.val hTS V hVS hne)
    Finset.subset_union_left (Finset.mem_union_right _ haV) (Finset.mem_union_right _ hbV)

end Atlas.Codes

