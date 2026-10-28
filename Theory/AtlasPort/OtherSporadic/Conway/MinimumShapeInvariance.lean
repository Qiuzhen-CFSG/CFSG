/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumShapeInvariance.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimalEvenOrbits
public import Theory.AtlasPort.OtherSporadic.Conway.MinimalOddOrbit
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumShapeInvariance.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem monomial_magnitude_support (m : GolayMonomialGroup) (x : leech) (k : ℤ) :
    evenMagnitudeSupport ((monomialEmbedding m).val x).val k =
      permuteBlock m.right.val (evenMagnitudeSupport x.val k) := by
  ext i
  have he : ((monomialEmbedding m).val x).val i * ((monomialEmbedding m).val x).val i =
      x.val (m.right.val.symm i) * x.val (m.right.val.symm i) := by
    rw [monomialEmbedding_apply]
    split_ifs <;> ring
  constructor
  · intro hi
    have hh := (Finset.mem_filter.mp hi).2
    rw [he] at hh
    exact Finset.mem_image.mpr ⟨m.right.val.symm i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩,
      m.right.val.apply_symm_apply i⟩
  · rintro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [he,Equiv.symm_apply_apply]
    exact (Finset.mem_filter.mp hj).2

theorem monomial_twoFour_invariant (m : GolayMonomialGroup) (x : leech) (k u : ℕ)
    (hx : x.val ∈ twoFourFamily k u) : ((monomialEmbedding m).val x).val ∈ twoFourFamily k u := by
  apply (twoFourFamily_iff k u _).mpr
  refine ⟨((monomialEmbedding m).val x).prop,?_⟩
  obtain ⟨hs,hk,hu⟩ := twoFourFamily_shape k u x.val hx
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [monomialEmbedding_apply]
    have hh := hs (m.right.val.symm i)
    split_ifs <;> rcases hh with h | h | h | h | h <;> simp_all
  · rw [monomial_magnitude_support,permuteBlock_card,hk]
  · rw [monomial_magnitude_support,permuteBlock_card,hu]

theorem monomial_odd_minimum_invariant (m : GolayMonomialGroup) (x : leech)
    (hx : x.val ∈ oddNoFiveVectors 1) : ((monomialEmbedding m).val x).val ∈ oddNoFiveVectors 1 := by
  obtain ⟨_,hp,hn⟩ := (odd_minimal_shell_iff x.val).mpr hx
  apply (odd_minimal_shell_iff _).mp
  refine ⟨((monomialEmbedding m).val x).prop,?_,?_⟩
  · intro i
    rw [monomialEmbedding_apply]
    have hh := hp (m.right.val.symm i)
    split_ifs <;> omega
  · exact ((monomialEmbedding m).prop x x).trans hn

end Atlas.Conway
