/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeNormalForm

/-!
# Uniqueness of the hexacode up to monomial equivalence

A binary six-dimensional subspace of six Kleinian coordinates with
minimum weight four is monomially equivalent to the hexacode. The proof
reduces its systematic form by local isometries and applies the normal-form
classification.

Source: `Atlas/Codes/HexacodeUniqueness.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- Ambient monomial equivalence, not merely an abstract code-space isomorphism. -/
def MonomiallyEquivalent (D E : Submodule Bit HexWord) : Prop :=
  ∃ g : Monomial HexIndex, ∀ w : HexWord, w ∈ D ↔ Monomial.act g w ∈ E

theorem mds_mem_graph (D : Submodule Bit HexWord) (hD : IsHexMDS D) (w : HexWord) :
    w ∈ D ↔ w ∈ Set.range (kleinGraphWord (mdsCoefficientEquiv D hD)) := by
  constructor
  · intro hw
    refine ⟨mdsInputEquiv D hD ⟨w,hw⟩,?_⟩
    rw [← mdsEncoder_graph]
    change ((mdsInputEquiv D hD).symm (mdsInputEquiv D hD ⟨w,hw⟩)).val = w
    rw [LinearEquiv.symm_apply_apply]
  · rintro ⟨x,rfl⟩
    rw [← mdsEncoder_graph]
    exact ((mdsInputEquiv D hD).symm x).prop

theorem hex_mds_normal_form (D : Submodule Bit HexWord) (hD : IsHexMDS D) :
    ∃ g : Monomial HexIndex, ∀ w : HexWord,
      w ∈ D ↔ Monomial.act g w ∈ KleinNormalWords := by
  obtain ⟨g,hg⟩ := mds_graph_normal_form (mdsCoefficientEquiv D hD) (mdsMatrix_valid D hD)
  exact ⟨g,fun w => (mds_mem_graph D hD w).trans (hg w)⟩

theorem hexacode_isHexMDS : IsHexMDS hexacode := ⟨hexacode_finrank,hexacode_minimum⟩

/-- Dimension six and minimum weight four already force the actual additive hexacode. -/
theorem hexacode_unique_of_dimension_minimum (D : Submodule Bit HexWord)
    (hd : Module.finrank Bit D = 6)
    (hm : ∀ w ∈ D, w ≠ 0 → 4 ≤ hammingNorm w) : MonomiallyEquivalent D hexacode := by
  obtain ⟨g,hg⟩ := hex_mds_normal_form D ⟨hd,hm⟩
  obtain ⟨h,hh⟩ := hex_mds_normal_form hexacode hexacode_isHexMDS
  refine ⟨h⁻¹*g,?_⟩
  intro w
  rw [hh,← Monomial.act_mul]
  simpa only [mul_inv_cancel_left] using hg w

theorem selfDual_hex_finrank (D : Submodule Bit HexWord) (hD : D = dual D) :
    Module.finrank Bit D = 6 := by
  have hd := wordPolar.finrank_orthogonal wordPolar_nondegenerate D
  change Module.finrank Bit (dual D) = Module.finrank Bit HexWord - Module.finrank Bit D at hd
  have ha : Module.finrank Bit HexWord = 12 := by
    change Module.finrank Bit (HexIndex → Bit × Bit) = 12
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_prod,HexIndex]
  rw [← hD,ha] at hd
  have hd' : Module.finrank Bit D = 12 - Module.finrank Bit D := hd
  omega

/-- The even self-dual formulation; evenness is unnecessary for the stronger theorem. -/
theorem hexacode_unique_even_selfDual (D : Submodule Bit HexWord)
    (_he : ∀ w ∈ D, Even (hammingNorm w)) (hs : D = dual D)
    (hm : ∀ w ∈ D, w ≠ 0 → 4 ≤ hammingNorm w) : MonomiallyEquivalent D hexacode :=
  hexacode_unique_of_dimension_minimum D (selfDual_hex_finrank D hs) hm

end Atlas.Codes
