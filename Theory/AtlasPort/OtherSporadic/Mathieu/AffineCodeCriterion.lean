/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineEncoderTransform

/-!
# AffineCodeCriterion

An affine monomial coordinate permutation preserves Golay exactly when its translation
is a hexacode word and its linear part preserves the hexacode. The encoder
transformation proves sufficiency; decoding the transformed even words and distinguished
odd word proves necessity.

Source: `Atlas/Mathieu/AffineCodeCriterion.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

/-- In finite dimension, invariant containment under a linear equivalence is equality. -/
theorem codePreserving_of_forward (σ : Equiv.Perm Omega)
    (hσ : ∀ w ∈ golay, coordinatePermutation σ w ∈ golay) : CodePreserving σ := by
  have hl : golay.map (coordinatePermutation σ).toLinearMap ≤ golay := by
    rintro _ ⟨w,hw,rfl⟩; exact hσ w hw
  have he := Submodule.eq_of_le_of_finrank_eq hl ((coordinatePermutation σ).finrank_map_eq golay)
  intro w
  constructor
  · exact hσ w
  · intro hw
    have hm : coordinatePermutation σ w ∈ golay.map (coordinatePermutation σ).toLinearMap := by
      rw [he]; exact hw
    obtain ⟨v,hv,hvw⟩ := hm
    have hh := (coordinatePermutation σ).injective hvw
    rwa [← hh]

theorem affineRepetition_sum (t : HexWord) (g : Monomial HexIndex) (h : HexWord)
    (r : HexIndex → Bit) (ε : Bit) :
    (∑ i, affineRepetition t g h r ε i) =
      (∑ i, r i) + wordPolar (Monomial.act g h) t + ε * wordQ qK t := by
  simp only [affineRepetition,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Equiv.sum_comp g.perm.symm r,Equiv.sum_comp g.perm.symm lastColumnBit]
  simp only [wordPolar_apply,wordQ]
  ring_nf
  simp

theorem hexacode_orthogonal (h t : HexWord) (hh : h ∈ hexacode) (ht : t ∈ hexacode) :
    wordPolar h t = 0 := by
  have hd : t ∈ dual hexacode := hexacode_selfDual ▸ ht
  exact hd h hh

theorem affine_preserves_code (t : HexWord) (g : Monomial HexIndex)
    (ht : t ∈ hexacode) (hg : g ∈ Monomial.stabilizer hexacode) :
    CodePreserving (affinePermutation t g) := by
  apply codePreserving_of_forward
  intro w hw
  obtain ⟨⟨h,r,ε⟩,he⟩ := golayEquiv.surjective ⟨w,hw⟩
  have he' := (rowEncoder_golayEquiv h r ε).trans (congrArg Subtype.val he)
  dsimp only at he'
  rw [← he',affine_encoder_transform,rowEncoder_mem_iff]
  have hh : Monomial.act g h.val ∈ hexacode := (hg _).mp h.prop
  refine ⟨hexacode.add_mem hh (hexacode.smul_mem ε ht),?_⟩
  rw [affineRepetition_sum,Equiv.sum_comp hexIndexEquiv]
  rw [(parityCode_mem 5 r.val).mp r.prop,hexacode_orthogonal _ _ hh ht,hexacode_isotropic t ht]
  simp

theorem rowEncoder_eta : rowEncoder 0 0 1 = eta := by
  have h := rowEncoder_lift 0 0 1
  simp only [map_zero,zero_add,one_smul,Pi.zero_apply] at h
  exact h

theorem affine_preservation_necessary (t : HexWord) (g : Monomial HexIndex)
    (hF : CodePreserving (affinePermutation t g)) :
    t ∈ hexacode ∧ g ∈ Monomial.stabilizer hexacode := by
  have he := (hF eta).mp eta_mem_golay
  rw [← rowEncoder_eta,affine_encoder_transform,rowEncoder_mem_iff] at he
  have ht : t ∈ hexacode := by simpa using he.1
  refine ⟨ht,monomial_mem_of_hexBasis g ?_⟩
  intro k
  have hk : hexGenerators k ∈ hexacode := by rw [← hexBasis_coe]; exact (hexBasis k).prop
  have hw : rowEncoder (hexGenerators k) 0 0 ∈ golay :=
    (rowEncoder_mem_iff _ _ _).mpr ⟨hk,by simp⟩
  have hi := (hF _).mp hw
  rw [affine_encoder_transform,rowEncoder_mem_iff] at hi
  simpa using hi.1

/-- Full code-preservation criterion for arbitrary ambient affine partition permutations. -/
theorem affine_code_preservation_iff (t : HexWord) (g : Monomial HexIndex) :
    CodePreserving (affinePermutation t g) ↔ t ∈ hexacode ∧ g ∈ Monomial.stabilizer hexacode :=
  ⟨affine_preservation_necessary t g,fun h => affine_preserves_code t g h.1 h.2⟩

end Atlas.Codes
