/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecoveredCode

/-!
# SextetReconstruction

Every unordered sextet is equivalent to the distinguished sextet by a Golay coordinate
automorphism. Its recovered tetrad code is first identified with Golay, and composing
that identification with the sextet coordinates proves reconstruction.

Source: `Atlas/Mathieu/SextetReconstruction.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- Reconstruction of the entire fixed code from any of its unordered sextets. -/
theorem sextet_marked_reconstruction (S : UnorderedSextet) :
    ∃ σ : Equiv.Perm Omega, CodePreserving σ ∧
      permuteSextetParts σ S.val = distinguishedUnorderedSextet.val := by
  obtain ⟨t,g,hg⟩ := tetradCode_equivalent (sextetCode S) (sextetCode_properties S)
  let ψ := affinePermutation 0 g * affinePermutation t 1
  let σ := ψ * (sextetCoordinates S)⁻¹
  refine ⟨σ,?_,?_⟩
  · intro w
    have he := hg (coordinatePermutation (sextetCoordinates S)⁻¹ w)
    change coordinatePermutation (sextetCoordinates S)
      (coordinatePermutation (sextetCoordinates S)⁻¹ w) ∈ golay ↔ _ at he
    rw [← coordinatePermutation_mul,mul_inv_cancel,coordinatePermutation_one] at he
    exact he
  · have hs : permuteSextetParts (sextetCoordinates S)⁻¹ S.val =
        distinguishedUnorderedSextet.val := by
      rw [← sextetCoordinates_parts S,← permuteSextetParts_mul,inv_mul_cancel,permuteSextetParts_one]
    rw [show σ = ψ * (sextetCoordinates S)⁻¹ from rfl,permuteSextetParts_mul,hs]
    rw [show ψ = affinePermutation 0 g * affinePermutation t 1 from rfl,permuteSextetParts_mul,
      affinePermutation_preserves_parts,affinePermutation_preserves_parts]

/-- The reconstruction witness is an element of the full, previously defined automorphism group. -/
theorem sextet_equivalent_distinguished (S : UnorderedSextet) :
    ∃ g : Mathieu24CodeModel, g • S = distinguishedUnorderedSextet := by
  obtain ⟨σ,hσ,hS⟩ := sextet_marked_reconstruction S
  exact ⟨⟨σ,hσ⟩,Subtype.ext hS⟩

end Atlas.Codes
