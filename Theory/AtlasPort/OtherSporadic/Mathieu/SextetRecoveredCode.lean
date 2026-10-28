/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetCoordinates

/-!
# SextetRecoveredCode

Pulling Golay back along sextet coordinates produces a tetrad code. Pairwise octad
unions supply its even repetition subcode, and transported self-duality and minimum
weight give the recovered hexacode properties.

Source: `Atlas/Mathieu/SextetRecoveredCode.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

theorem R0_le_of_pairs (E : Submodule Bit BinaryWord)
    (hp : ∀ i j, wholeTetrad i+wholeTetrad j ∈ E) : R0 ≤ E := by
  rintro _ ⟨r,hr,rfl⟩
  have he := congrArg (fun v : P6 => rho v.val) ((parityBasis 5).sum_repr ⟨r,hr⟩)
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul] at he
  rw [← he]
  apply E.sum_mem
  intro i _
  apply E.smul_mem
  rw [parityBasis_coe,map_add]
  simpa only [wholeTetrad,index_hexPos] using hp (hexPos 0) (hexPos i.succ)

/-- The fixed Golay code expressed in arbitrary coordinates of the specified sextet. -/
def sextetCode (S : UnorderedSextet) : Submodule Bit BinaryWord :=
  golay.comap (coordinatePermutation (sextetCoordinates S)).toLinearMap

theorem sextetCode_properties (S : UnorderedSextet) : IsTetradCode (sextetCode S) where
  self_dual := by
    ext w
    constructor
    · intro hw z hz
      have ho : coordinatePermutation (sextetCoordinates S) w ∈ binaryDot.orthogonal golay := by
        rw [← golay_selfDual]; exact hw
      have he := ho (coordinatePermutation (sextetCoordinates S) z) hz
      rw [coordinatePermutation_dot] at he
      exact he
    · intro hw
      change coordinatePermutation (sextetCoordinates S) w ∈ golay
      rw [golay_selfDual]
      intro v hv
      obtain ⟨z,rfl⟩ := (coordinatePermutation (sextetCoordinates S)).surjective v
      rw [coordinatePermutation_dot]
      exact hw z hv
  doubly_even := by
    intro w hw
    have he := golay_doublyEven (coordinatePermutation (sextetCoordinates S) w) hw
    rwa [coordinatePermutation_weight] at he
  minimum := by
    intro w hw hn
    have hn' : coordinatePermutation (sextetCoordinates S) w ≠ 0 := by
      intro hz
      apply hn
      exact (coordinatePermutation (sextetCoordinates S)).injective (hz.trans (map_zero _).symm)
    have he := golay_minimum (coordinatePermutation (sextetCoordinates S) w) hw hn'
    rwa [coordinatePermutation_weight] at he
  repetitions := R0_le_of_pairs _ (sextetCoordinates_pair_mem S)

/-- The intrinsic even-block quotient attached to an arbitrary sextet of the fixed code. -/
def sextetHexacode (S : UnorderedSextet) := tetradHexacode (sextetCode S)

theorem sextetHexacode_properties (S : UnorderedSextet) :
    Module.finrank Bit (sextetHexacode S) = 6 ∧
    sextetHexacode S = dual (sextetHexacode S) ∧
    (∀ h ∈ sextetHexacode S, Even (hammingNorm h)) ∧
    (∀ h ∈ sextetHexacode S, h ≠ 0 → 4 ≤ hammingNorm h) ∧
    MonomiallyEquivalent (sextetHexacode S) hexacode :=
  ⟨tetradHexacode_finrank _ (sextetCode_properties S),
    tetradHexacode_selfDual _ (sextetCode_properties S),
    tetradHexacode_even _ (sextetCode_properties S),
    tetradHexacode_minimum _ (sextetCode_properties S),
    tetradHexacode_unique _ (sextetCode_properties S)⟩

end Atlas.Codes
