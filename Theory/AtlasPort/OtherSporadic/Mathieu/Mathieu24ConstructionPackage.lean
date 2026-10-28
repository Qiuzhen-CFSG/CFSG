/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24Nonabelian

/-!
# The hexacode construction of the Golay automorphism group

This interface assembles the proved hexacode reconstruction, sextet
orbit-stabilizer equivalence, coordinate actions, stabilizer orders and parity
of the Golay automorphism group. Each field is supplied by a proved result
from the concrete construction; simplicity is established separately.

Source: `Atlas/Mathieu/Mathieu24ConstructionPackage.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The verified Job 6 construction/action package; simplicity is a separate obligation. -/
structure Mathieu24HexacodeConstructionPackage : Prop where
  hexacode_uniqueness : ∀ D : Submodule Bit HexWord, Module.finrank Bit D = 6 →
    (∀ w ∈ D, w ≠ 0 → 4 ≤ hammingNorm w) → MonomiallyEquivalent D hexacode
  recovered_dimension : ∀ S : UnorderedSextet, Module.finrank Bit (sextetHexacode S) = 6
  recovered_selfDual : ∀ S : UnorderedSextet, sextetHexacode S = dual (sextetHexacode S)
  recovered_minimum : ∀ (S : UnorderedSextet) w, w ∈ sextetHexacode S → w ≠ 0 → 4 ≤ hammingNorm w
  recovered_kernel : ∀ S : UnorderedSextet, (tetradDecode (sextetCode S)).ker =
    (tetradConstants (sextetCode S) (sextetCode_properties S)).range
  recovered_quotient : ∀ S : UnorderedSextet, Nonempty
    ((tetradEvenSubcode (sextetCode S) ⧸ (tetradDecode (sextetCode S)).ker) ≃ₗ[Bit] sextetHexacode S)
  full_normal_form : ∀ S : UnorderedSextet, ∃ t : HexWord, ∀ w : BinaryWord,
    w ∈ permutedBinaryCode (sextetCode S) (affinePermutation t 1) ↔
      ∃ (h : sextetHexacode S) (r : P6) (ε : Bit), w = jWord h.val+rho r.val+ε • eta
  marked_reconstruction : ∀ S : UnorderedSextet, ∃ σ : Equiv.Perm Omega, CodePreserving σ ∧
    permuteSextetParts σ S.val = distinguishedUnorderedSextet.val
  sextet_transitive : MulAction.IsPretransitive Mathieu24CodeModel UnorderedSextet
  orbit_stabilizer : Nonempty (UnorderedSextet × SextetStabilizer ≃ Mathieu24CodeModel)
  finite : Finite Mathieu24CodeModel
  order : Nat.card Mathieu24CodeModel = 244823040
  faithful : FaithfulSMul Mathieu24CodeModel Omega
  five_transitive : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 5
  not_six_transitive : ¬ MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 6
  not_six_homogeneous : ∃ U V : Finset Omega, U.card = 6 ∧ V.card = 6 ∧
    ∀ g : Mathieu24CodeModel, permuteBlock g.val U ≠ V
  local_symmetric : ∀ (i : HexIndex) (σ : Equiv.Perm (Fin 4)),
    ∃ s : SextetStabilizer, ∀ k : Fin 4, s.val.val (i,k) = (i,σ k)
  local_kernel_structure : ∀ i : HexIndex, Nonempty (hexPointKernel i ≃* HexEvenPoint i)
  tetrad_pointwise_structure : ∀ i : HexIndex, Nonempty (TetradPointAffine i ≃* TetradPointStabilizer i)
  tetrad_pointwise_order : ∀ i : HexIndex, Nat.card (TetradPointStabilizer i) = 960
  one_point_order : ∀ e : Fin 1 ↪ Omega, Nat.card (orderedPointStabilizer e) = 10200960
  two_point_order : ∀ e : Fin 2 ↪ Omega, Nat.card (orderedPointStabilizer e) = 443520
  three_point_order : ∀ e : Fin 3 ↪ Omega, Nat.card (orderedPointStabilizer e) = 20160
  four_point_order : ∀ e : Fin 4 ↪ Omega, Nat.card (orderedPointStabilizer e) = 960
  five_point_order : ∀ e : Fin 5 ↪ Omega, Nat.card (orderedPointStabilizer e) = 48
  noncommuting : ∃ g h : Mathieu24CodeModel, g*h ≠ h*g
  alternating : Mathieu24CodeModel ≤ alternatingGroup Omega

theorem mathieu24_hexacode_construction : Mathieu24HexacodeConstructionPackage where
  hexacode_uniqueness := hexacode_unique_of_dimension_minimum
  recovered_dimension S := (sextetHexacode_properties S).1
  recovered_selfDual S := (sextetHexacode_properties S).2.1
  recovered_minimum S := (sextetHexacode_properties S).2.2.2.1
  recovered_kernel S := tetradDecode_kernel _ (sextetCode_properties S)
  recovered_quotient S := ⟨tetradQuotientEquiv (sextetCode S)⟩
  full_normal_form S := tetradCode_normalized _ (sextetCode_properties S)
  marked_reconstruction := sextet_marked_reconstruction
  sextet_transitive := unorderedSextet_pretransitive
  orbit_stabilizer := ⟨sextetOrbitStabilizerEquiv⟩
  finite := inferInstance
  order := mathieu24_order
  faithful := inferInstance
  five_transitive := mathieu24_five_transitive
  not_six_transitive := mathieu24_not_six_transitive
  not_six_homogeneous := mathieu24_not_six_homogeneous
  local_symmetric := sextet_tetrad_full_symmetric
  local_kernel_structure i := ⟨hexPointKernelAlternatingEquiv i⟩
  tetrad_pointwise_structure i := ⟨tetradPointStabilizerEquiv i⟩
  tetrad_pointwise_order := tetradPointStabilizer_card
  one_point_order := mathieu24_one_point_order
  two_point_order := mathieu24_two_point_order
  three_point_order := mathieu24_three_point_order
  four_point_order := mathieu24_four_point_order
  five_point_order := mathieu24_five_point_order
  noncommuting := mathieu24_noncommuting_pair
  alternating := mathieu24_le_alternating

end Atlas.Codes
