module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products3

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 3

The binary mask is 50. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part3
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (50 : ℕ).testBit j.val) = e 1 * (e 4 * (e 5)) := by
  have hv : (fun j : Fin 11 => (50 : ℕ).testBit j.val) = ![false, true, false, false, true, true, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (50 : ℕ).testBit j.val) = decodeRows m3_1Rows := by
  rw [← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r3 : toMatrix (outsideRepresentative hA hB 3 : Model) = decodeRows r3Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (50 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_02]

theorem square_3 : (outsideRepresentative hA hB 3 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r3, pow_two, decoded_product product_03, decode_packedOne]

private theorem odd_power : decodeRows q3Rows ^ 43 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q3p2Rows = decodeRows q3Rows ^ 2 := by
    rw [← decoded_product product_05, ← pow_two]
  have h4 : decodeRows q3p4Rows = decodeRows q3Rows ^ 4 := by
    rw [← decoded_product product_06, h2, ← pow_add]
  have h5 : decodeRows q3p5Rows = decodeRows q3Rows ^ 5 := by
    rw [← decoded_product product_07, h4, ← pow_succ]
  have h10 : decodeRows q3p10Rows = decodeRows q3Rows ^ 10 := by
    rw [← decoded_product product_08, h5, ← pow_add]
  have h20 : decodeRows q3p20Rows = decodeRows q3Rows ^ 20 := by
    rw [← decoded_product product_09, h10, ← pow_add]
  have h21 : decodeRows q3p21Rows = decodeRows q3Rows ^ 21 := by
    rw [← decoded_product product_10, h20, ← pow_succ]
  have h42 : decodeRows q3p42Rows = decodeRows q3Rows ^ 42 := by
    rw [← decoded_product product_11, h21, ← pow_add]
  have h := decoded_product product_12
  rw [h42, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_3 :
    ((outsideRepresentative hA hB 3 : Model) * (word (a hA) (b hB) "bb" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "bb")⁻¹)) ^ 43 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r3]
  rw [eval_conj1Rows]
  rw [decoded_product product_04]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
