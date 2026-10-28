module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products4

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 4

The binary mask is 70. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part4
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (70 : ℕ).testBit j.val) = e 1 * (e 2 * (e 6)) := by
  have hv : (fun j : Fin 11 => (70 : ℕ).testBit j.val) = ![false, true, true, false, false, false, true, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (70 : ℕ).testBit j.val) = decodeRows m4_1Rows := by
  rw [← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r4 : toMatrix (outsideRepresentative hA hB 4 : Model) = decodeRows r4Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (70 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_02]

theorem square_4 : (outsideRepresentative hA hB 4 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r4, pow_two, decoded_product product_03, decode_packedOne]

private theorem odd_power : decodeRows q4Rows ^ 43 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q4p2Rows = decodeRows q4Rows ^ 2 := by
    rw [← decoded_product product_05, ← pow_two]
  have h4 : decodeRows q4p4Rows = decodeRows q4Rows ^ 4 := by
    rw [← decoded_product product_06, h2, ← pow_add]
  have h5 : decodeRows q4p5Rows = decodeRows q4Rows ^ 5 := by
    rw [← decoded_product product_07, h4, ← pow_succ]
  have h10 : decodeRows q4p10Rows = decodeRows q4Rows ^ 10 := by
    rw [← decoded_product product_08, h5, ← pow_add]
  have h20 : decodeRows q4p20Rows = decodeRows q4Rows ^ 20 := by
    rw [← decoded_product product_09, h10, ← pow_add]
  have h21 : decodeRows q4p21Rows = decodeRows q4Rows ^ 21 := by
    rw [← decoded_product product_10, h20, ← pow_succ]
  have h42 : decodeRows q4p42Rows = decodeRows q4Rows ^ 42 := by
    rw [← decoded_product product_11, h21, ← pow_add]
  have h := decoded_product product_12
  rw [h42, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_4 :
    ((outsideRepresentative hA hB 4 : Model) * (word (a hA) (b hB) "ababb" ^ 5)) ^ 43 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r4]
  rw [← decode_target]
  rw [decoded_product product_04]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
