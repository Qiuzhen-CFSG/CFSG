module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products9

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 9

The binary mask is 254. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part9
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (254 : ℕ).testBit j.val) = e 1 * (e 2 * (e 3 * (e 4 * (e 5 * (e 6 * (e 7)))))) := by
  have hv : (fun j : Fin 11 => (254 : ℕ).testBit j.val) = ![false, true, true, true, true, true, true, true, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (254 : ℕ).testBit j.val) = decodeRows m9_1Rows := by
  rw [← decoded_product product_05, ← decoded_product product_04, ← decoded_product product_03, ← decoded_product product_02, ← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r9 : toMatrix (outsideRepresentative hA hB 9 : Model) = decodeRows r9Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (254 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_06]

theorem square_9 : (outsideRepresentative hA hB 9 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r9, pow_two, decoded_product product_07, decode_packedOne]

private theorem odd_power : decodeRows q9Rows ^ 11 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q9p2Rows = decodeRows q9Rows ^ 2 := by
    rw [← decoded_product product_09, ← pow_two]
  have h4 : decodeRows q9p4Rows = decodeRows q9Rows ^ 4 := by
    rw [← decoded_product product_10, h2, ← pow_add]
  have h5 : decodeRows q9p5Rows = decodeRows q9Rows ^ 5 := by
    rw [← decoded_product product_11, h4, ← pow_succ]
  have h10 : decodeRows q9p10Rows = decodeRows q9Rows ^ 10 := by
    rw [← decoded_product product_12, h5, ← pow_add]
  have h := decoded_product product_13
  rw [h10, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_9 :
    ((outsideRepresentative hA hB 9 : Model) * (word (a hA) (b hB) "b" * (a hA) * (word (a hA) (b hB) "b")⁻¹)) ^ 11 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r9]
  rw [eval_conj3Rows]
  rw [decoded_product product_08]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
