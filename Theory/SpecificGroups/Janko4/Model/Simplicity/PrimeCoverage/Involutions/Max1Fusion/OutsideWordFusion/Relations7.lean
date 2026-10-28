module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products7

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 7

The binary mask is 164. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part7
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (164 : ℕ).testBit j.val) = e 2 * (e 5 * (e 7)) := by
  have hv : (fun j : Fin 11 => (164 : ℕ).testBit j.val) = ![false, false, true, false, false, true, false, true, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (164 : ℕ).testBit j.val) = decodeRows m7_2Rows := by
  rw [← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r7 : toMatrix (outsideRepresentative hA hB 7 : Model) = decodeRows r7Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (164 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_02]

theorem square_7 : (outsideRepresentative hA hB 7 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r7, pow_two, decoded_product product_03, decode_packedOne]

private theorem odd_power : decodeRows q7Rows ^ 31 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q7p2Rows = decodeRows q7Rows ^ 2 := by
    rw [← decoded_product product_05, ← pow_two]
  have h3 : decodeRows q7p3Rows = decodeRows q7Rows ^ 3 := by
    rw [← decoded_product product_06, h2, ← pow_succ]
  have h6 : decodeRows q7p6Rows = decodeRows q7Rows ^ 6 := by
    rw [← decoded_product product_07, h3, ← pow_add]
  have h7 : decodeRows q7p7Rows = decodeRows q7Rows ^ 7 := by
    rw [← decoded_product product_08, h6, ← pow_succ]
  have h14 : decodeRows q7p14Rows = decodeRows q7Rows ^ 14 := by
    rw [← decoded_product product_09, h7, ← pow_add]
  have h15 : decodeRows q7p15Rows = decodeRows q7Rows ^ 15 := by
    rw [← decoded_product product_10, h14, ← pow_succ]
  have h30 : decodeRows q7p30Rows = decodeRows q7Rows ^ 30 := by
    rw [← decoded_product product_11, h15, ← pow_add]
  have h := decoded_product product_12
  rw [h30, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_7 :
    ((outsideRepresentative hA hB 7 : Model) * (word (a hA) (b hB) "ababb" ^ 5)) ^ 31 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r7]
  rw [← decode_target]
  rw [decoded_product product_04]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
