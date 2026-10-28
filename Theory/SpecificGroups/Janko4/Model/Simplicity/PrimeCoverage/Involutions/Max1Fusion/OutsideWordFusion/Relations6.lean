module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products6

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 6

The binary mask is 138. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part6
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (138 : ℕ).testBit j.val) = e 1 * (e 3 * (e 7)) := by
  have hv : (fun j : Fin 11 => (138 : ℕ).testBit j.val) = ![false, true, false, true, false, false, false, true, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (138 : ℕ).testBit j.val) = decodeRows m6_1Rows := by
  rw [← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r6 : toMatrix (outsideRepresentative hA hB 6 : Model) = decodeRows r6Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (138 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_02]

theorem square_6 : (outsideRepresentative hA hB 6 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r6, pow_two, decoded_product product_03, decode_packedOne]

private theorem odd_power : decodeRows q6Rows ^ 29 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q6p2Rows = decodeRows q6Rows ^ 2 := by
    rw [← decoded_product product_05, ← pow_two]
  have h3 : decodeRows q6p3Rows = decodeRows q6Rows ^ 3 := by
    rw [← decoded_product product_06, h2, ← pow_succ]
  have h6 : decodeRows q6p6Rows = decodeRows q6Rows ^ 6 := by
    rw [← decoded_product product_07, h3, ← pow_add]
  have h7 : decodeRows q6p7Rows = decodeRows q6Rows ^ 7 := by
    rw [← decoded_product product_08, h6, ← pow_succ]
  have h14 : decodeRows q6p14Rows = decodeRows q6Rows ^ 14 := by
    rw [← decoded_product product_09, h7, ← pow_add]
  have h28 : decodeRows q6p28Rows = decodeRows q6Rows ^ 28 := by
    rw [← decoded_product product_10, h14, ← pow_add]
  have h := decoded_product product_11
  rw [h28, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_6 :
    ((outsideRepresentative hA hB 6 : Model) * (word (a hA) (b hB) "bbabbbbbba" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "bbabbbbbba")⁻¹)) ^ 29 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r6]
  rw [eval_conj2Rows]
  rw [decoded_product product_04]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
