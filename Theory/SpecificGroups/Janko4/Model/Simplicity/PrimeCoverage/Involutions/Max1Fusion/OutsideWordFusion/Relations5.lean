module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products5

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 5

The binary mask is 104. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part5
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (104 : ℕ).testBit j.val) = e 3 * (e 5 * (e 6)) := by
  have hv : (fun j : Fin 11 => (104 : ℕ).testBit j.val) = ![false, false, false, true, false, true, true, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (104 : ℕ).testBit j.val) = decodeRows m5_3Rows := by
  rw [← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r5 : toMatrix (outsideRepresentative hA hB 5 : Model) = decodeRows r5Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (104 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_02]

theorem square_5 : (outsideRepresentative hA hB 5 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r5, pow_two, decoded_product product_03, decode_packedOne]

private theorem odd_power : decodeRows q5Rows ^ 11 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q5p2Rows = decodeRows q5Rows ^ 2 := by
    rw [← decoded_product product_05, ← pow_two]
  have h4 : decodeRows q5p4Rows = decodeRows q5Rows ^ 4 := by
    rw [← decoded_product product_06, h2, ← pow_add]
  have h5 : decodeRows q5p5Rows = decodeRows q5Rows ^ 5 := by
    rw [← decoded_product product_07, h4, ← pow_succ]
  have h10 : decodeRows q5p10Rows = decodeRows q5Rows ^ 10 := by
    rw [← decoded_product product_08, h5, ← pow_add]
  have h := decoded_product product_09
  rw [h10, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_5 :
    ((outsideRepresentative hA hB 5 : Model) * (word (a hA) (b hB) "bb" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "bb")⁻¹)) ^ 11 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r5]
  rw [eval_conj1Rows]
  rw [decoded_product product_04]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
