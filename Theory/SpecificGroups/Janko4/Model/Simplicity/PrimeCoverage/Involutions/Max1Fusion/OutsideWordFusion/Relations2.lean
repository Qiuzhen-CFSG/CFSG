module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products2

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 2

The binary mask is 28. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part2
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (28 : ℕ).testBit j.val) = e 2 * (e 3 * (e 4)) := by
  have hv : (fun j : Fin 11 => (28 : ℕ).testBit j.val) = ![false, false, true, true, true, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (28 : ℕ).testBit j.val) = decodeRows m2_2Rows := by
  rw [← decoded_product product_01, ← decoded_product product_00]
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r2 : toMatrix (outsideRepresentative hA hB 2 : Model) = decodeRows r2Rows := by
  unfold outsideRepresentative
  change representation hA hB (((localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (28 : ℕ).testBit j.val)) = _
  rw [map_mul, ← decode_xy7,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_02]

theorem square_2 : (outsideRepresentative hA hB 2 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r2, pow_two, decoded_product product_03, decode_packedOne]

private theorem odd_power : decodeRows q2Rows ^ 15 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q2p2Rows = decodeRows q2Rows ^ 2 := by
    rw [← decoded_product product_05, ← pow_two]
  have h3 : decodeRows q2p3Rows = decodeRows q2Rows ^ 3 := by
    rw [← decoded_product product_06, h2, ← pow_succ]
  have h6 : decodeRows q2p6Rows = decodeRows q2Rows ^ 6 := by
    rw [← decoded_product product_07, h3, ← pow_add]
  have h7 : decodeRows q2p7Rows = decodeRows q2Rows ^ 7 := by
    rw [← decoded_product product_08, h6, ← pow_succ]
  have h14 : decodeRows q2p14Rows = decodeRows q2Rows ^ 14 := by
    rw [← decoded_product product_09, h7, ← pow_add]
  have h := decoded_product product_10
  rw [h14, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_2 :
    ((outsideRepresentative hA hB 2 : Model) * (word (a hA) (b hB) "bb" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "bb")⁻¹)) ^ 15 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r2]
  rw [eval_conj1Rows]
  rw [decoded_product product_04]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
