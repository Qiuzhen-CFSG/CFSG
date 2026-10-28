module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products1

import Mathlib.Tactic.FinCases

/-!
# Certified square and odd-product relations for outside word 1

The binary mask is 16. Evaluation uses the production kernel basis.
Packed multiplication proves the square-one and odd-power identities, and
faithfulness transfers them to the concrete subgroup and `Model`.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part1
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

private theorem expand_mask {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (16 : ℕ).testBit j.val) = e 4 := by
  have hv : (fun j : Fin 11 => (16 : ℕ).testBit j.val) = ![false, false, false, false, true, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [hv]
  simp [binaryProduct, List.ofFn_succ]

private theorem eval_mask :
    matrixProduct (fun j => (16 : ℕ).testBit j.val) = decodeRows e4Rows := by
  exact expand_mask (fun j => decodeRows (basisRows j))

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY basis outsideRepresentative

theorem eval_r1 : toMatrix (outsideRepresentative hA hB 1 : Model) = decodeRows r1Rows := by
  unfold outsideRepresentative
  change representation hA hB ((localX hA hB) *
    binaryProduct (basis hA hB) (fun j => (16 : ℕ).testBit j.val)) = _
  rw [map_mul, representation_x,
    representation_binaryProduct hA hB (representation_basis hA hB),
    eval_mask, decoded_product product_00]

theorem square_1 : (outsideRepresentative hA hB 1 : Model) ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_r1, pow_two, decoded_product product_01, decode_packedOne]

private theorem odd_power : decodeRows q1Rows ^ 43 = (1 : BinaryMatrix) := by
  have h2 : decodeRows q1p2Rows = decodeRows q1Rows ^ 2 := by
    rw [← decoded_product product_03, ← pow_two]
  have h4 : decodeRows q1p4Rows = decodeRows q1Rows ^ 4 := by
    rw [← decoded_product product_04, h2, ← pow_add]
  have h5 : decodeRows q1p5Rows = decodeRows q1Rows ^ 5 := by
    rw [← decoded_product product_05, h4, ← pow_succ]
  have h10 : decodeRows q1p10Rows = decodeRows q1Rows ^ 10 := by
    rw [← decoded_product product_06, h5, ← pow_add]
  have h20 : decodeRows q1p20Rows = decodeRows q1Rows ^ 20 := by
    rw [← decoded_product product_07, h10, ← pow_add]
  have h21 : decodeRows q1p21Rows = decodeRows q1Rows ^ 21 := by
    rw [← decoded_product product_08, h20, ← pow_succ]
  have h42 : decodeRows q1p42Rows = decodeRows q1Rows ^ 42 := by
    rw [← decoded_product product_09, h21, ← pow_add]
  have h := decoded_product product_10
  rw [h42, ← pow_succ, decode_packedOne] at h
  exact h

theorem odd_product_1 :
    ((outsideRepresentative hA hB 1 : Model) * (word (a hA) (b hB) "b" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "b")⁻¹)) ^ 43 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, eval_r1]
  rw [eval_conj0Rows]
  rw [decoded_product product_02]
  exact odd_power

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
