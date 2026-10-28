module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime31Products

/-!
# Kernel-checked power products for the J4 word of order 31

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

@[expose] def matrixWord31 : BinaryMatrix := ((matrixA * matrixB * matrixA * matrixB * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))))

lemma decode_p31e1 : decodeRows t7Rows = matrixWord31 ^ 1 := by
  simpa only [pow_one, matrixWord31] using decode_t7

lemma decode_p31e2 : decodeRows p31e2Rows = matrixWord31 ^ 2 := by
  have h := congrArg decodeRows product_p31e2
  rw [decode_packedMul, decode_p31e1, ← pow_add] at h
  exact h.symm

lemma decode_p31e3 : decodeRows p31e3Rows = matrixWord31 ^ 3 := by
  have h := congrArg decodeRows product_p31e3
  rw [decode_packedMul, decode_p31e2, decode_p31e1, ← pow_add] at h
  exact h.symm

lemma decode_p31e6 : decodeRows p31e6Rows = matrixWord31 ^ 6 := by
  have h := congrArg decodeRows product_p31e6
  rw [decode_packedMul, decode_p31e3, ← pow_add] at h
  exact h.symm

lemma decode_p31e7 : decodeRows p31e7Rows = matrixWord31 ^ 7 := by
  have h := congrArg decodeRows product_p31e7
  rw [decode_packedMul, decode_p31e6, decode_p31e1, ← pow_add] at h
  exact h.symm

lemma decode_p31e14 : decodeRows p31e14Rows = matrixWord31 ^ 14 := by
  have h := congrArg decodeRows product_p31e14
  rw [decode_packedMul, decode_p31e7, ← pow_add] at h
  exact h.symm

lemma decode_p31e15 : decodeRows p31e15Rows = matrixWord31 ^ 15 := by
  have h := congrArg decodeRows product_p31e15
  rw [decode_packedMul, decode_p31e14, decode_p31e1, ← pow_add] at h
  exact h.symm

lemma decode_p31e30 : decodeRows p31e30Rows = matrixWord31 ^ 30 := by
  have h := congrArg decodeRows product_p31e30
  rw [decode_packedMul, decode_p31e15, ← pow_add] at h
  exact h.symm

lemma decode_p31e31 : 1 = matrixWord31 ^ 31 := by
  have h := congrArg decodeRows product_p31e31
  rw [decode_packedMul, decode_p31e30, decode_p31e1, ← pow_add, decode_packedOne] at h
  exact h.symm

lemma matrixWord31_representative_ne_one : matrixWord31 ^ 1 ≠ 1 := by
  rw [← decode_p31e1]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 1) h
  have h0 : decodeRows t7Rows 0 1 ≠ (1 : BinaryMatrix) 0 1 := by decide +kernel
  exact h0 e

lemma orderOf_matrixWord31_representative : orderOf (matrixWord31 ^ 1) = 31 := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  apply orderOf_eq_prime _ matrixWord31_representative_ne_one
  rw [← pow_mul]
  exact decode_p31e31.symm

end Janko4.Simplicity.WordOrderCertificates
