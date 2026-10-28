module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime23Products

/-!
# Kernel-checked power products for the J4 word of order 23

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

@[expose] def matrixWord23 : BinaryMatrix := (matrixA * ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))))))

lemma decode_p23e1 : decodeRows t4Rows = matrixWord23 ^ 1 := by
  simpa only [pow_one, matrixWord23] using decode_t4

lemma decode_p23e2 : decodeRows p23e2Rows = matrixWord23 ^ 2 := by
  have h := congrArg decodeRows product_p23e2
  rw [decode_packedMul, decode_p23e1, ← pow_add] at h
  exact h.symm

lemma decode_p23e4 : decodeRows p23e4Rows = matrixWord23 ^ 4 := by
  have h := congrArg decodeRows product_p23e4
  rw [decode_packedMul, decode_p23e2, ← pow_add] at h
  exact h.symm

lemma decode_p23e5 : decodeRows p23e5Rows = matrixWord23 ^ 5 := by
  have h := congrArg decodeRows product_p23e5
  rw [decode_packedMul, decode_p23e4, decode_p23e1, ← pow_add] at h
  exact h.symm

lemma decode_p23e10 : decodeRows p23e10Rows = matrixWord23 ^ 10 := by
  have h := congrArg decodeRows product_p23e10
  rw [decode_packedMul, decode_p23e5, ← pow_add] at h
  exact h.symm

lemma decode_p23e11 : decodeRows p23e11Rows = matrixWord23 ^ 11 := by
  have h := congrArg decodeRows product_p23e11
  rw [decode_packedMul, decode_p23e10, decode_p23e1, ← pow_add] at h
  exact h.symm

lemma decode_p23e22 : decodeRows p23e22Rows = matrixWord23 ^ 22 := by
  have h := congrArg decodeRows product_p23e22
  rw [decode_packedMul, decode_p23e11, ← pow_add] at h
  exact h.symm

lemma decode_p23e23 : 1 = matrixWord23 ^ 23 := by
  have h := congrArg decodeRows product_p23e23
  rw [decode_packedMul, decode_p23e22, decode_p23e1, ← pow_add, decode_packedOne] at h
  exact h.symm

lemma matrixWord23_representative_ne_one : matrixWord23 ^ 1 ≠ 1 := by
  rw [← decode_p23e1]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : decodeRows t4Rows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e

lemma orderOf_matrixWord23_representative : orderOf (matrixWord23 ^ 1) = 23 := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  apply orderOf_eq_prime _ matrixWord23_representative_ne_one
  rw [← pow_mul]
  exact decode_p23e23.symm

end Janko4.Simplicity.WordOrderCertificates
