module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime43Products

/-!
# Kernel-checked power products for the J4 word of order 43

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

@[expose] def matrixWord43 : BinaryMatrix := ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))))

lemma decode_p43e1 : decodeRows t3Rows = matrixWord43 ^ 1 := by
  simpa only [pow_one, matrixWord43] using decode_t3

lemma decode_p43e2 : decodeRows p43e2Rows = matrixWord43 ^ 2 := by
  have h := congrArg decodeRows product_p43e2
  rw [decode_packedMul, decode_p43e1, ← pow_add] at h
  exact h.symm

lemma decode_p43e4 : decodeRows p43e4Rows = matrixWord43 ^ 4 := by
  have h := congrArg decodeRows product_p43e4
  rw [decode_packedMul, decode_p43e2, ← pow_add] at h
  exact h.symm

lemma decode_p43e5 : decodeRows p43e5Rows = matrixWord43 ^ 5 := by
  have h := congrArg decodeRows product_p43e5
  rw [decode_packedMul, decode_p43e4, decode_p43e1, ← pow_add] at h
  exact h.symm

lemma decode_p43e10 : decodeRows p43e10Rows = matrixWord43 ^ 10 := by
  have h := congrArg decodeRows product_p43e10
  rw [decode_packedMul, decode_p43e5, ← pow_add] at h
  exact h.symm

lemma decode_p43e20 : decodeRows p43e20Rows = matrixWord43 ^ 20 := by
  have h := congrArg decodeRows product_p43e20
  rw [decode_packedMul, decode_p43e10, ← pow_add] at h
  exact h.symm

lemma decode_p43e21 : decodeRows p43e21Rows = matrixWord43 ^ 21 := by
  have h := congrArg decodeRows product_p43e21
  rw [decode_packedMul, decode_p43e20, decode_p43e1, ← pow_add] at h
  exact h.symm

lemma decode_p43e42 : decodeRows p43e42Rows = matrixWord43 ^ 42 := by
  have h := congrArg decodeRows product_p43e42
  rw [decode_packedMul, decode_p43e21, ← pow_add] at h
  exact h.symm

lemma decode_p43e43 : 1 = matrixWord43 ^ 43 := by
  have h := congrArg decodeRows product_p43e43
  rw [decode_packedMul, decode_p43e42, decode_p43e1, ← pow_add, decode_packedOne] at h
  exact h.symm

lemma matrixWord43_representative_ne_one : matrixWord43 ^ 1 ≠ 1 := by
  rw [← decode_p43e1]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : decodeRows t3Rows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e

lemma orderOf_matrixWord43_representative : orderOf (matrixWord43 ^ 1) = 43 := by
  let : Fact (Nat.Prime 43) := ⟨by decide⟩
  apply orderOf_eq_prime _ matrixWord43_representative_ne_one
  rw [← pow_mul]
  exact decode_p43e43.symm

end Janko4.Simplicity.WordOrderCertificates
